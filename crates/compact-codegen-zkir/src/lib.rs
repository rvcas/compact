use std::fmt::Write as _;
use std::sync::Arc;

use compact_circuit::{CircuitInstr, ProofCircuit};
use midnight_base_crypto::data_provider::{FetchMode, MidnightDataProvider, OutputMode};
use midnight_serialize::tagged_serialize;
use midnight_transient_crypto::curve::Fr;
use midnight_transient_crypto::proofs::Zkir;
use midnight_zkir::ir::{Instruction, IrMinorVersion, IrSource, Operand};
use sha2::{Digest, Sha256};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ZkirError {
    #[error("failed to serialize bzkir for circuit `{circuit}`: {message}")]
    SerializeBzkir { circuit: String, message: String },
    #[error("failed to initialize Midnight data provider: {0}")]
    DataProvider(String),
    #[error("failed to initialize async runtime for ZKIR keygen: {0}")]
    Runtime(#[source] std::io::Error),
    #[error("ZKIR keygen failed: {0}")]
    Keygen(String),
    #[error("failed to serialize prover key: {0}")]
    SerializeProverKey(String),
    #[error("failed to serialize verifier key: {0}")]
    SerializeVerifierKey(String),
}

#[derive(Debug, Clone)]
pub struct GeneratedZkir {
    pub name: String,
    pub ir: IrSource,
    /// Pretty-formatted `.zkir` v3.1 JSON (matching upstream `print-zkir-v3.ss`).
    pub json: String,
    /// Tagged binary `.bzkir` encoding produced by `midnight-serialize`.
    pub bzkir: Vec<u8>,
}

#[derive(Debug, Clone)]
pub struct CompiledKeys {
    pub prover_key: Vec<u8>,
    pub verifier_key: Vec<u8>,
    pub verifier_key_sha256: String,
    pub k: u8,
    pub rows: usize,
}

#[derive(Debug, Clone, Copy)]
pub struct CircuitModelSummary {
    pub k: u8,
    pub rows: usize,
}

/// Lower a flattened proof circuit into Midnight's native [`IrSource`], canonical
/// `.zkir` JSON, and tagged `.bzkir` bytes.
pub fn generate_zkir(circuit: &ProofCircuit) -> Result<GeneratedZkir, ZkirError> {
    let mut instructions = Vec::with_capacity(circuit.instructions.len());
    for instr in &circuit.instructions {
        match instr {
            CircuitInstr::Impact { guard, op } => {
                let guard_op = Operand::Immediate(Fr::from(u64::from(*guard)));
                let inputs = op
                    .assemble()
                    .into_iter()
                    .map(|word| Operand::Immediate(Fr::from(word)))
                    .collect();
                instructions.push(Instruction::Impact {
                    guard: guard_op,
                    inputs,
                });
            }
        }
    }

    let ir = IrSource {
        version: IrMinorVersion::V1,
        inputs: Vec::new(),
        outputs: Vec::new(),
        do_communications_commitment: true,
        instructions: Arc::new(instructions),
    };

    let json = format_zkir_json(&ir);
    let mut bzkir = Vec::new();
    tagged_serialize(&ir, &mut bzkir).map_err(|e| ZkirError::SerializeBzkir {
        circuit: circuit.name.clone(),
        message: e.to_string(),
    })?;

    Ok(GeneratedZkir {
        name: circuit.name.clone(),
        ir,
        json,
        bzkir,
    })
}

/// Run Midnight's Halo2 circuit cost model offline to verify circuit synthesis and compute `(k, rows)`.
pub fn analyze_model(ir: &IrSource) -> CircuitModelSummary {
    let model = ir.model();
    CircuitModelSummary {
        k: model.k(),
        rows: model.rows(),
    }
}

/// Compile proving and verifier keys in-process using `midnight-zkir` (no external `zkir-v3` binary).
pub fn compile_keys(ir: &IrSource) -> Result<CompiledKeys, ZkirError> {
    let model = analyze_model(ir);
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .map_err(ZkirError::Runtime)?;

    let (pk, vk) = rt.block_on(async {
        let provider = MidnightDataProvider::new(FetchMode::OnDemand, OutputMode::Log, vec![])
            .map_err(|e| ZkirError::DataProvider(e.to_string()))?;
        ir.keygen(&provider)
            .await
            .map_err(|e| ZkirError::Keygen(e.to_string()))
    })?;

    let mut prover_key = Vec::new();
    tagged_serialize(&pk, &mut prover_key)
        .map_err(|e| ZkirError::SerializeProverKey(e.to_string()))?;

    let mut verifier_key = Vec::new();
    tagged_serialize(&vk, &mut verifier_key)
        .map_err(|e| ZkirError::SerializeVerifierKey(e.to_string()))?;

    let verifier_key_sha256 = hex::encode(Sha256::digest(&verifier_key));

    Ok(CompiledKeys {
        prover_key,
        verifier_key,
        verifier_key_sha256,
        k: model.k,
        rows: model.rows,
    })
}

/// Format an [`IrSource`] into canonical upstream `.zkir` v3.1 JSON.
fn format_zkir_json(ir: &IrSource) -> String {
    let minor = match ir.version {
        IrMinorVersion::V0 => 0,
        IrMinorVersion::V1 => 1,
        _ => 2,
    };

    let mut out = String::new();
    writeln!(out, "{{").unwrap();
    writeln!(out, "  \"version\": {{ \"major\": 3, \"minor\": {minor} }},").unwrap();
    writeln!(
        out,
        "  \"do_communications_commitment\": {},",
        ir.do_communications_commitment
    )
    .unwrap();
    writeln!(out, "  \"inputs\": [").unwrap();
    writeln!(out, "  ],").unwrap();
    writeln!(out, "  \"outputs\": [").unwrap();
    writeln!(out, "  ],").unwrap();
    writeln!(out, "  \"instructions\": [").unwrap();

    for (idx, instr) in ir.instructions.iter().enumerate() {
        let comma = if idx + 1 < ir.instructions.len() {
            ","
        } else {
            ""
        };
        match instr {
            Instruction::Impact { guard, inputs } => {
                let guard_json = serde_json::to_string(guard).unwrap();
                let inputs_json: Vec<_> = inputs
                    .iter()
                    .map(|op| serde_json::to_string(op).unwrap())
                    .collect();
                writeln!(
                    out,
                    "    {{ \"op\": \"impact\", \"guard\": {guard_json}, \"inputs\": [{}] }}{comma}",
                    inputs_json.join(", ")
                )
                .unwrap();
            }
            other => {
                let serialized = serde_json::to_string(other).unwrap();
                writeln!(out, "    {serialized}{comma}").unwrap();
            }
        }
    }

    writeln!(out, "  ]").unwrap();
    writeln!(out, "}}").unwrap();
    out
}

#[cfg(test)]
mod tests {
    use compact_circuit::lower_to_circuits;
    use compact_hir::lower;
    use compact_parser::parse;
    use compact_span::SourceMap;
    use compact_test_utils::assert_compact_snapshot;
    use midnight_zkir::IrSource;

    use super::{analyze_model, generate_zkir};

    fn compile_to_zkir(src: &str) -> String {
        let mut sm = SourceMap::new();
        let id = sm.add_file("counter.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let lowered = lower(file, &parsed.ast);
        assert!(!lowered.diagnostics.has_errors());
        let circuits = lower_to_circuits(&lowered.program);
        assert_eq!(circuits.circuits.len(), 1);
        let generated = generate_zkir(&circuits.circuits[0]).unwrap();

        // Round-trip verify with midnight-zkir's own JSON loader!
        let reloaded = IrSource::load(generated.json.as_bytes()).unwrap();
        assert_eq!(reloaded, generated.ir);

        // Validate offline Halo2 circuit synthesis model!
        let model = analyze_model(&generated.ir);
        assert!(model.k > 0);
        assert!(model.rows > 0);

        generated.json
    }

    #[test]
    fn zkir_counter_increment() {
        assert_compact_snapshot!(
            r#"
            import CompactStandardLibrary;

            export ledger round: Counter;

            export circuit increment(): [] {
              round.increment(1);
            }
            "#,
            compile_to_zkir
        );
    }
}
