use std::fmt::Write as _;

use compact_circuit::{AlignmentAtom, CircuitInstr, CircuitVal, CircuitVar, ProofCircuit};
use midnight_base_crypto::data_provider::{FetchMode, MidnightDataProvider, OutputMode};
use midnight_serialize::tagged_serialize;
use midnight_transient_crypto::proofs::Zkir;
use midnight_zkir::IrSource;
use sha2::{Digest, Sha256};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ZkirError {
    #[error("failed to load generated ZKIR for circuit `{circuit}`: {message}")]
    LoadIr { circuit: String, message: String },
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

/// Lower a flattened proof circuit into canonical `.zkir` v3.1 JSON, validate and
/// hydrate Midnight's native [`IrSource`], and produce tagged `.bzkir` bytes.
pub fn generate_zkir(circuit: &ProofCircuit) -> Result<GeneratedZkir, ZkirError> {
    let json = format_circuit_zkir(circuit);
    let ir = IrSource::load(json.as_bytes()).map_err(|e| ZkirError::LoadIr {
        circuit: circuit.name.clone(),
        message: e.to_string(),
    })?;

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

fn var_name(circuit: &ProofCircuit, var: CircuitVar) -> String {
    let hint = &circuit.var_names[var.id as usize];
    format!("%{hint}.{}", var.id)
}

/// Format a signed integer immediate into ZKIR v3 little-endian hex (`"0x00"`, `"-0x02"`, ...).
fn format_imm(val: i128) -> String {
    let mut s = String::new();
    let mut n = if val < 0 {
        s.push_str("-0x");
        val.unsigned_abs()
    } else {
        s.push_str("0x");
        val as u128
    };
    loop {
        let byte = (n & 0xff) as u8;
        write!(s, "{byte:02x}").unwrap();
        n >>= 8;
        if n == 0 {
            break;
        }
    }
    s
}

fn format_val(circuit: &ProofCircuit, val: &CircuitVal) -> String {
    match val {
        CircuitVal::Var(v) => format!("\"{}\"", var_name(circuit, *v)),
        CircuitVal::Imm(n) => format!("\"{}\"", format_imm(*n)),
        CircuitVal::ImmBytes(bytes) => format!("\"0x{}\"", hex::encode(bytes)),
    }
}

fn format_alignment(alignment: &[AlignmentAtom]) -> String {
    let items: Vec<String> = alignment
        .iter()
        .map(|atom| match atom {
            AlignmentAtom::Bytes(len) => {
                format!("{{ \"tag\": \"atom\", \"value\": {{ \"length\": {len}, \"tag\": \"bytes\" }} }}")
            }
            AlignmentAtom::Field => {
                "{ \"tag\": \"atom\", \"value\": { \"tag\": \"field\" } }".to_owned()
            }
        })
        .collect();
    format!("[{}]", items.join(", "))
}

/// Format a [`ProofCircuit`] into canonical upstream `.zkir` v3.1 JSON.
fn format_circuit_zkir(circuit: &ProofCircuit) -> String {
    let mut out = String::new();
    writeln!(out, "{{").unwrap();
    writeln!(out, "  \"version\": {{ \"major\": 3, \"minor\": 1 }},").unwrap();
    writeln!(out, "  \"do_communications_commitment\": true,").unwrap();

    writeln!(out, "  \"inputs\": [").unwrap();
    for (idx, &inp) in circuit.inputs.iter().enumerate() {
        let comma = if idx + 1 < circuit.inputs.len() { "," } else { "" };
        writeln!(
            out,
            "    {{ \"name\": \"{}\", \"type\": \"Scalar<BLS12-381>\" }}{comma}",
            var_name(circuit, inp)
        )
        .unwrap();
    }
    writeln!(out, "  ],").unwrap();

    writeln!(out, "  \"outputs\": [").unwrap();
    for idx in 0..circuit.output_count {
        let comma = if idx + 1 < circuit.output_count { "," } else { "" };
        writeln!(out, "    \"Scalar<BLS12-381>\"{comma}").unwrap();
    }
    writeln!(out, "  ],").unwrap();

    writeln!(out, "  \"instructions\": [").unwrap();
    for (idx, instr) in circuit.instructions.iter().enumerate() {
        let comma = if idx + 1 < circuit.instructions.len() {
            ","
        } else {
            ""
        };
        match instr {
            CircuitInstr::PublicInput { guard, output } => {
                let guard_str = match guard {
                    Some(g) => format_val(circuit, g),
                    None => "null".to_owned(),
                };
                writeln!(
                    out,
                    "    {{ \"op\": \"public_input\", \"type\": \"Scalar<BLS12-381>\", \"output\": \"{}\", \"guard\": {guard_str} }}{comma}",
                    var_name(circuit, *output)
                )
                .unwrap();
            }
            CircuitInstr::PrivateInput { guard, output } => {
                let guard_str = match guard {
                    Some(g) => format_val(circuit, g),
                    None => "null".to_owned(),
                };
                writeln!(
                    out,
                    "    {{ \"op\": \"private_input\", \"type\": \"Scalar<BLS12-381>\", \"output\": \"{}\", \"guard\": {guard_str} }}{comma}",
                    var_name(circuit, *output)
                )
                .unwrap();
            }
            CircuitInstr::ConstrainBits { val, bits } => {
                writeln!(
                    out,
                    "    {{ \"op\": \"constrain_bits\", \"val\": {}, \"bits\": {bits} }}{comma}",
                    format_val(circuit, val)
                )
                .unwrap();
            }
            CircuitInstr::Impact { guard, op } => {
                let guard_str = format_val(circuit, guard);
                let inputs: Vec<_> = op
                    .assemble()
                    .iter()
                    .map(|v| format_val(circuit, v))
                    .collect();
                writeln!(
                    out,
                    "    {{ \"op\": \"impact\", \"guard\": {guard_str}, \"inputs\": [{}] }}{comma}",
                    inputs.join(", ")
                )
                .unwrap();
            }
            CircuitInstr::PersistentHash {
                alignment,
                inputs,
                output,
            } => {
                let rendered_inputs: Vec<_> =
                    inputs.iter().map(|v| format_val(circuit, v)).collect();
                writeln!(
                    out,
                    "    {{ \"op\": \"persistent_hash\", \"output\": \"{}\", \"alignment\": {}, \"inputs\": [{}] }}{comma}",
                    var_name(circuit, *output),
                    format_alignment(alignment),
                    rendered_inputs.join(", ")
                )
                .unwrap();
            }
            CircuitInstr::BytesIntoNatives { bytes, outputs } => {
                let rendered_outputs: Vec<_> = outputs
                    .iter()
                    .map(|v| format!("\"{}\"", var_name(circuit, *v)))
                    .collect();
                writeln!(
                    out,
                    "    {{ \"op\": \"bytes_into_natives\", \"outputs\": [{}], \"bytes\": \"{}\" }}{comma}",
                    rendered_outputs.join(", "),
                    var_name(circuit, *bytes)
                )
                .unwrap();
            }
            CircuitInstr::TestEq { a, b, output } => {
                writeln!(
                    out,
                    "    {{ \"op\": \"test_eq\", \"output\": \"{}\", \"a\": {}, \"b\": {} }}{comma}",
                    var_name(circuit, *output),
                    format_val(circuit, a),
                    format_val(circuit, b)
                )
                .unwrap();
            }
            CircuitInstr::Not { a, output } => {
                writeln!(
                    out,
                    "    {{ \"op\": \"not\", \"output\": \"{}\", \"a\": {} }}{comma}",
                    var_name(circuit, *output),
                    format_val(circuit, a)
                )
                .unwrap();
            }
            CircuitInstr::Add { a, b, output } => {
                writeln!(
                    out,
                    "    {{ \"op\": \"add\", \"output\": \"{}\", \"a\": {}, \"b\": {} }}{comma}",
                    var_name(circuit, *output),
                    format_val(circuit, a),
                    format_val(circuit, b)
                )
                .unwrap();
            }
            CircuitInstr::Neg { a, output } => {
                writeln!(
                    out,
                    "    {{ \"op\": \"neg\", \"output\": \"{}\", \"a\": {} }}{comma}",
                    var_name(circuit, *output),
                    format_val(circuit, a)
                )
                .unwrap();
            }
            CircuitInstr::CondSelect { bit, a, b, output } => {
                writeln!(
                    out,
                    "    {{ \"op\": \"cond_select\", \"output\": \"{}\", \"bit\": {}, \"a\": {}, \"b\": {} }}{comma}",
                    var_name(circuit, *output),
                    format_val(circuit, bit),
                    format_val(circuit, a),
                    format_val(circuit, b)
                )
                .unwrap();
            }
            CircuitInstr::Assert { cond } => {
                writeln!(
                    out,
                    "    {{ \"op\": \"assert\", \"cond\": {} }}{comma}",
                    format_val(circuit, cond)
                )
                .unwrap();
            }
            CircuitInstr::Output { vals } => {
                let rendered: Vec<_> = vals.iter().map(|v| format_val(circuit, v)).collect();
                writeln!(
                    out,
                    "    {{ \"op\": \"output\", \"vals\": [{}] }}{comma}",
                    rendered.join(", ")
                )
                .unwrap();
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
    use compact_parser::parse;
    use compact_sema::check;
    use compact_span::SourceMap;
    use compact_test_utils::assert_compact_snapshot;

    use super::{analyze_model, generate_zkir};

    fn compile_all_zkir(src: &str) -> String {
        let mut sm = SourceMap::new();
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(
            !parsed.diagnostics.has_errors(),
            "unexpected parse errors: {:?}",
            parsed.diagnostics
        );
        let checked = check(file, &parsed.ast);
        assert!(
            !checked.diagnostics.has_errors(),
            "unexpected sema errors: {:?}",
            checked.diagnostics
        );
        let circuits = lower_to_circuits(&checked.program);
        let mut out = String::new();
        for (i, c) in circuits.circuits.iter().enumerate() {
            let generated = generate_zkir(c).unwrap();
            // Validate offline Halo2 circuit synthesis model via midnight-zkir!
            let model = analyze_model(&generated.ir);
            assert!(model.k > 0);
            assert!(model.rows > 0);
            if circuits.circuits.len() > 1 {
                if i > 0 {
                    out.push('\n');
                }
                out.push_str(&format!("=== {}.zkir ===\n", c.name));
            }
            out.push_str(&generated.json);
        }
        out
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
            compile_all_zkir
        );
    }

    #[test]
    fn zkir_cell_enum_helper_and_ternary() {
        assert_compact_snapshot!(
            r#"
            import CompactStandardLibrary;

            enum STATE { unset, set }

            export ledger value: Field;
            ledger state: STATE;

            circuit in_state(s: STATE): Boolean {
              return state == s;
            }

            export circuit set(v: Field): [] {
              assert(in_state(STATE.unset), "already set");
              value = disclose(v);
              state = STATE.set;
            }

            export circuit get(): Field {
              return in_state(STATE.set) ? value : 0 as Field;
            }
            "#,
            compile_all_zkir
        );
    }

    #[test]
    fn zkir_tiny_contract() {
        assert_compact_snapshot!(
            r#"
            export {Maybe}
            export {set, get, clear, public_key}

            import CompactStandardLibrary;

            enum STATE { unset, set }

            ledger authority: Bytes<32>;
            export ledger value: Field;
            ledger state: STATE;
            constructor(v: Field) {
              const sk = private$secret_key();
              authority = public_key(sk);
              value = disclose(v);
              state = STATE.set;
            }

            witness private$secret_key(): Bytes<32>;

            circuit in_state(s: STATE): Boolean {
              return state == s;
            }

            circuit set(v: Field): [] {
              assert(in_state(STATE.unset), "set: attempted to overwrite recorded value");
              const sk = private$secret_key();
              const apk = public_key(sk);
              authority = apk;
              value = disclose(v);
              state = STATE.set;
            }

            circuit get(): Maybe<Field> {
              return in_state(STATE.set) ? some<Field>(value) : none<Field>();
            }

            circuit clear(): [] {
              assert(in_state(STATE.set), "clear: no value is currently recorded");
              const sk = private$secret_key();
              const apk = public_key(sk);
              assert(apk == authority, "clear: attempted clear without proper authorization");
              authority = default<Bytes<32>>;
              value = default<Field>;
              state = STATE.unset;
            }

            circuit public_key(sk: Bytes<32>): Bytes<32> {
              return disclose(persistentHash<Vector<2, Bytes<32>>>([pad(32, "lares:tiny:pk:"), sk]));
            }
            "#,
            compile_all_zkir
        );
    }
}
