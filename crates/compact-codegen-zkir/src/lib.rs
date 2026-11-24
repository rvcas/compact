use std::fmt::Write as _;

use compact_circuit::{
    AlignmentAtom, CircuitInstr, CircuitVal, CircuitVar, ProofCircuit, WireType,
};
use midnight_base_crypto::data_provider::{FetchMode, MidnightDataProvider, OutputMode};
use midnight_base_crypto::fab::{Alignment, AlignmentAtom as FabAlignmentAtom, AlignmentSegment};
use midnight_serialize::tagged_serialize;
use midnight_transient_crypto::curve::Fr;
use midnight_transient_crypto::proofs::Zkir;
use midnight_zkir::ir::Operand;
use midnight_zkir::ir_types::IrType;
use midnight_zkir::{Identifier, Instruction, IrSource};
use serde::Serialize;
use sha2::{Digest, Sha256};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ZkirError {
    #[error("invalid field immediate `{value}` in circuit `{circuit}`")]
    InvalidImmediate { circuit: String, value: String },
    #[error("failed to serialize ZKIR JSON for circuit `{circuit}`: {message}")]
    SerializeJson { circuit: String, message: String },
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
    /// Pretty-formatted `.zkir` v3.1 JSON (one instruction per line).
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

/// Lower a flattened proof circuit into typed `midnight-zkir` instructions, serialize
/// canonical `.zkir` v3.1 JSON, hydrate [`IrSource`], and produce tagged `.bzkir` bytes.
pub fn generate_zkir(circuit: &ProofCircuit) -> Result<GeneratedZkir, ZkirError> {
    let inputs: Vec<ZkirInput> = circuit
        .inputs
        .iter()
        .map(|&(v, wt)| ZkirInput {
            name: ident(circuit, v),
            val_t: to_ir_type(wt),
        })
        .collect();
    let outputs: Vec<IrType> = circuit
        .output_types
        .iter()
        .map(|&wt| to_ir_type(wt))
        .collect();
    let instructions = lower_instructions(circuit)?;

    let json = render_zkir_json(&inputs, &outputs, &instructions).map_err(|e| {
        ZkirError::SerializeJson {
            circuit: circuit.name.clone(),
            message: e.to_string(),
        }
    })?;
    let ir = IrSource::load(json.as_bytes()).map_err(|e| ZkirError::LoadIr {
        circuit: circuit.name.clone(),
        message: e.to_string(),
    })?;
    debug_assert_eq!(ir.outputs, outputs);
    debug_assert_eq!(ir.instructions.as_slice(), instructions.as_slice());

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
    compile_keys_with_model(ir, analyze_model(ir))
}

/// Compile proving and verifier keys using a precomputed [`CircuitModelSummary`] to avoid
/// running Halo2 model synthesis twice.
pub fn compile_keys_with_model(
    ir: &IrSource,
    model: CircuitModelSummary,
) -> Result<CompiledKeys, ZkirError> {
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

#[derive(Serialize)]
struct ZkirVersion {
    major: u8,
    minor: u8,
}

#[derive(Serialize)]
struct ZkirInput {
    name: Identifier,
    #[serde(rename = "type")]
    val_t: IrType,
}

fn ident(circuit: &ProofCircuit, var: CircuitVar) -> Identifier {
    let hint = &circuit.var_names[var.id as usize];
    Identifier(format!("%{hint}.{}", var.id))
}

fn imm_to_fr(circuit: &ProofCircuit, val: i128) -> Result<Fr, ZkirError> {
    let bytes = val.unsigned_abs().to_le_bytes();
    let f = Fr::from_le_bytes(&bytes).ok_or_else(|| ZkirError::InvalidImmediate {
        circuit: circuit.name.clone(),
        value: val.to_string(),
    })?;
    Ok(if val < 0 { -f } else { f })
}

fn operand(circuit: &ProofCircuit, val: &CircuitVal) -> Result<Operand, ZkirError> {
    match val {
        CircuitVal::Var(v) => Ok(Operand::Variable(ident(circuit, *v))),
        CircuitVal::Imm(n) => Ok(Operand::Immediate(imm_to_fr(circuit, *n)?)),
        CircuitVal::ImmBytes(bytes) => {
            let f = Fr::from_le_bytes(bytes).ok_or_else(|| ZkirError::InvalidImmediate {
                circuit: circuit.name.clone(),
                value: format!("0x{}", hex::encode(bytes)),
            })?;
            Ok(Operand::Immediate(f))
        }
    }
}

fn operands(circuit: &ProofCircuit, vals: &[CircuitVal]) -> Result<Vec<Operand>, ZkirError> {
    vals.iter().map(|v| operand(circuit, v)).collect()
}

fn to_alignment(alignment: &[AlignmentAtom]) -> Alignment {
    Alignment(
        alignment
            .iter()
            .map(|atom| {
                AlignmentSegment::Atom(match atom {
                    AlignmentAtom::Bytes(length) => FabAlignmentAtom::Bytes { length: *length },
                    AlignmentAtom::Field => FabAlignmentAtom::Field,
                    AlignmentAtom::Compress => FabAlignmentAtom::Compress,
                })
            })
            .collect(),
    )
}

fn to_ir_type(wt: WireType) -> IrType {
    match wt {
        WireType::Native => IrType::Native,
        WireType::JubjubPoint => IrType::JubjubPoint,
        WireType::JubjubScalar => IrType::JubjubScalar,
        WireType::Secp256k1Point => IrType::Secp256k1Point,
        WireType::Secp256k1Base => IrType::Secp256k1Base,
        WireType::Secp256k1Scalar => IrType::Secp256k1Scalar,
        WireType::Secp256r1Point => IrType::Secp256r1Point,
        WireType::Secp256r1Base => IrType::Secp256r1Base,
        WireType::Secp256r1Scalar => IrType::Secp256r1Scalar,
        WireType::Curve25519Point => IrType::Curve25519Point,
        WireType::Curve25519Base => IrType::Curve25519Base,
        WireType::Curve25519Scalar => IrType::Curve25519Scalar,
    }
}

fn lower_instructions(circuit: &ProofCircuit) -> Result<Vec<Instruction>, ZkirError> {
    let mut out = Vec::with_capacity(circuit.instructions.len());
    for instr in &circuit.instructions {
        let zkir_instr = match instr {
            CircuitInstr::PublicInput {
                guard,
                val_t,
                output,
            } => Instruction::PublicInput {
                guard: guard.as_ref().map(|g| operand(circuit, g)).transpose()?,
                val_t: to_ir_type(*val_t),
                output: ident(circuit, *output),
            },
            CircuitInstr::PrivateInput {
                guard,
                val_t,
                output,
            } => Instruction::PrivateInput {
                guard: guard.as_ref().map(|g| operand(circuit, g)).transpose()?,
                val_t: to_ir_type(*val_t),
                output: ident(circuit, *output),
            },
            CircuitInstr::ConstrainToBoolean { val } => Instruction::ConstrainToBoolean {
                val: operand(circuit, val)?,
            },
            CircuitInstr::ConstrainBits { val, bits } => Instruction::ConstrainBits {
                val: operand(circuit, val)?,
                bits: *bits,
            },
            CircuitInstr::ConstrainEq { a, b } => Instruction::ConstrainEq {
                a: operand(circuit, a)?,
                b: operand(circuit, b)?,
            },
            CircuitInstr::LessThan { a, b, bits, output } => Instruction::LessThan {
                a: operand(circuit, a)?,
                b: operand(circuit, b)?,
                bits: *bits,
                output: ident(circuit, *output),
            },
            CircuitInstr::Copy { val, output } => Instruction::Copy {
                val: operand(circuit, val)?,
                output: ident(circuit, *output),
            },
            CircuitInstr::Encode { input, outputs } => Instruction::Encode {
                input: operand(circuit, input)?,
                outputs: outputs.iter().map(|v| ident(circuit, *v)).collect(),
            },
            CircuitInstr::Impact { guard, op } => Instruction::Impact {
                guard: operand(circuit, guard)?,
                inputs: operands(circuit, &op.assemble())?,
            },
            CircuitInstr::PersistentHash {
                alignment,
                inputs,
                output,
            } => Instruction::PersistentHash {
                alignment: to_alignment(alignment),
                inputs: operands(circuit, inputs)?,
                output: ident(circuit, *output),
            },
            CircuitInstr::Keccak256 {
                alignment,
                inputs,
                output,
            } => Instruction::Keccak256 {
                alignment: to_alignment(alignment),
                inputs: operands(circuit, inputs)?,
                output: ident(circuit, *output),
            },
            CircuitInstr::Sha512 {
                alignment,
                inputs,
                output,
            } => Instruction::Sha512 {
                alignment: to_alignment(alignment),
                inputs: operands(circuit, inputs)?,
                output: ident(circuit, *output),
            },
            CircuitInstr::TransientHash { inputs, output } => Instruction::TransientHash {
                inputs: operands(circuit, inputs)?,
                output: ident(circuit, *output),
            },
            CircuitInstr::BytesIntoNatives { bytes, outputs } => Instruction::BytesIntoNatives {
                bytes: Operand::Variable(ident(circuit, *bytes)),
                outputs: outputs.iter().map(|v| ident(circuit, *v)).collect(),
            },
            CircuitInstr::BytesFromNatives {
                inputs,
                len,
                output,
            } => Instruction::BytesFromNatives {
                inputs: operands(circuit, inputs)?,
                len: *len,
                output: ident(circuit, *output),
            },
            CircuitInstr::ToBytes { input, output } => Instruction::ToBytes {
                input: operand(circuit, input)?,
                output: ident(circuit, *output),
            },
            CircuitInstr::FromBytes {
                bytes,
                val_t,
                output,
            } => Instruction::FromBytes {
                bytes: Operand::Variable(ident(circuit, *bytes)),
                val_t: to_ir_type(*val_t),
                output: ident(circuit, *output),
            },
            CircuitInstr::Slice {
                bytes,
                start,
                len,
                output,
            } => Instruction::Slice {
                bytes: Operand::Variable(ident(circuit, *bytes)),
                start: *start,
                len: *len,
                output: ident(circuit, *output),
            },
            CircuitInstr::JubjubScalarFromNative { native, output } => {
                Instruction::JubjubScalarFromNative {
                    native: operand(circuit, native)?,
                    output: ident(circuit, *output),
                }
            }
            CircuitInstr::DivModPowerOfTwo {
                val,
                bits,
                quotient,
                remainder,
            } => Instruction::DivModPowerOfTwo {
                val: operand(circuit, val)?,
                bits: *bits,
                outputs: vec![ident(circuit, *quotient), ident(circuit, *remainder)],
            },
            CircuitInstr::TestEq { a, b, output } => Instruction::TestEq {
                a: operand(circuit, a)?,
                b: operand(circuit, b)?,
                output: ident(circuit, *output),
            },
            CircuitInstr::Not { a, output } => Instruction::Not {
                a: operand(circuit, a)?,
                output: ident(circuit, *output),
            },
            CircuitInstr::Add { a, b, output } => Instruction::Add {
                a: operand(circuit, a)?,
                b: operand(circuit, b)?,
                output: ident(circuit, *output),
            },
            CircuitInstr::Mul { a, b, output } => Instruction::Mul {
                a: operand(circuit, a)?,
                b: operand(circuit, b)?,
                output: ident(circuit, *output),
            },
            CircuitInstr::Neg { a, output } => Instruction::Neg {
                a: operand(circuit, a)?,
                output: ident(circuit, *output),
            },
            CircuitInstr::Inv { a, output } => Instruction::Inv {
                a: operand(circuit, a)?,
                output: ident(circuit, *output),
            },
            CircuitInstr::EcMul { a, scalar, output } => Instruction::EcMul {
                a: operand(circuit, a)?,
                scalar: operand(circuit, scalar)?,
                output: ident(circuit, *output),
            },
            CircuitInstr::EcMulGenerator { scalar, output } => Instruction::EcMulGenerator {
                scalar: operand(circuit, scalar)?,
                output: ident(circuit, *output),
            },
            CircuitInstr::HashToCurve { inputs, output } => Instruction::HashToCurve {
                inputs: operands(circuit, inputs)?,
                output: ident(circuit, *output),
            },
            CircuitInstr::IntoCoordinates { point, x, y } => Instruction::IntoCoordinates {
                point: operand(circuit, point)?,
                outputs: (ident(circuit, *x), ident(circuit, *y)),
            },
            CircuitInstr::FromCoordinates { x, y, output } => Instruction::FromCoordinates {
                inputs: (operand(circuit, x)?, operand(circuit, y)?),
                output: ident(circuit, *output),
            },
            CircuitInstr::CondSelect { bit, a, b, output } => Instruction::CondSelect {
                bit: operand(circuit, bit)?,
                a: operand(circuit, a)?,
                b: operand(circuit, b)?,
                output: ident(circuit, *output),
            },
            CircuitInstr::Assert { cond } => Instruction::Assert {
                cond: operand(circuit, cond)?,
            },
            CircuitInstr::Output { vals } => Instruction::Output {
                vals: operands(circuit, vals)?,
            },
        };
        out.push(zkir_instr);
    }
    Ok(out)
}

fn write_json_array<T: Serialize>(
    out: &mut String,
    key: &str,
    items: &[T],
    trailing_comma: bool,
) -> Result<(), serde_json::Error> {
    writeln!(out, "  \"{key}\": [").unwrap();
    for (idx, item) in items.iter().enumerate() {
        let serialized = serde_json::to_string(item)?;
        let comma = if idx + 1 < items.len() { "," } else { "" };
        writeln!(out, "    {serialized}{comma}").unwrap();
    }
    let end_comma = if trailing_comma { "," } else { "" };
    writeln!(out, "  ]{end_comma}").unwrap();
    Ok(())
}

/// Render a `.zkir` v3.1 JSON document with one compact `serde_json`-serialized entry per line.
fn render_zkir_json(
    inputs: &[ZkirInput],
    outputs: &[IrType],
    instructions: &[Instruction],
) -> Result<String, serde_json::Error> {
    let version = serde_json::to_string(&ZkirVersion { major: 3, minor: 1 })?;
    let mut out = String::new();
    writeln!(out, "{{").unwrap();
    writeln!(out, "  \"version\": {version},").unwrap();
    writeln!(out, "  \"do_communications_commitment\": true,").unwrap();
    write_json_array(&mut out, "inputs", inputs, true)?;
    write_json_array(&mut out, "outputs", outputs, true)?;
    write_json_array(&mut out, "instructions", instructions, false)?;
    writeln!(out, "}}").unwrap();
    Ok(out)
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

    #[test]
    fn zkir_election_contract() {
        assert_compact_snapshot!(
            r#"
            export {vote$commit, vote$reveal, advance, set_topic, add_voter}

            import CompactStandardLibrary;

            enum PublicState { setup, commit, reveal, final, }
            enum PrivateState { initial, committed, revealed, }
            enum PermissibleVotes { yes, no, }

            ledger authority: Bytes<32>;
            ledger state: PublicState;
            ledger topic: Maybe<Opaque<"string">>;
            ledger tally_yes: Counter;
            ledger tally_no: Counter;
            ledger committed_votes: MerkleTree<10, Bytes<32>>;
            ledger eligible_voters: MerkleTree<10, Bytes<32>>;
            ledger committed: Set<Bytes<32>>;
            ledger revealed: Set<Bytes<32>>;

            witness private$secret_key(): Bytes<32>;
            witness private$state(): PrivateState;
            witness private$state$advance(): [];
            witness private$vote$record(ballot: PermissibleVotes): [];
            witness private$vote(): PermissibleVotes;
            witness context$eligible_voters$path_of(pk: Bytes<32>): Maybe<MerkleTreePath<10, Bytes<32>>>;
            witness context$committed_votes$path_of(cm: Bytes<32>): Maybe<MerkleTreePath<10, Bytes<32>>>;

            circuit ballot_repr(ballot: PermissibleVotes): Bytes<32> {
              return ballot == PermissibleVotes.yes ? pad(32, "yes") : pad(32, "no");
            }

            circuit vote$commit(ballot: PermissibleVotes): [] {
              assert(state.read() == PublicState.commit && private$state() == PrivateState.initial, "In illegal state for committing");
              private$vote$record(ballot);
              const sk = private$secret_key();
              const com_nul = commitment_nullifier(sk);
              assert(!committed.member(com_nul), "Unexpected attempt to double use of nullifier");
              const pk = public_key(sk);
              const path = disclose(context$eligible_voters$path_of(pk));
              assert(path.is_some &&
                     eligible_voters.checkRoot(disclose(merkleTreePathRoot<10, Bytes<32>>(path.value))) &&
                     pk == path.value.leaf, "Attempted to vote without authorization - need to add-voter");
              const cm = commit_with_sk(ballot_repr(ballot), sk);
              committed_votes.insert(cm);
              committed.insert(com_nul);
              private$state$advance();
            }

            circuit vote$reveal(): [] {
              assert(state.read() == PublicState.reveal && private$state() == PrivateState.committed, "In illegal state for revealing");
              const sk = private$secret_key();
              const rev_nul = reveal_nullifier(sk);
              assert(!revealed.member(rev_nul), "Attempted to double vote");
              const vote = private$vote();
              const cm = commit_with_sk(ballot_repr(vote), sk);
              const path = disclose(context$committed_votes$path_of(cm));
              assert(path.is_some &&
                     committed_votes.checkRoot(disclose(merkleTreePathRoot<10, Bytes<32>>(path.value))) &&
                     cm == path.value.leaf, "Attempted to reveal incorrectly");
              if(disclose(vote) == PermissibleVotes.yes) {
                tally_yes.increment(1);
              } else {
                tally_no.increment(1);
              }
              revealed.insert(rev_nul);
              private$state$advance();
            }

            circuit advance(): [] {
              const sk = private$secret_key();
              const apk = public_key(sk);
              assert(apk == authority.read(), "Attempted to advance state without authorization");
              assert(topic.read().is_some, "Attempted to start election without a topic");
              state.write(successor(state.read()));
            }

            circuit successor(state: PublicState): PublicState {
              if(state == PublicState.setup) {
                return PublicState.commit;
              } else if(state == PublicState.commit) {
                return PublicState.reveal;
              } else {
                return PublicState.final;
              }
            }

            circuit set_topic(t: Opaque<"string">): [] {
              const sk = private$secret_key();
              const apk = public_key(sk);
              assert(apk == authority.read(), "Attempted to set topic without authorization");
              assert(state.read() == PublicState.setup, "Attempted to set topic after setup phase");
              topic.write(Maybe<Opaque<"string">>{ is_some: true, value: disclose(t) });
            }

            circuit add_voter(pk: Bytes<32>): [] {
              assert(!context$eligible_voters$path_of(pk).is_some, "Attempted to add a voter twice");
              const sk = private$secret_key();
              const apk = public_key(sk);
              assert(apk == authority.read(), "Attempted to add a voter without authorization");
              assert(state.read() == PublicState.setup, "Attempted to add a voter after setup phase");
              eligible_voters.insert(disclose(pk));
            }

            circuit commitment_nullifier(sk: Bytes<32>): Bytes<32> {
              return disclose(persistentHash<Vector<2, Bytes<32>>>([pad(32, "lares:election:cm-nul:"), sk]));
            }

            circuit reveal_nullifier(sk: Bytes<32>): Bytes<32> {
              return disclose(persistentHash<Vector<2, Bytes<32>>>([pad(32, "lares:election:rv-nul:"), sk]));
            }

            circuit public_key(sk: Bytes<32>): Bytes<32> {
              return disclose(persistentHash<Vector<2, Bytes<32>>>([pad(32, "lares:election:pk:"), sk]));
            }

            circuit commit_with_sk(ballot: Bytes<32>, sk: Bytes<32>): Bytes<32> {
              return disclose(persistentHash<Vector<2, Bytes<32>>>([ballot, sk]));
            }
            "#,
            compile_all_zkir
        );
    }

    #[test]
    fn zkir_zerocash_contract() {
        assert_compact_snapshot!(
            file: include_str!("../../../examples/zerocash.compact"),
            compile_all_zkir
        );
    }

    #[test]
    fn zkir_map_nested_counter() {
        assert_compact_snapshot!(
            r#"
            import CompactStandardLibrary;

            export ledger c: Map<Boolean, Map<Field, Counter>>;

            export circuit test(): [] {
              c.insert(true, default<Map<Field, Counter>>);
              c.insert(false, default<Map<Field, Counter>>);
              c.lookup(true).insert(1 as Field, default<Counter>);
              c.lookup(false).insert(2 as Field, default<Counter>);
              c.lookup(true).insert(3 as Field, default<Counter>);
              c.lookup(false).lookup(2 as Field).increment(5);
            }
            "#,
            compile_all_zkir
        );
    }

    #[test]
    fn zkir_list_field() {
        assert_compact_snapshot!(
            r#"
            import CompactStandardLibrary;

            export ledger c: List<Field>;

            export circuit test(): [] {
              assert(c.isEmpty() == true, "Structure should be empty");
              assert(c.length() == 0, "Size should be 0");
              assert(c.head().is_some == false, "Head should not exist");

              c.pushFront(0 as Field);
              assert(c.length() == 1, "Size should be 1");
              assert(c.head().is_some == true, "Head should exist");
              assert(c.head().value == 0 as Field, "Head should have value 0");

              c.pushFront(1 as Field);
              assert(c.length() == 2, "Size should be 2");
              assert(c.head().value == 1 as Field, "Head should have value 1");

              c.popFront();
              assert(c.length() == 1, "Size should be 1");
              assert(c.head().value == 0 as Field, "Head should have value 0");

              c.popFront();
              assert(c.head().is_some == false, "Head should not exist");

              c.resetToDefault();
              assert(c.length() == 0, "Size should be 0");
              assert(c.isEmpty() == true, "Structure should be empty");
            }
            "#,
            compile_all_zkir
        );
    }

    #[test]
    fn zkir_map_field_list_field() {
        assert_compact_snapshot!(
            r#"
            import CompactStandardLibrary;

            export ledger c: Map<Field, List<Field>>;

            export circuit test(): [] {
              assert(c.isEmpty() == true, "Structure should be empty");
              assert(c.size() == 0, "Size should be 0");

              c.insert(0 as Field, default<List<Field>>);
              assert(c.size() == 1, "Size should be 1");
              assert(c.lookup(0 as Field).length() == 0, "Key 0 should have value 1");

              c.insertDefault(1 as Field);
              assert(c.size() == 2, "Size should be 2");
              assert(c.lookup(1 as Field).length() == 0, "Key 1 should have value 0");
              assert(c.member(1 as Field) == true, "Key 1 should be member");

              c.remove(0 as Field);
              assert(c.size() == 1, "Size should be 1");

              c.resetToDefault();
              assert(c.size() == 0, "Size should be 0");
              assert(c.isEmpty() == true, "Structure should be empty");
            }
            "#,
            compile_all_zkir
        );
    }

    #[test]
    fn zkir_for_loops_and_arithmetic() {
        assert_compact_snapshot!(
            r#"
            import CompactStandardLibrary;

            export ledger totals: Map<Field, Counter>;
            export ledger items: List<Field>;

            export circuit seed_and_check(batch: Vector<3, Field>, a: Uint<32>, b: Uint<32>, limit: Uint<64>): Boolean {
              for (const i of 0..3) {
                totals.insertDefault(i as Field);
              }
              for (const x of batch) {
                items.pushFront(disclose(x));
              }
              const prod = a * b;
              return a < b && a <= b && b > a && b >= a && prod <= limit;
            }
            "#,
            compile_all_zkir
        );
    }

    #[test]
    fn zkir_modules_generics_and_slicing() {
        assert_compact_snapshot!(
            r#"
            pragma language_version >= 0.16.0 && <= 1.0.0;

            import CompactStandardLibrary;

            type Step = Uint<16>;
            export new type Tag<#N> = Bytes<N>;

            struct Pair<A, B> {
              first: A;
              second: B;
            }

            module Burst<#N> {
              export ledger counter: Counter;

              export circuit run(step: Step): [] {
                for (const i of 0..N) {
                  counter.increment(disclose(step));
                }
              }
            }

            import Burst<2> prefix B_;
            export { B_run }

            circuit first_of<A, B>(p: Pair<A, B>): A {
              return p.first;
            }

            export circuit inspect(v: Vector<3, Field>, idx: Uint<8>, raw: Bytes<8>): [Field, Vector<2, Field>, Tag<4>] {
              const p: Pair<Field, Field> = Pair<Field, Field>{ first: v[0], second: v[idx] };
              const head = slice<2>(v, 0);
              const tag: Tag<4> = slice<4>(raw, 2) as Tag<4>;
              B_run(1);
              return [first_of<Field, Field>(p), head, tag];
            }
            "#,
            compile_all_zkir
        );
    }

    #[test]
    fn zkir_patterns_map_fold_and_commits() {
        assert_compact_snapshot!(
            file: include_str!("../../../examples/functional_patterns.compact"),
            compile_all_zkir
        );
    }

    #[test]
    fn zkir_kernel_block_time_and_tokens() {
        assert_compact_snapshot!(
            file: include_str!("../../../examples/token_vault.compact"),
            compile_all_zkir
        );
    }

    #[test]
    fn zkir_crypto_curves_and_signatures() {
        assert_compact_snapshot!(
            file: include_str!("../../../examples/crypto_curves.compact"),
            compile_all_zkir
        );
    }

    #[test]
    fn zkir_composable_contracts_events_and_serialize() {
        assert_compact_snapshot!(
            file: include_str!("../../../examples/composable_events.compact"),
            compile_all_zkir
        );
    }
}
