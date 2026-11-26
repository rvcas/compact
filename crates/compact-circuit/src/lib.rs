pub mod optimize;

use std::collections::HashMap;

pub use optimize::{optimize_circuit, optimize_program};

use compact_hir::{
    BinaryOp, Circuit, CurveFieldKind, CurveKind, Expr, ExprKind, LedgerAdt, LedgerOp, LocalId,
    NativeWitnessKind, Program, Stmt, Type, UnaryOp,
};
use sha2::{Digest, Sha256};

/// Compute the on-chain entry-point hash for a cross-contract callee circuit name:
/// `SHA-256(pad32("midnight:entry-point") || utf8(method))`.
fn entry_point_hash(method: &str) -> [u8; 32] {
    let mut preimage = Vec::with_capacity(32 + method.len());
    preimage.extend_from_slice(b"midnight:entry-point");
    preimage.resize(32, 0);
    preimage.extend_from_slice(method.as_bytes());
    Sha256::digest(&preimage).into()
}

/// Number of bytes packed per native BLS12-381 scalar wire in ZKIR v3 (248 bits).
pub const FIELD_BYTES: u32 = 31;

/// SSA variable inside a flattened proof circuit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CircuitVar {
    pub id: u32,
}

/// SSA operand: a variable reference, a small signed integer immediate, or an
/// arbitrary-width little-endian byte immediate (up to 31 bytes for native field elements).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CircuitVal {
    Var(CircuitVar),
    Imm(i128),
    ImmBytes(Vec<u8>),
}

impl CircuitVal {
    pub const TRUE: Self = Self::Imm(1);
    pub const FALSE: Self = Self::Imm(0);

    pub fn is_const_true(&self) -> bool {
        matches!(self, Self::Imm(1))
    }

    pub fn is_const_false(&self) -> bool {
        matches!(self, Self::Imm(0))
    }
}

/// ZKIR v3.1 wire type for typed circuit inputs, outputs, and public/private inputs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum WireType {
    Native,
    JubjubPoint,
    JubjubScalar,
    Secp256k1Point,
    Secp256k1Base,
    Secp256k1Scalar,
    Secp256r1Point,
    Secp256r1Base,
    Secp256r1Scalar,
    Curve25519Point,
    Curve25519Base,
    Curve25519Scalar,
}

impl WireType {
    pub fn from_field(field: CurveFieldKind) -> Self {
        match field {
            CurveFieldKind::JubjubScalar => Self::JubjubScalar,
            CurveFieldKind::Secp256k1Base => Self::Secp256k1Base,
            CurveFieldKind::Secp256k1Scalar => Self::Secp256k1Scalar,
            CurveFieldKind::Secp256r1Base => Self::Secp256r1Base,
            CurveFieldKind::Secp256r1Scalar => Self::Secp256r1Scalar,
            CurveFieldKind::Curve25519Base => Self::Curve25519Base,
            CurveFieldKind::Curve25519Scalar => Self::Curve25519Scalar,
        }
    }

    pub fn from_point(curve: CurveKind) -> Self {
        match curve {
            CurveKind::Jubjub => Self::JubjubPoint,
            CurveKind::Secp256k1 => Self::Secp256k1Point,
            CurveKind::Secp256r1 => Self::Secp256r1Point,
            CurveKind::Curve25519 => Self::Curve25519Point,
        }
    }

    /// Number of raw `Native` field elements produced by `Instruction::Encode` for this wire type.
    pub fn encoded_native_count(self) -> usize {
        match self {
            Self::Native | Self::JubjubScalar => 1,
            Self::JubjubPoint
            | Self::Secp256k1Base
            | Self::Secp256k1Scalar
            | Self::Secp256r1Base
            | Self::Secp256r1Scalar
            | Self::Curve25519Base
            | Self::Curve25519Scalar => 2,
            Self::Curve25519Point => 4,
            Self::Secp256k1Point | Self::Secp256r1Point => 5,
        }
    }
}

/// Alignment atom for Impact VM cell encoding and hash gates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AlignmentAtom {
    Bytes(u32),
    Field,
    /// Compressed/opaque value (`acompress` -> `-0x01` in Impact VM).
    Compress,
}

impl AlignmentAtom {
    /// Flatten a Compact type into its Impact/ZKIR alignment atom sequence.
    pub fn alignment_of(program: &Program, ty: &Type) -> Vec<Self> {
        match program.underlying_type(ty) {
            Type::Field => vec![Self::Field],
            Type::Boolean | Type::Enum(_) => vec![Self::Bytes(1)],
            Type::Uint(bits) => vec![Self::Bytes((*bits).div_ceil(8))],
            Type::Bytes(len) => vec![Self::Bytes(*len)],
            Type::Contract(_) => vec![Self::Bytes(32)],
            Type::CurveField(CurveFieldKind::JubjubScalar) => vec![Self::Field],
            Type::CurveField(CurveFieldKind::Curve25519Scalar) => {
                vec![Self::Bytes(26), Self::Bytes(7)]
            }
            Type::CurveField(_) => vec![Self::Bytes(24), Self::Bytes(8)],
            Type::CurvePoint(CurveKind::Jubjub) => vec![Self::Field, Self::Field],
            Type::CurvePoint(CurveKind::Secp256k1 | CurveKind::Secp256r1) => vec![
                Self::Bytes(24),
                Self::Bytes(8),
                Self::Bytes(24),
                Self::Bytes(8),
                Self::Field,
            ],
            Type::CurvePoint(CurveKind::Curve25519) => vec![
                Self::Bytes(24),
                Self::Bytes(8),
                Self::Bytes(24),
                Self::Bytes(8),
            ],
            Type::Opaque(_) => vec![Self::Compress],
            Type::Vector(len, elem) => {
                let single = Self::alignment_of(program, elem);
                let mut out = Vec::with_capacity(single.len() * (*len as usize));
                for _ in 0..*len {
                    out.extend_from_slice(&single);
                }
                out
            }
            Type::Tuple(elems) => elems
                .iter()
                .flat_map(|e| Self::alignment_of(program, e))
                .collect(),
            Type::Struct(_)
            | Type::Maybe(_)
            | Type::Either(_, _)
            | Type::MerkleTreeDigest
            | Type::MerkleTreePathEntry
            | Type::MerkleTreePath(_, _) => program
                .struct_fields_of(ty)
                .unwrap_or_default()
                .iter()
                .flat_map(|(_, fty)| Self::alignment_of(program, fty))
                .collect(),
            Type::NewType(_) => unreachable!("underlying_type peeled all NewType layers"),
        }
    }

    /// Encode alignment atom as a ZKIR Impact VM immediate (`abytes(n)` -> `n`, `afield` -> `-2`, `acompress` -> `-1`).
    pub fn as_imm(self) -> i128 {
        match self {
            Self::Bytes(n) => n as i128,
            Self::Field => -2,
            Self::Compress => -1,
        }
    }
}

/// Ordered ZKIR wire types representing a Compact type.
pub fn wire_types(program: &Program, ty: &Type) -> Vec<WireType> {
    match program.underlying_type(ty) {
        Type::Field | Type::Boolean | Type::Uint(_) | Type::Enum(_) | Type::Opaque(_) => {
            vec![WireType::Native]
        }
        Type::Bytes(0) => Vec::new(),
        Type::Bytes(len) => vec![WireType::Native; (*len).div_ceil(FIELD_BYTES) as usize],
        Type::Contract(_) => vec![WireType::Native, WireType::Native],
        Type::CurveField(f) => vec![WireType::from_field(*f)],
        Type::CurvePoint(c) => vec![WireType::from_point(*c)],
        Type::Vector(len, elem) => {
            let single = wire_types(program, elem);
            let mut out = Vec::with_capacity(single.len() * (*len as usize));
            for _ in 0..*len {
                out.extend_from_slice(&single);
            }
            out
        }
        Type::Tuple(elems) => elems.iter().flat_map(|e| wire_types(program, e)).collect(),
        Type::Struct(_)
        | Type::Maybe(_)
        | Type::Either(_, _)
        | Type::MerkleTreeDigest
        | Type::MerkleTreePathEntry
        | Type::MerkleTreePath(_, _) => program
            .struct_fields_of(ty)
            .unwrap_or_default()
            .iter()
            .flat_map(|(_, fty)| wire_types(program, fty))
            .collect(),
        Type::NewType(_) => unreachable!("underlying_type peeled all NewType layers"),
    }
}

/// Number of ZKIR wires representing a Compact type.
pub fn wire_count(program: &Program, ty: &Type) -> usize {
    match program.underlying_type(ty) {
        Type::Field
        | Type::Boolean
        | Type::Uint(_)
        | Type::Enum(_)
        | Type::Opaque(_)
        | Type::CurveField(_)
        | Type::CurvePoint(_) => 1,
        Type::Bytes(0) => 0,
        Type::Bytes(len) => (*len).div_ceil(FIELD_BYTES) as usize,
        Type::Contract(_) => 2,
        Type::Vector(len, elem) => (*len as usize) * wire_count(program, elem),
        Type::Tuple(elems) => elems.iter().map(|e| wire_count(program, e)).sum(),
        Type::Struct(_)
        | Type::Maybe(_)
        | Type::Either(_, _)
        | Type::MerkleTreeDigest
        | Type::MerkleTreePathEntry
        | Type::MerkleTreePath(_, _) => program
            .struct_fields_of(ty)
            .unwrap_or_default()
            .iter()
            .map(|(_, fty)| wire_count(program, fty))
            .sum(),
        Type::NewType(_) => unreachable!("underlying_type peeled all NewType layers"),
    }
}

/// Default native-encoded Impact cell values for a Compact type.
fn default_encoded_native_values(program: &Program, ty: &Type) -> Vec<CircuitVal> {
    match program.underlying_type(ty) {
        Type::Field | Type::Boolean | Type::Uint(_) | Type::Enum(_) | Type::Opaque(_) => {
            vec![CircuitVal::Imm(0)]
        }
        Type::Bytes(0) => Vec::new(),
        Type::Bytes(len) => vec![CircuitVal::Imm(0); (*len).div_ceil(FIELD_BYTES) as usize],
        Type::Contract(_) => vec![CircuitVal::Imm(0), CircuitVal::Imm(0)],
        Type::CurveField(f) => {
            vec![CircuitVal::Imm(0); WireType::from_field(*f).encoded_native_count()]
        }
        Type::CurvePoint(CurveKind::Jubjub) => vec![CircuitVal::Imm(0), CircuitVal::Imm(1)],
        Type::CurvePoint(CurveKind::Secp256k1 | CurveKind::Secp256r1) => vec![
            CircuitVal::Imm(0),
            CircuitVal::Imm(0),
            CircuitVal::Imm(0),
            CircuitVal::Imm(0),
            CircuitVal::Imm(1),
        ],
        Type::CurvePoint(CurveKind::Curve25519) => vec![
            CircuitVal::Imm(0),
            CircuitVal::Imm(0),
            CircuitVal::Imm(1),
            CircuitVal::Imm(0),
        ],
        Type::Vector(len, elem) => {
            let single = default_encoded_native_values(program, elem);
            let mut out = Vec::with_capacity(single.len() * (*len as usize));
            for _ in 0..*len {
                out.extend_from_slice(&single);
            }
            out
        }
        Type::Tuple(elems) => elems
            .iter()
            .flat_map(|e| default_encoded_native_values(program, e))
            .collect(),
        Type::Struct(_)
        | Type::Maybe(_)
        | Type::Either(_, _)
        | Type::MerkleTreeDigest
        | Type::MerkleTreePathEntry
        | Type::MerkleTreePath(_, _) => program
            .struct_fields_of(ty)
            .unwrap_or_default()
            .iter()
            .flat_map(|(_, fty)| default_encoded_native_values(program, fty))
            .collect(),
        Type::NewType(_) => unreachable!("underlying_type peeled all NewType layers"),
    }
}

/// Range constraint required on a circuit input or private witness wire.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum WireConstraint {
    None,
    Zero,
    Boolean,
    Bits(u32),
    LessThan { upper: u128, bits: u32 },
}

fn wire_constraints(program: &Program, ty: &Type) -> Vec<WireConstraint> {
    match program.underlying_type(ty) {
        Type::Field | Type::Opaque(_) | Type::CurveField(_) | Type::CurvePoint(_) => {
            vec![WireConstraint::None]
        }
        Type::Boolean => vec![WireConstraint::Boolean],
        Type::Uint(bits) => vec![WireConstraint::Bits(*bits)],
        Type::Enum(id) => {
            let count = program.enum_decl(*id).variants.len() as u128;
            let maxval = count.saturating_sub(1);
            let c = if maxval == 0 {
                WireConstraint::Zero
            } else if maxval == 1 {
                WireConstraint::Boolean
            } else if (maxval & (maxval + 1)) == 0 {
                WireConstraint::Bits(u128::BITS - maxval.leading_zeros())
            } else {
                let upper = maxval + 1;
                let ilen = u128::BITS - upper.leading_zeros();
                let bits = 2 * ilen.div_ceil(2);
                WireConstraint::LessThan { upper, bits }
            };
            vec![c]
        }
        Type::Bytes(0) => Vec::new(),
        Type::Bytes(len) => {
            let full = *len / FIELD_BYTES;
            let rem = *len % FIELD_BYTES;
            let mut out = Vec::new();
            if rem > 0 {
                out.push(WireConstraint::Bits(rem * 8));
            }
            for _ in 0..full {
                out.push(WireConstraint::Bits(FIELD_BYTES * 8));
            }
            out
        }
        Type::Contract(_) => vec![
            WireConstraint::Bits(8),
            WireConstraint::Bits(FIELD_BYTES * 8),
        ],
        Type::Vector(len, elem) => {
            let single = wire_constraints(program, elem);
            let mut out = Vec::with_capacity(single.len() * (*len as usize));
            for _ in 0..*len {
                out.extend_from_slice(&single);
            }
            out
        }
        Type::Tuple(elems) => elems
            .iter()
            .flat_map(|e| wire_constraints(program, e))
            .collect(),
        Type::Struct(_)
        | Type::Maybe(_)
        | Type::Either(_, _)
        | Type::MerkleTreeDigest
        | Type::MerkleTreePathEntry
        | Type::MerkleTreePath(_, _) => program
            .struct_fields_of(ty)
            .unwrap_or_default()
            .iter()
            .flat_map(|(_, fty)| wire_constraints(program, fty))
            .collect(),
        Type::NewType(_) => unreachable!("underlying_type peeled all NewType layers"),
    }
}

/// Split a fixed-length byte slice into Compact's flattened ZKIR wire order:
/// high remainder chunk first, then 31-byte little-endian chunks.
fn bytes_to_wires(bytes: &[u8]) -> Vec<CircuitVal> {
    if bytes.is_empty() {
        return Vec::new();
    }
    let mut chunks: Vec<&[u8]> = bytes.chunks(FIELD_BYTES as usize).collect();
    chunks.reverse();
    chunks
        .into_iter()
        .map(|chunk| {
            let mut le = chunk.to_vec();
            while le.last() == Some(&0) && le.len() > 1 {
                le.pop();
            }
            if le.len() == 1 && le[0] == 0 {
                CircuitVal::Imm(0)
            } else {
                CircuitVal::ImmBytes(le)
            }
        })
        .collect()
}

/// Conservative upper bound on serialized cell byte size (matching upstream `VMmax-sizeof`).
fn max_sizeof(alignment: &[AlignmentAtom]) -> u64 {
    fn ceil_bytes(n: u64) -> u64 {
        let bits = (u64::BITS - n.leading_zeros()) as u64;
        bits.div_ceil(8)
    }
    if alignment.is_empty() {
        return 2;
    }
    let header = 1 + ceil_bytes(alignment.len() as u64);
    let body: u64 = alignment
        .iter()
        .map(|atom| match atom {
            AlignmentAtom::Bytes(0) => 3,
            AlignmentAtom::Bytes(n) => 2 + (*n as u64) + ceil_bytes(*n as u64),
            AlignmentAtom::Field | AlignmentAtom::Compress => 34,
        })
        .sum();
    header + body
}

/// Evaluate a constant integer expression (supporting `+`, `-`, `*` on integer literals)
/// for Impact VM immediate operands such as `Counter.increment(16 * 16 * 16)`.
fn eval_const_u128(expr: &Expr) -> Option<u128> {
    match &expr.kind {
        ExprKind::IntLit(v) => Some(*v),
        ExprKind::Cast { expr, .. } | ExprKind::Disclose(expr) => eval_const_u128(expr),
        ExprKind::Binary { op, lhs, rhs } => {
            let l = eval_const_u128(lhs)?;
            let r = eval_const_u128(rhs)?;
            match op {
                BinaryOp::Add => l.checked_add(r),
                BinaryOp::Sub => l.checked_sub(r),
                BinaryOp::Mul => l.checked_mul(r),
                _ => None,
            }
        }
        _ => None,
    }
}

/// A single segment in an Impact VM ledger state path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PathSegment {
    /// Static ledger tree slot index (1-byte aligned cell).
    Static(u32),
    /// Runtime dynamic key value (e.g. a `Map` key lookup).
    Dynamic {
        alignment: Vec<AlignmentAtom>,
        values: Vec<CircuitVal>,
    },
    /// Pop key dynamically from the Impact VM stack (`'stack` -> `-1`).
    Stack,
}

impl PathSegment {
    fn encode_path(&self, out: &mut Vec<CircuitVal>) {
        match self {
            Self::Static(seg) => {
                out.push(CircuitVal::Imm(0x01));
                out.push(CircuitVal::Imm(0x01));
                out.push(CircuitVal::Imm(*seg as i128));
            }
            Self::Dynamic { alignment, values } => {
                out.push(CircuitVal::Imm(alignment.len() as i128));
                for atom in alignment {
                    out.push(CircuitVal::Imm(atom.as_imm()));
                }
                out.extend(values.iter().cloned());
            }
            Self::Stack => out.push(CircuitVal::Imm(-1)),
        }
    }

    fn into_cell_state_value(self) -> ImpactStateValue {
        match self {
            Self::Static(seg) => ImpactStateValue::Cell {
                alignment: vec![AlignmentAtom::Bytes(1)],
                values: vec![CircuitVal::Imm(seg as i128)],
            },
            Self::Dynamic { alignment, values } => ImpactStateValue::Cell { alignment, values },
            Self::Stack => unreachable!("stack segment cannot be converted to a literal cell"),
        }
    }
}

/// Structured Impact VM `StateValue` payload for `push` / `pushs`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImpactStateValue {
    Null,
    Cell {
        alignment: Vec<AlignmentAtom>,
        values: Vec<CircuitVal>,
    },
    EmptyMap,
    MerkleTree {
        depth: u32,
    },
    Array(Vec<ImpactStateValue>),
}

impl ImpactStateValue {
    fn cell_u8(val: u8) -> Self {
        Self::Cell {
            alignment: vec![AlignmentAtom::Bytes(1)],
            values: vec![CircuitVal::Imm(val as i128)],
        }
    }

    fn cell_u32(val: u32) -> Self {
        Self::Cell {
            alignment: vec![AlignmentAtom::Bytes(4)],
            values: vec![CircuitVal::Imm(val as i128)],
        }
    }

    fn cell_u64(val: u64) -> Self {
        Self::Cell {
            alignment: vec![AlignmentAtom::Bytes(8)],
            values: vec![CircuitVal::Imm(val as i128)],
        }
    }

    fn encode(&self, out: &mut Vec<CircuitVal>) {
        match self {
            Self::Null => out.push(CircuitVal::Imm(0x00)),
            Self::Cell { alignment, values } => {
                out.push(CircuitVal::Imm(0x01));
                out.push(CircuitVal::Imm(alignment.len() as i128));
                for atom in alignment {
                    out.push(CircuitVal::Imm(atom.as_imm()));
                }
                out.extend(values.iter().cloned());
            }
            Self::EmptyMap => out.push(CircuitVal::Imm(0x02)),
            Self::MerkleTree { depth } => {
                out.push(CircuitVal::Imm((4u32 | (*depth << 4)) as i128));
            }
            Self::Array(elems) => {
                out.push(CircuitVal::Imm((((elems.len() as u32) << 4) | 3) as i128));
                for elem in elems {
                    elem.encode(out);
                }
            }
        }
    }
}

fn adt_initial_state_value(program: &Program, adt: &LedgerAdt) -> ImpactStateValue {
    match adt {
        LedgerAdt::Cell(ty) => ImpactStateValue::Cell {
            alignment: AlignmentAtom::alignment_of(program, ty),
            values: default_encoded_native_values(program, ty),
        },
        LedgerAdt::Counter => ImpactStateValue::cell_u64(0),
        LedgerAdt::Set(_) | LedgerAdt::Map { .. } => ImpactStateValue::EmptyMap,
        LedgerAdt::List(_) => ImpactStateValue::Array(vec![
            ImpactStateValue::Null,
            ImpactStateValue::Null,
            ImpactStateValue::cell_u64(0),
        ]),
        LedgerAdt::MerkleTree { depth, .. } => ImpactStateValue::Array(vec![
            ImpactStateValue::MerkleTree { depth: *depth },
            ImpactStateValue::cell_u64(0),
        ]),
        LedgerAdt::HistoricMerkleTree { depth, .. } => ImpactStateValue::Array(vec![
            ImpactStateValue::MerkleTree { depth: *depth },
            ImpactStateValue::cell_u64(0),
            ImpactStateValue::EmptyMap,
        ]),
        LedgerAdt::Kernel => ImpactStateValue::Null,
    }
}

/// A single Impact VM instruction lowered for a ledger operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImpactVmOp {
    /// `dup n` (`0x3n`) — duplicate stack item at depth `n`.
    Dup { n: u8 },
    /// `swap n` (`0x4n`) — swap top of stack with item at depth `n + 1`.
    Swap { n: u8 },
    /// `idx` / `idxc` / `idxp` / `idxpc` — index into public ledger state along `path`.
    Idx {
        cached: bool,
        push_path: bool,
        path: Vec<PathSegment>,
    },
    /// `popeq` / `popeqc` — pop state value from VM stack and constrain equal to `results`.
    Popeq {
        cached: bool,
        alignment: Vec<AlignmentAtom>,
        results: Vec<CircuitVal>,
    },
    /// `push` / `pushs` — push a `StateValue` onto the VM stack.
    Push {
        storage: bool,
        value: ImpactStateValue,
    },
    /// `lt` (`0x01`) — pop two stack items and push less-than boolean.
    Lt,
    /// `eq` (`0x02`) — pop two stack items and push equality boolean.
    Eq,
    /// `type` (`0x03`) — pop a state value and push its type tag (`0` = Cell, `1` = Null, ...).
    Type,
    /// `size` (`0x04`) — pop a map/set/array and push its `Uint<64>` size.
    Size,
    /// `neg` (`0x08`) — negate boolean on top of stack.
    Neg,
    /// `log` (`0x09`) — emit a versioned event log item popped from top of stack.
    Log,
    /// `root` (`0x0a`) — pop a Merkle tree and push its root digest cell.
    Root,
    /// `pop` (`0x0b`) — discard top of stack.
    Pop,
    /// `branch` (`0x12`) — pop boolean and skip `skip` VM instructions if true.
    Branch { skip: u32 },
    /// `jmp` (`0x13`) — unconditionally skip `skip` VM instructions.
    Jmp { skip: u32 },
    /// `add` (`0x14`) — pop two counter/uint cells and push their sum.
    Add,
    /// `concat` / `concatc` (`0x16` / `0x17`) — concatenate two cells up to `n` bytes.
    Concat { cached: bool, n: u64 },
    /// `member` (`0x18`) — pop key & set/map and push membership boolean.
    Member,
    /// `rem` / `remc` (`0x19` / `0x1a`) — remove key from set/map.
    Rem { cached: bool },
    /// `addi` (`0x0e`) — add `Uint<16>` to counter cell on stack.
    Addi { immediate: CircuitVal },
    /// `subi` (`0x0f`) — subtract `Uint<16>` from counter cell on stack.
    Subi { immediate: CircuitVal },
    /// `ins` / `insc` (`0x9n` / `0xan`) — write updated value back up `n` path levels.
    Ins { cached: bool, n: u8 },
    /// `ckpt` (`0xff`) — mark execution checkpoint boundary.
    Ckpt,
}

impl ImpactVmOp {
    /// Assemble this Impact VM instruction into the sequence of ZKIR `impact` operands
    /// (matching upstream `reduce-to-zkir.ss`).
    pub fn assemble(&self) -> Vec<CircuitVal> {
        match self {
            Self::Dup { n } => vec![CircuitVal::Imm(0x30 | (*n as i128))],
            Self::Swap { n } => vec![CircuitVal::Imm(0x40 | (*n as i128))],
            Self::Idx {
                cached,
                push_path,
                path,
            } => {
                debug_assert!(!path.is_empty());
                let hi: i128 = match (*push_path, *cached) {
                    (false, false) => 0x5,
                    (false, true) => 0x6,
                    (true, false) => 0x7,
                    (true, true) => 0x8,
                };
                let lo = (path.len() - 1) as i128;
                let mut words = vec![CircuitVal::Imm((hi << 4) | lo)];
                for seg in path {
                    seg.encode_path(&mut words);
                }
                words
            }
            Self::Popeq {
                cached,
                alignment,
                results,
            } => {
                let op = if *cached { 0x0d } else { 0x0c };
                let mut words = vec![
                    CircuitVal::Imm(op),
                    CircuitVal::Imm(alignment.len() as i128),
                ];
                for atom in alignment {
                    words.push(CircuitVal::Imm(atom.as_imm()));
                }
                words.extend(results.iter().cloned());
                words
            }
            Self::Push { storage, value } => {
                let op = if *storage { 0x11 } else { 0x10 };
                let mut words = vec![CircuitVal::Imm(op)];
                value.encode(&mut words);
                words
            }
            Self::Lt => vec![CircuitVal::Imm(0x01)],
            Self::Eq => vec![CircuitVal::Imm(0x02)],
            Self::Type => vec![CircuitVal::Imm(0x03)],
            Self::Size => vec![CircuitVal::Imm(0x04)],
            Self::Neg => vec![CircuitVal::Imm(0x08)],
            Self::Log => vec![CircuitVal::Imm(0x09)],
            Self::Root => vec![CircuitVal::Imm(0x0a)],
            Self::Pop => vec![CircuitVal::Imm(0x0b)],
            Self::Branch { skip } => vec![CircuitVal::Imm(0x12), CircuitVal::Imm(*skip as i128)],
            Self::Jmp { skip } => vec![CircuitVal::Imm(0x13), CircuitVal::Imm(*skip as i128)],
            Self::Add => vec![CircuitVal::Imm(0x14)],
            Self::Concat { cached, n } => vec![
                CircuitVal::Imm(if *cached { 0x17 } else { 0x16 }),
                CircuitVal::Imm(*n as i128),
            ],
            Self::Member => vec![CircuitVal::Imm(0x18)],
            Self::Rem { cached } => vec![CircuitVal::Imm(if *cached { 0x1a } else { 0x19 })],
            Self::Addi { immediate } => vec![CircuitVal::Imm(0x0e), immediate.clone()],
            Self::Subi { immediate } => vec![CircuitVal::Imm(0x0f), immediate.clone()],
            Self::Ins { cached, n } => {
                let hi: i128 = if *cached { 0xa } else { 0x9 };
                vec![CircuitVal::Imm((hi << 4) | (*n as i128))]
            }
            Self::Ckpt => vec![CircuitVal::Imm(0xff)],
        }
    }
}

/// Flattened SSA instruction inside a proof circuit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CircuitInstr {
    PublicInput {
        guard: Option<CircuitVal>,
        val_t: WireType,
        output: CircuitVar,
    },
    PrivateInput {
        guard: Option<CircuitVal>,
        val_t: WireType,
        output: CircuitVar,
    },
    ConstrainToBoolean {
        val: CircuitVal,
    },
    ConstrainBits {
        val: CircuitVal,
        bits: u32,
    },
    ConstrainEq {
        a: CircuitVal,
        b: CircuitVal,
    },
    LessThan {
        a: CircuitVal,
        b: CircuitVal,
        bits: u32,
        output: CircuitVar,
    },
    Copy {
        val: CircuitVal,
        output: CircuitVar,
    },
    Encode {
        input: CircuitVal,
        outputs: Vec<CircuitVar>,
    },
    Impact {
        guard: CircuitVal,
        op: ImpactVmOp,
    },
    PersistentHash {
        alignment: Vec<AlignmentAtom>,
        inputs: Vec<CircuitVal>,
        output: CircuitVar,
    },
    Keccak256 {
        alignment: Vec<AlignmentAtom>,
        inputs: Vec<CircuitVal>,
        output: CircuitVar,
    },
    Sha512 {
        alignment: Vec<AlignmentAtom>,
        inputs: Vec<CircuitVal>,
        output: CircuitVar,
    },
    TransientHash {
        inputs: Vec<CircuitVal>,
        output: CircuitVar,
    },
    BytesIntoNatives {
        bytes: CircuitVar,
        outputs: Vec<CircuitVar>,
    },
    BytesFromNatives {
        inputs: Vec<CircuitVal>,
        len: u32,
        output: CircuitVar,
    },
    ToBytes {
        input: CircuitVal,
        output: CircuitVar,
    },
    FromBytes {
        bytes: CircuitVar,
        val_t: WireType,
        output: CircuitVar,
    },
    Slice {
        bytes: CircuitVar,
        start: u32,
        len: u32,
        output: CircuitVar,
    },
    JubjubScalarFromNative {
        native: CircuitVal,
        output: CircuitVar,
    },
    DivModPowerOfTwo {
        val: CircuitVal,
        bits: u32,
        quotient: CircuitVar,
        remainder: CircuitVar,
    },
    TestEq {
        a: CircuitVal,
        b: CircuitVal,
        output: CircuitVar,
    },
    Not {
        a: CircuitVal,
        output: CircuitVar,
    },
    Add {
        a: CircuitVal,
        b: CircuitVal,
        output: CircuitVar,
    },
    Mul {
        a: CircuitVal,
        b: CircuitVal,
        output: CircuitVar,
    },
    Neg {
        a: CircuitVal,
        output: CircuitVar,
    },
    Inv {
        a: CircuitVal,
        output: CircuitVar,
    },
    EcMul {
        a: CircuitVal,
        scalar: CircuitVal,
        output: CircuitVar,
    },
    EcMulGenerator {
        scalar: CircuitVal,
        output: CircuitVar,
    },
    HashToCurve {
        inputs: Vec<CircuitVal>,
        output: CircuitVar,
    },
    IntoCoordinates {
        point: CircuitVal,
        x: CircuitVar,
        y: CircuitVar,
    },
    FromCoordinates {
        x: CircuitVal,
        y: CircuitVal,
        output: CircuitVar,
    },
    CondSelect {
        bit: CircuitVal,
        a: CircuitVal,
        b: CircuitVal,
        output: CircuitVar,
    },
    Assert {
        cond: CircuitVal,
    },
    Output {
        vals: Vec<CircuitVal>,
    },
}

/// Flattened representation of an exported proof circuit ready for ZKIR codegen.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofCircuit {
    pub name: String,
    /// Debug name hints indexed by `CircuitVar.id`.
    pub var_names: Vec<String>,
    /// Typed input SSA variables.
    pub inputs: Vec<(CircuitVar, WireType)>,
    /// Typed output wire list produced by the final `Output` instruction.
    pub output_types: Vec<WireType>,
    pub instructions: Vec<CircuitInstr>,
}

/// Lowered circuit program containing all exported proof circuits.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CircuitProgram {
    pub circuits: Vec<ProofCircuit>,
}

pub fn lower_to_circuits_unoptimized(program: &Program) -> CircuitProgram {
    let circuits = program
        .proof_circuits()
        .map(|circuit| CircuitLowerer::new(program).lower_root_circuit(circuit))
        .collect();
    CircuitProgram { circuits }
}

pub fn lower_to_circuits(program: &Program) -> CircuitProgram {
    let mut lowered = lower_to_circuits_unoptimized(program);
    optimize_program(&mut lowered);
    lowered
}

struct CircuitLowerer<'a> {
    program: &'a Program,
    var_names: Vec<String>,
    instructions: Vec<CircuitInstr>,
}

impl<'a> CircuitLowerer<'a> {
    fn new(program: &'a Program) -> Self {
        Self {
            program,
            var_names: Vec::new(),
            instructions: Vec::new(),
        }
    }

    fn fresh_var(&mut self, hint: &str) -> CircuitVar {
        let id = self.var_names.len() as u32;
        self.var_names.push(hint.to_owned());
        CircuitVar { id }
    }

    fn emit_wire_constraint(&mut self, var: CircuitVar, constraint: WireConstraint) {
        let val = CircuitVal::Var(var);
        match constraint {
            WireConstraint::None => {}
            WireConstraint::Zero => {
                self.instructions.push(CircuitInstr::ConstrainEq {
                    a: val,
                    b: CircuitVal::Imm(0),
                });
            }
            WireConstraint::Boolean => {
                self.instructions
                    .push(CircuitInstr::ConstrainToBoolean { val });
            }
            WireConstraint::Bits(bits) => {
                self.instructions
                    .push(CircuitInstr::ConstrainBits { val, bits });
            }
            WireConstraint::LessThan { upper, bits } => {
                let tmp = self.fresh_var("tmp");
                self.instructions.push(CircuitInstr::LessThan {
                    a: val,
                    b: CircuitVal::Imm(upper as i128),
                    bits,
                    output: tmp,
                });
                self.instructions.push(CircuitInstr::Assert {
                    cond: CircuitVal::Var(tmp),
                });
            }
        }
    }

    fn emit_not(&mut self, val: &CircuitVal) -> CircuitVal {
        if val.is_const_true() {
            return CircuitVal::FALSE;
        }
        if val.is_const_false() {
            return CircuitVal::TRUE;
        }
        let out = self.fresh_var("t");
        self.instructions.push(CircuitInstr::CondSelect {
            bit: val.clone(),
            a: CircuitVal::FALSE,
            b: CircuitVal::TRUE,
            output: out,
        });
        CircuitVal::Var(out)
    }

    fn select_wires(
        &mut self,
        cond_val: &CircuitVal,
        then_vals: Vec<CircuitVal>,
        else_vals: Vec<CircuitVal>,
    ) -> Vec<CircuitVal> {
        let mut out = Vec::with_capacity(then_vals.len());
        for (a, b) in then_vals.into_iter().zip(else_vals) {
            if a == b {
                out.push(a);
            } else if a.is_const_true() && b.is_const_false() {
                out.push(cond_val.clone());
            } else {
                let sel = self.fresh_var("t");
                self.instructions.push(CircuitInstr::CondSelect {
                    bit: cond_val.clone(),
                    a,
                    b,
                    output: sel,
                });
                out.push(CircuitVal::Var(sel));
            }
        }
        out
    }

    fn pack_bytes_wires(&mut self, byte_vals: &[CircuitVal]) -> Vec<CircuitVal> {
        if byte_vals.is_empty() {
            return Vec::new();
        }
        let mut chunks: Vec<&[CircuitVal]> = byte_vals.chunks(FIELD_BYTES as usize).collect();
        chunks.reverse();
        let mut wires = Vec::with_capacity(chunks.len());
        for chunk in chunks {
            if chunk.iter().all(|v| matches!(v, CircuitVal::Imm(_))) {
                let raw: Vec<u8> = chunk
                    .iter()
                    .map(|v| match v {
                        CircuitVal::Imm(n) => *n as u8,
                        _ => unreachable!(),
                    })
                    .collect();
                wires.extend(bytes_to_wires(&raw));
                continue;
            }
            let k = chunk.len();
            let mut acc = chunk[k - 1].clone();
            for b in chunk[..k - 1].iter().rev() {
                let shifted = self.fresh_var("t");
                self.instructions.push(CircuitInstr::Mul {
                    a: acc,
                    b: CircuitVal::Imm(256),
                    output: shifted,
                });
                let added = self.fresh_var("t");
                self.instructions.push(CircuitInstr::Add {
                    a: CircuitVal::Var(shifted),
                    b: b.clone(),
                    output: added,
                });
                acc = CircuitVal::Var(added);
            }
            wires.push(acc);
        }
        wires
    }

    fn unpack_bytes_wires(&mut self, wires: &[CircuitVal], total_len: u32) -> Vec<CircuitVal> {
        if total_len == 0 {
            return Vec::new();
        }
        let full = total_len / FIELD_BYTES;
        let rem = total_len % FIELD_BYTES;
        let mut chunk_sizes: Vec<u32> = vec![FIELD_BYTES; full as usize];
        if rem > 0 {
            chunk_sizes.push(rem);
        }
        let mut out = Vec::with_capacity(total_len as usize);
        for (wire, k) in wires.iter().rev().zip(chunk_sizes) {
            let mut cur = wire.clone();
            for _ in 0..(k - 1) {
                let q = self.fresh_var("quo");
                let b = self.fresh_var("byte");
                self.instructions.push(CircuitInstr::DivModPowerOfTwo {
                    val: cur,
                    bits: 8,
                    quotient: q,
                    remainder: b,
                });
                out.push(CircuitVal::Var(b));
                cur = CircuitVal::Var(q);
            }
            out.push(cur);
        }
        out
    }

    /// Convert typed curve/foreign-field wires to raw `Native` limbs via `Encode` for Impact VM
    /// cells and hash gates, leaving already-`Native` wires untouched.
    fn encode_to_native_wires(&mut self, ty: &Type, vals: Vec<CircuitVal>) -> Vec<CircuitVal> {
        let wtypes = wire_types(self.program, ty);
        debug_assert_eq!(wtypes.len(), vals.len());
        if wtypes.iter().all(|wt| *wt == WireType::Native) {
            return vals;
        }
        let mut out = Vec::with_capacity(vals.len());
        for (wt, val) in wtypes.into_iter().zip(vals) {
            if wt == WireType::Native {
                out.push(val);
            } else {
                let n = wt.encoded_native_count();
                let mut enc_vars = Vec::with_capacity(n);
                for _ in 0..n {
                    enc_vars.push(self.fresh_var("fld"));
                }
                self.instructions.push(CircuitInstr::Encode {
                    input: val,
                    outputs: enc_vars.clone(),
                });
                for v in enc_vars {
                    out.push(CircuitVal::Var(v));
                }
            }
        }
        out
    }

    /// Emit ZKIR instructions producing the default value for `ty`.
    fn lower_default(&mut self, ty: &Type) -> Vec<CircuitVal> {
        match self.program.underlying_type(ty).clone() {
            Type::Field | Type::Boolean | Type::Uint(_) | Type::Enum(_) | Type::Opaque(_) => {
                vec![CircuitVal::Imm(0)]
            }
            Type::Bytes(0) => Vec::new(),
            Type::Bytes(len) => vec![CircuitVal::Imm(0); len.div_ceil(FIELD_BYTES) as usize],
            Type::Contract(_) => vec![CircuitVal::Imm(0), CircuitVal::Imm(0)],
            Type::CurveField(CurveFieldKind::JubjubScalar) => {
                let out = self.fresh_var("t");
                self.instructions
                    .push(CircuitInstr::JubjubScalarFromNative {
                        native: CircuitVal::Imm(0),
                        output: out,
                    });
                vec![CircuitVal::Var(out)]
            }
            Type::CurveField(field) => {
                let tmp = self.fresh_var("tmp");
                self.instructions.push(CircuitInstr::ToBytes {
                    input: CircuitVal::Imm(0),
                    output: tmp,
                });
                let out = self.fresh_var("t");
                self.instructions.push(CircuitInstr::FromBytes {
                    bytes: tmp,
                    val_t: WireType::from_field(field),
                    output: out,
                });
                vec![CircuitVal::Var(out)]
            }
            Type::CurvePoint(CurveKind::Jubjub) => {
                let out = self.fresh_var("t");
                self.instructions.push(CircuitInstr::FromCoordinates {
                    x: CircuitVal::Imm(0),
                    y: CircuitVal::Imm(1),
                    output: out,
                });
                vec![CircuitVal::Var(out)]
            }
            Type::CurvePoint(curve) => {
                let zero_scalar = self.lower_default(&Type::CurveField(curve.scalar_field()));
                let out = self.fresh_var("t");
                self.instructions.push(CircuitInstr::EcMulGenerator {
                    scalar: zero_scalar.into_iter().next().unwrap(),
                    output: out,
                });
                vec![CircuitVal::Var(out)]
            }
            Type::Vector(len, elem) => {
                let mut out = Vec::new();
                for _ in 0..len {
                    out.extend(self.lower_default(&elem));
                }
                out
            }
            Type::Tuple(elems) => {
                let mut out = Vec::new();
                for e in elems {
                    out.extend(self.lower_default(&e));
                }
                out
            }
            Type::Struct(_)
            | Type::Maybe(_)
            | Type::Either(_, _)
            | Type::MerkleTreeDigest
            | Type::MerkleTreePathEntry
            | Type::MerkleTreePath(_, _) => {
                let mut out = Vec::new();
                for (_, fty) in self.program.struct_fields_of(ty).unwrap_or_default() {
                    out.extend(self.lower_default(&fty));
                }
                out
            }
            Type::NewType(_) => unreachable!("underlying_type peeled all NewType layers"),
        }
    }

    fn lower_root_circuit(mut self, circuit: &Circuit) -> ProofCircuit {
        let mut inputs = Vec::new();
        let mut param_vals: Vec<Vec<CircuitVal>> = Vec::with_capacity(circuit.params.len());
        let mut input_constraints: Vec<(CircuitVar, WireConstraint)> = Vec::new();
        for p in &circuit.params {
            let wtypes = wire_types(self.program, &p.ty);
            let constraints = wire_constraints(self.program, &p.ty);
            let mut wires = Vec::with_capacity(constraints.len());
            for (wt, c) in wtypes.into_iter().zip(constraints) {
                let var = self.fresh_var(&p.name);
                inputs.push((var, wt));
                input_constraints.push((var, c));
                wires.push(CircuitVal::Var(var));
            }
            param_vals.push(wires);
        }
        for (var, c) in input_constraints {
            self.emit_wire_constraint(var, c);
        }

        let ret_vals = self.lower_circuit_body(circuit, &param_vals, &CircuitVal::TRUE);
        let output_types = wire_types(self.program, &circuit.ret_type);
        if !output_types.is_empty() {
            self.instructions
                .push(CircuitInstr::Output { vals: ret_vals });
        }

        ProofCircuit {
            name: circuit.name.clone(),
            var_names: self.var_names,
            inputs,
            output_types,
            instructions: self.instructions,
        }
    }

    fn lower_circuit_body(
        &mut self,
        circuit: &Circuit,
        param_vals: &[Vec<CircuitVal>],
        guard: &CircuitVal,
    ) -> Vec<CircuitVal> {
        let mut locals: HashMap<LocalId, Vec<CircuitVal>> = HashMap::new();
        self.lower_stmts(&circuit.body, param_vals, &mut locals, guard)
            .unwrap_or_default()
    }

    fn lower_stmts(
        &mut self,
        stmts: &[Stmt],
        param_vals: &[Vec<CircuitVal>],
        locals: &mut HashMap<LocalId, Vec<CircuitVal>>,
        guard: &CircuitVal,
    ) -> Option<Vec<CircuitVal>> {
        let mut ret_vals: Option<Vec<CircuitVal>> = None;

        for stmt in stmts {
            match stmt {
                Stmt::Const {
                    local, name, init, ..
                } => {
                    let vals =
                        self.lower_expr_with_hint(init, param_vals, locals, guard, Some(name));
                    locals.insert(*local, vals);
                }
                Stmt::If {
                    cond,
                    then_branch,
                    else_branch,
                    ..
                } => {
                    let cond_val = self
                        .lower_expr(cond, param_vals, locals, guard)
                        .into_iter()
                        .next()
                        .unwrap_or(CircuitVal::FALSE);
                    let then_guard = if stmts_have_effects(then_branch, self.program) {
                        self.combine_guard(guard, &cond_val)
                    } else {
                        guard.clone()
                    };
                    let else_guard = if stmts_have_effects(else_branch, self.program) {
                        let not_cond = self.emit_not(&cond_val);
                        self.combine_guard(guard, &not_cond)
                    } else {
                        guard.clone()
                    };

                    let mut then_locals = locals.clone();
                    let then_ret =
                        self.lower_stmts(then_branch, param_vals, &mut then_locals, &then_guard);
                    let mut else_locals = locals.clone();
                    let else_ret =
                        self.lower_stmts(else_branch, param_vals, &mut else_locals, &else_guard);

                    match (then_ret, else_ret) {
                        (Some(t), Some(e)) => {
                            ret_vals = Some(self.select_wires(&cond_val, t, e));
                        }
                        (Some(t), None) => ret_vals = Some(t),
                        (None, Some(e)) => ret_vals = Some(e),
                        (None, None) => {}
                    }
                }
                Stmt::ForRange {
                    local,
                    start,
                    end,
                    body,
                    ..
                } => {
                    for i in *start..*end {
                        let mut iter_locals = locals.clone();
                        iter_locals.insert(*local, vec![CircuitVal::Imm(i as i128)]);
                        if let Some(r) = self.lower_stmts(body, param_vals, &mut iter_locals, guard)
                        {
                            ret_vals = Some(r);
                        }
                    }
                }
                Stmt::ForEach {
                    local, iter, body, ..
                } => {
                    let iter_vals = self.lower_expr(iter, param_vals, locals, guard);
                    match self.program.underlying_type(&iter.ty).clone() {
                        Type::Vector(len, elem_ty) => {
                            let elem_width = wire_count(self.program, &elem_ty);
                            for i in 0..(len as usize) {
                                let mut iter_locals = locals.clone();
                                let slice =
                                    iter_vals[i * elem_width..(i + 1) * elem_width].to_vec();
                                iter_locals.insert(*local, slice);
                                if let Some(r) =
                                    self.lower_stmts(body, param_vals, &mut iter_locals, guard)
                                {
                                    ret_vals = Some(r);
                                }
                            }
                        }
                        Type::Bytes(len) => {
                            let byte_wires = self.unpack_bytes_wires(&iter_vals, len);
                            for bw in byte_wires {
                                let mut iter_locals = locals.clone();
                                iter_locals.insert(*local, vec![bw]);
                                if let Some(r) =
                                    self.lower_stmts(body, param_vals, &mut iter_locals, guard)
                                {
                                    ret_vals = Some(r);
                                }
                            }
                        }
                        Type::Tuple(elems) if !elems.is_empty() => {
                            let mut offset = 0usize;
                            for elem_ty in &elems {
                                let w = wire_count(self.program, elem_ty);
                                let mut iter_locals = locals.clone();
                                let slice = iter_vals[offset..offset + w].to_vec();
                                offset += w;
                                iter_locals.insert(*local, slice);
                                if let Some(r) =
                                    self.lower_stmts(body, param_vals, &mut iter_locals, guard)
                                {
                                    ret_vals = Some(r);
                                }
                            }
                        }
                        _ => {}
                    }
                }
                Stmt::Expr(expr) => {
                    let _ = self.lower_expr(expr, param_vals, locals, guard);
                }
                Stmt::Return { value, .. } => {
                    ret_vals = Some(
                        value
                            .as_ref()
                            .map(|e| self.lower_expr(e, param_vals, locals, guard))
                            .unwrap_or_default(),
                    );
                }
            }
        }

        ret_vals
    }

    fn combine_guard(&mut self, outer: &CircuitVal, cond: &CircuitVal) -> CircuitVal {
        if outer.is_const_true() {
            return cond.clone();
        }
        let out = self.fresh_var("t");
        self.instructions.push(CircuitInstr::CondSelect {
            bit: outer.clone(),
            a: cond.clone(),
            b: CircuitVal::FALSE,
            output: out,
        });
        CircuitVal::Var(out)
    }

    fn lower_expr(
        &mut self,
        expr: &Expr,
        param_vals: &[Vec<CircuitVal>],
        locals: &HashMap<LocalId, Vec<CircuitVal>>,
        guard: &CircuitVal,
    ) -> Vec<CircuitVal> {
        self.lower_expr_with_hint(expr, param_vals, locals, guard, None)
    }

    fn lower_expr_with_hint(
        &mut self,
        expr: &Expr,
        param_vals: &[Vec<CircuitVal>],
        locals: &HashMap<LocalId, Vec<CircuitVal>>,
        guard: &CircuitVal,
        hint: Option<&str>,
    ) -> Vec<CircuitVal> {
        match &expr.kind {
            ExprKind::IntLit(v) => vec![CircuitVal::Imm(*v as i128)],
            ExprKind::BoolLit(b) => vec![CircuitVal::Imm(i128::from(*b))],
            ExprKind::BytesLit(bytes) => bytes_to_wires(bytes),
            ExprKind::Default(ty) => self.lower_default(ty),
            ExprKind::DefaultAdt(_) => Vec::new(),
            ExprKind::EnumVariant { variant_idx, .. } => {
                vec![CircuitVal::Imm(*variant_idx as i128)]
            }
            ExprKind::ParamRef(pid) => param_vals[pid.0 as usize].clone(),
            ExprKind::LocalRef(lid) => locals.get(lid).cloned().unwrap_or_default(),
            ExprKind::Tuple(elems) | ExprKind::Vector(elems) => {
                let mut out = Vec::new();
                for e in elems {
                    out.extend(self.lower_expr(e, param_vals, locals, guard));
                }
                out
            }
            ExprKind::StructLit { fields } => {
                let mut out = Vec::new();
                for (_, e) in fields {
                    out.extend(self.lower_expr(e, param_vals, locals, guard));
                }
                out
            }
            ExprKind::FieldAccess { base, field } => {
                let base_vals = self.lower_expr(base, param_vals, locals, guard);
                let fields = self
                    .program
                    .struct_fields_of(&base.ty)
                    .expect("sema validated FieldAccess on struct type");
                let mut offset = 0usize;
                for (fname, fty) in fields {
                    let width = wire_count(self.program, &fty);
                    if fname == *field {
                        return base_vals[offset..offset + width].to_vec();
                    }
                    offset += width;
                }
                unreachable!("sema validated struct field `{field}`")
            }
            ExprKind::Index { base, index } => {
                let base_vals = self.lower_expr(base, param_vals, locals, guard);
                match self.program.underlying_type(&base.ty) {
                    Type::Vector(len, elem_ty) => {
                        let elem_width = wire_count(self.program, elem_ty);
                        if let Some(k) = eval_const_u128(index) {
                            let off = (k as usize) * elem_width;
                            return base_vals[off..off + elem_width].to_vec();
                        }
                        let idx_val = self
                            .lower_expr(index, param_vals, locals, guard)
                            .into_iter()
                            .next()
                            .unwrap_or(CircuitVal::Imm(0));
                        let mut acc = base_vals[..elem_width].to_vec();
                        for i in 1..(*len as usize) {
                            let eq = self.fresh_var("t");
                            self.instructions.push(CircuitInstr::TestEq {
                                a: idx_val.clone(),
                                b: CircuitVal::Imm(i as i128),
                                output: eq,
                            });
                            let elem_slice =
                                base_vals[i * elem_width..(i + 1) * elem_width].to_vec();
                            acc = self.select_wires(&CircuitVal::Var(eq), elem_slice, acc);
                        }
                        acc
                    }
                    Type::Tuple(elems) => {
                        if let Some(k) = eval_const_u128(index) {
                            let k = k as usize;
                            let mut offset = 0usize;
                            for (i, ety) in elems.iter().enumerate() {
                                let w = wire_count(self.program, ety);
                                if i == k {
                                    return base_vals[offset..offset + w].to_vec();
                                }
                                offset += w;
                            }
                            unreachable!("sema validated tuple index")
                        }
                        let elem_width = wire_count(self.program, &elems[0]);
                        let idx_val = self
                            .lower_expr(index, param_vals, locals, guard)
                            .into_iter()
                            .next()
                            .unwrap_or(CircuitVal::Imm(0));
                        let mut acc = base_vals[..elem_width].to_vec();
                        for i in 1..elems.len() {
                            let eq = self.fresh_var("t");
                            self.instructions.push(CircuitInstr::TestEq {
                                a: idx_val.clone(),
                                b: CircuitVal::Imm(i as i128),
                                output: eq,
                            });
                            let elem_slice =
                                base_vals[i * elem_width..(i + 1) * elem_width].to_vec();
                            acc = self.select_wires(&CircuitVal::Var(eq), elem_slice, acc);
                        }
                        acc
                    }
                    Type::Bytes(len) => {
                        let byte_wires = self.unpack_bytes_wires(&base_vals, *len);
                        if let Some(k) = eval_const_u128(index) {
                            return vec![byte_wires[k as usize].clone()];
                        }
                        let idx_val = self
                            .lower_expr(index, param_vals, locals, guard)
                            .into_iter()
                            .next()
                            .unwrap_or(CircuitVal::Imm(0));
                        let mut acc = vec![byte_wires[0].clone()];
                        for (i, bw) in byte_wires.into_iter().enumerate().skip(1) {
                            let eq = self.fresh_var("t");
                            self.instructions.push(CircuitInstr::TestEq {
                                a: idx_val.clone(),
                                b: CircuitVal::Imm(i as i128),
                                output: eq,
                            });
                            acc = self.select_wires(&CircuitVal::Var(eq), vec![bw], acc);
                        }
                        acc
                    }
                    _ => unreachable!("sema validated Index on Vector, Bytes, or Tuple"),
                }
            }
            ExprKind::Slice { base, start, len } => {
                let base_vals = self.lower_expr(base, param_vals, locals, guard);
                match self.program.underlying_type(&base.ty) {
                    Type::Vector(_, elem_ty) => {
                        let elem_width = wire_count(self.program, elem_ty);
                        let off = (*start as usize) * elem_width;
                        let width = (*len as usize) * elem_width;
                        base_vals[off..off + width].to_vec()
                    }
                    Type::Tuple(elems) => {
                        let mut offset = 0usize;
                        let mut out = Vec::new();
                        for (i, ety) in elems.iter().enumerate() {
                            let w = wire_count(self.program, ety);
                            if i >= (*start as usize) && i < ((*start + *len) as usize) {
                                out.extend_from_slice(&base_vals[offset..offset + w]);
                            }
                            offset += w;
                        }
                        out
                    }
                    Type::Bytes(blen) => {
                        if *len == 0 {
                            return Vec::new();
                        }
                        if *start == 0 && *len == *blen {
                            return base_vals;
                        }
                        if *blen <= FIELD_BYTES && *start + *len <= FIELD_BYTES {
                            // Extract bytes `[start .. start + len]` within the single 31-byte chunk
                            // using `div_mod_power_of_two` on the packed little-endian scalar wire.
                            let mut wire = base_vals.last().cloned().unwrap_or(CircuitVal::Imm(0));
                            if *start > 0 {
                                let q = self.fresh_var("quo");
                                let rem = self.fresh_var("rem");
                                self.instructions.push(CircuitInstr::DivModPowerOfTwo {
                                    val: wire,
                                    bits: *start * 8,
                                    quotient: q,
                                    remainder: rem,
                                });
                                wire = CircuitVal::Var(q);
                            }
                            if *start + *len < *blen {
                                let q = self.fresh_var("quo");
                                let rem = self.fresh_var("rem");
                                self.instructions.push(CircuitInstr::DivModPowerOfTwo {
                                    val: wire,
                                    bits: *len * 8,
                                    quotient: q,
                                    remainder: rem,
                                });
                                wire = CircuitVal::Var(rem);
                            }
                            vec![wire]
                        } else {
                            // General multi-chunk `Bytes` slice using ZKIR v3.1 `Slice`.
                            let mut rev_in = base_vals;
                            rev_in.reverse();
                            let b_in = self.fresh_var("bytes");
                            self.instructions.push(CircuitInstr::BytesFromNatives {
                                inputs: rev_in,
                                len: *blen,
                                output: b_in,
                            });
                            let b_out = self.fresh_var("bytes");
                            self.instructions.push(CircuitInstr::Slice {
                                bytes: b_in,
                                start: *start,
                                len: *len,
                                output: b_out,
                            });
                            let out_count = (*len).div_ceil(FIELD_BYTES) as usize;
                            let mut out_vars = Vec::with_capacity(out_count);
                            for _ in 0..out_count {
                                out_vars.push(self.fresh_var("t"));
                            }
                            self.instructions.push(CircuitInstr::BytesIntoNatives {
                                bytes: b_out,
                                outputs: out_vars.clone(),
                            });
                            out_vars.reverse();
                            out_vars.into_iter().map(CircuitVal::Var).collect()
                        }
                    }
                    _ => unreachable!("sema validated Slice target"),
                }
            }
            ExprKind::MaybeSome(inner) => {
                let mut out = vec![CircuitVal::TRUE];
                out.extend(self.lower_expr(inner, param_vals, locals, guard));
                out
            }
            ExprKind::MaybeNone(inner_ty) => {
                let mut out = vec![CircuitVal::FALSE];
                out.extend(self.lower_default(inner_ty));
                out
            }
            ExprKind::Disclose(inner) => {
                self.lower_expr_with_hint(inner, param_vals, locals, guard, hint)
            }
            ExprKind::Cast {
                expr: inner,
                target,
            } => {
                let src_u = self.program.underlying_type(&inner.ty).clone();
                let dst_u = self.program.underlying_type(target).clone();
                match (&src_u, &dst_u) {
                    (Type::Bytes(n), Type::Vector(_, _) | Type::Tuple(_)) => {
                        let wires = self.lower_expr(inner, param_vals, locals, guard);
                        self.unpack_bytes_wires(&wires, *n)
                    }
                    (Type::Vector(_, _) | Type::Tuple(_), Type::Bytes(_)) => {
                        let byte_vals = self.lower_expr(inner, param_vals, locals, guard);
                        self.pack_bytes_wires(&byte_vals)
                    }
                    (Type::Field | Type::Uint(_), Type::Boolean) => {
                        let val = self
                            .lower_expr(inner, param_vals, locals, guard)
                            .into_iter()
                            .next()
                            .unwrap_or(CircuitVal::Imm(0));
                        let is_zero = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::TestEq {
                            a: val,
                            b: CircuitVal::Imm(0),
                            output: is_zero,
                        });
                        let out = self.fresh_var(hint.unwrap_or("t"));
                        self.instructions.push(CircuitInstr::CondSelect {
                            bit: CircuitVal::Var(is_zero),
                            a: CircuitVal::Imm(0),
                            b: CircuitVal::Imm(1),
                            output: out,
                        });
                        vec![CircuitVal::Var(out)]
                    }
                    (Type::Uint(_), Type::Bytes(n)) => {
                        let val = self
                            .lower_expr(inner, param_vals, locals, guard)
                            .into_iter()
                            .next()
                            .unwrap_or(CircuitVal::Imm(0));
                        if *n == 0 {
                            Vec::new()
                        } else if *n <= FIELD_BYTES {
                            let out = self.fresh_var(hint.unwrap_or("t"));
                            self.instructions
                                .push(CircuitInstr::Copy { val, output: out });
                            self.instructions.push(CircuitInstr::ConstrainBits {
                                val: CircuitVal::Var(out),
                                bits: *n * 8,
                            });
                            vec![CircuitVal::Var(out)]
                        } else {
                            let total_wires = (*n as usize).div_ceil(FIELD_BYTES as usize);
                            let hi = self.fresh_var("hi");
                            let lo = self.fresh_var("lo");
                            self.instructions.push(CircuitInstr::DivModPowerOfTwo {
                                val,
                                bits: FIELD_BYTES * 8,
                                quotient: hi,
                                remainder: lo,
                            });
                            let mut out = vec![CircuitVal::Imm(0); total_wires];
                            out[total_wires - 2] = CircuitVal::Var(hi);
                            out[total_wires - 1] = CircuitVal::Var(lo);
                            out
                        }
                    }
                    (Type::Bytes(n), Type::Uint(bits)) => {
                        let wires = self.lower_expr(inner, param_vals, locals, guard);
                        let val = if *n == 0 {
                            CircuitVal::Imm(0)
                        } else {
                            wires.into_iter().last().unwrap_or(CircuitVal::Imm(0))
                        };
                        let out = self.fresh_var(hint.unwrap_or("t"));
                        self.instructions
                            .push(CircuitInstr::Copy { val, output: out });
                        self.instructions.push(CircuitInstr::ConstrainBits {
                            val: CircuitVal::Var(out),
                            bits: *bits,
                        });
                        vec![CircuitVal::Var(out)]
                    }
                    (
                        Type::Field | Type::Uint(_) | Type::Boolean | Type::Enum(_),
                        Type::CurveField(CurveFieldKind::JubjubScalar),
                    ) => {
                        let val = self
                            .lower_expr(inner, param_vals, locals, guard)
                            .into_iter()
                            .next()
                            .unwrap_or(CircuitVal::Imm(0));
                        let out = self.fresh_var(hint.unwrap_or("t"));
                        self.instructions
                            .push(CircuitInstr::JubjubScalarFromNative {
                                native: val,
                                output: out,
                            });
                        vec![CircuitVal::Var(out)]
                    }
                    (
                        Type::CurveField(CurveFieldKind::JubjubScalar),
                        Type::Field | Type::Uint(_),
                    ) => {
                        let val = self
                            .lower_expr(inner, param_vals, locals, guard)
                            .into_iter()
                            .next()
                            .unwrap_or(CircuitVal::Imm(0));
                        let out = self.fresh_var(hint.unwrap_or("t"));
                        self.instructions.push(CircuitInstr::Encode {
                            input: val,
                            outputs: vec![out],
                        });
                        if let Type::Uint(bits) = dst_u {
                            self.instructions.push(CircuitInstr::ConstrainBits {
                                val: CircuitVal::Var(out),
                                bits,
                            });
                        }
                        vec![CircuitVal::Var(out)]
                    }
                    (Type::Field, Type::Uint(bits)) => {
                        let val = self
                            .lower_expr(inner, param_vals, locals, guard)
                            .into_iter()
                            .next()
                            .unwrap_or(CircuitVal::Imm(0));
                        let out = self.fresh_var(hint.unwrap_or("t"));
                        self.instructions
                            .push(CircuitInstr::Copy { val, output: out });
                        self.instructions.push(CircuitInstr::ConstrainBits {
                            val: CircuitVal::Var(out),
                            bits: *bits,
                        });
                        vec![CircuitVal::Var(out)]
                    }
                    (Type::Field, Type::Bytes(n)) => {
                        let val = self
                            .lower_expr(inner, param_vals, locals, guard)
                            .into_iter()
                            .next()
                            .unwrap_or(CircuitVal::Imm(0));
                        if *n == 0 {
                            Vec::new()
                        } else if *n <= FIELD_BYTES {
                            let out = self.fresh_var(hint.unwrap_or("t"));
                            self.instructions
                                .push(CircuitInstr::Copy { val, output: out });
                            self.instructions.push(CircuitInstr::ConstrainBits {
                                val: CircuitVal::Var(out),
                                bits: *n * 8,
                            });
                            vec![CircuitVal::Var(out)]
                        } else {
                            let hi = self.fresh_var("hi");
                            let lo = self.fresh_var("lo");
                            self.instructions.push(CircuitInstr::DivModPowerOfTwo {
                                val,
                                bits: FIELD_BYTES * 8,
                                quotient: hi,
                                remainder: lo,
                            });
                            vec![CircuitVal::Var(hi), CircuitVal::Var(lo)]
                        }
                    }
                    (Type::CurveField(_), Type::Bytes(32)) => {
                        let val = self
                            .lower_expr(inner, param_vals, locals, guard)
                            .into_iter()
                            .next()
                            .unwrap_or(CircuitVal::Imm(0));
                        let tmp = self.fresh_var("bytes");
                        self.instructions.push(CircuitInstr::ToBytes {
                            input: val,
                            output: tmp,
                        });
                        let lo = self.fresh_var(hint.unwrap_or("t"));
                        let hi = self.fresh_var(hint.unwrap_or("t"));
                        self.instructions.push(CircuitInstr::BytesIntoNatives {
                            bytes: tmp,
                            outputs: vec![lo, hi],
                        });
                        vec![CircuitVal::Var(hi), CircuitVal::Var(lo)]
                    }
                    (Type::Bytes(n), Type::CurveField(field)) => {
                        let mut wires = self.lower_expr(inner, param_vals, locals, guard);
                        wires.reverse();
                        let tmp = self.fresh_var("bytes");
                        self.instructions.push(CircuitInstr::BytesFromNatives {
                            inputs: wires,
                            len: *n,
                            output: tmp,
                        });
                        let out = self.fresh_var(hint.unwrap_or("t"));
                        self.instructions.push(CircuitInstr::FromBytes {
                            bytes: tmp,
                            val_t: WireType::from_field(*field),
                            output: out,
                        });
                        vec![CircuitVal::Var(out)]
                    }
                    _ => self.lower_expr_with_hint(inner, param_vals, locals, guard, hint),
                }
            }
            ExprKind::BytesPack(elems) => {
                let mut byte_vals = Vec::with_capacity(elems.len());
                for e in elems {
                    let vals = self.lower_expr(e, param_vals, locals, guard);
                    byte_vals.push(vals.into_iter().next().unwrap_or(CircuitVal::Imm(0)));
                }
                self.pack_bytes_wires(&byte_vals)
            }
            ExprKind::Block { stmts, tail } => {
                let mut block_locals = locals.clone();
                let _ = self.lower_stmts(stmts, param_vals, &mut block_locals, guard);
                self.lower_expr_with_hint(tail, param_vals, &block_locals, guard, hint)
            }
            ExprKind::Unary { op, operand } => {
                let vals = self.lower_expr(operand, param_vals, locals, guard);
                let val = vals.into_iter().next().unwrap_or(CircuitVal::FALSE);
                match op {
                    UnaryOp::Not => vec![self.emit_not(&val)],
                    UnaryOp::Neg => {
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::Neg {
                            a: val,
                            output: out,
                        });
                        vec![CircuitVal::Var(out)]
                    }
                }
            }
            ExprKind::Binary { op, lhs, rhs } => {
                if matches!(op, BinaryOp::And | BinaryOp::Or) {
                    let av = self
                        .lower_expr(lhs, param_vals, locals, guard)
                        .into_iter()
                        .next()
                        .unwrap_or(CircuitVal::FALSE);
                    if *op == BinaryOp::And {
                        let rhs_guard = self.combine_guard(guard, &av);
                        let bv = self
                            .lower_expr(rhs, param_vals, locals, &rhs_guard)
                            .into_iter()
                            .next()
                            .unwrap_or(CircuitVal::FALSE);
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::CondSelect {
                            bit: av,
                            a: bv,
                            b: CircuitVal::FALSE,
                            output: out,
                        });
                        return vec![CircuitVal::Var(out)];
                    } else {
                        let not_a = self.emit_not(&av);
                        let rhs_guard = self.combine_guard(guard, &not_a);
                        let bv = self
                            .lower_expr(rhs, param_vals, locals, &rhs_guard)
                            .into_iter()
                            .next()
                            .unwrap_or(CircuitVal::FALSE);
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::CondSelect {
                            bit: av,
                            a: CircuitVal::TRUE,
                            b: bv,
                            output: out,
                        });
                        return vec![CircuitVal::Var(out)];
                    }
                }
                let lvals = self.lower_expr(lhs, param_vals, locals, guard);
                let rvals = self.lower_expr(rhs, param_vals, locals, guard);
                match op {
                    BinaryOp::Eq | BinaryOp::Neq => {
                        debug_assert_eq!(lvals.len(), rvals.len());
                        let mut eq_vars = Vec::with_capacity(lvals.len());
                        for (a, b) in lvals.into_iter().zip(rvals) {
                            let eq = self.fresh_var("t");
                            self.instructions
                                .push(CircuitInstr::TestEq { a, b, output: eq });
                            eq_vars.push(CircuitVal::Var(eq));
                        }
                        let mut acc = eq_vars
                            .into_iter()
                            .reduce(|acc, next| {
                                let combined = self.fresh_var("t");
                                self.instructions.push(CircuitInstr::CondSelect {
                                    bit: acc,
                                    a: next,
                                    b: CircuitVal::FALSE,
                                    output: combined,
                                });
                                CircuitVal::Var(combined)
                            })
                            .unwrap_or(CircuitVal::TRUE);
                        if *op == BinaryOp::Neq {
                            acc = self.emit_not(&acc);
                        }
                        vec![acc]
                    }
                    BinaryOp::Add => {
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::Add {
                            a: lvals[0].clone(),
                            b: rvals[0].clone(),
                            output: out,
                        });
                        vec![CircuitVal::Var(out)]
                    }
                    BinaryOp::Sub => {
                        let neg = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::Neg {
                            a: rvals[0].clone(),
                            output: neg,
                        });
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::Add {
                            a: lvals[0].clone(),
                            b: CircuitVal::Var(neg),
                            output: out,
                        });
                        vec![CircuitVal::Var(out)]
                    }
                    BinaryOp::Mul => {
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::Mul {
                            a: lvals[0].clone(),
                            b: rvals[0].clone(),
                            output: out,
                        });
                        vec![CircuitVal::Var(out)]
                    }
                    BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge => {
                        let max_bits = match (&lhs.ty, &rhs.ty) {
                            (Type::Uint(a), Type::Uint(b)) => (*a).max(*b),
                            (Type::Uint(a), _) | (_, Type::Uint(a)) => *a,
                            _ => 248,
                        };
                        let bits = (2 * max_bits.div_ceil(2)).max(2);
                        let (a, b, invert) = match op {
                            BinaryOp::Lt => (lvals[0].clone(), rvals[0].clone(), false),
                            BinaryOp::Gt => (rvals[0].clone(), lvals[0].clone(), false),
                            BinaryOp::Le => (rvals[0].clone(), lvals[0].clone(), true),
                            BinaryOp::Ge => (lvals[0].clone(), rvals[0].clone(), true),
                            _ => unreachable!(),
                        };
                        let lt = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::LessThan {
                            a,
                            b,
                            bits,
                            output: lt,
                        });
                        let res = if invert {
                            self.emit_not(&CircuitVal::Var(lt))
                        } else {
                            CircuitVal::Var(lt)
                        };
                        vec![res]
                    }
                    BinaryOp::And | BinaryOp::Or => unreachable!(),
                }
            }
            ExprKind::Ternary {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond_val = self
                    .lower_expr(cond, param_vals, locals, guard)
                    .into_iter()
                    .next()
                    .unwrap_or(CircuitVal::FALSE);
                let then_guard = if expr_has_effects(then_branch, self.program) {
                    self.combine_guard(guard, &cond_val)
                } else {
                    guard.clone()
                };
                let then_vals = self.lower_expr(then_branch, param_vals, locals, &then_guard);

                let else_guard = if expr_has_effects(else_branch, self.program) {
                    let not_cond = self.emit_not(&cond_val);
                    self.combine_guard(guard, &not_cond)
                } else {
                    guard.clone()
                };
                let else_vals = self.lower_expr(else_branch, param_vals, locals, &else_guard);

                self.select_wires(&cond_val, then_vals, else_vals)
            }
            ExprKind::Assert { cond, .. } => {
                let cond_val = self
                    .lower_expr(cond, param_vals, locals, guard)
                    .into_iter()
                    .next()
                    .unwrap_or(CircuitVal::FALSE);
                if guard.is_const_true() {
                    self.instructions
                        .push(CircuitInstr::Assert { cond: cond_val });
                } else {
                    let guarded = self.fresh_var("t");
                    self.instructions.push(CircuitInstr::CondSelect {
                        bit: guard.clone(),
                        a: cond_val,
                        b: CircuitVal::TRUE,
                        output: guarded,
                    });
                    self.instructions.push(CircuitInstr::Assert {
                        cond: CircuitVal::Var(guarded),
                    });
                }
                Vec::new()
            }
            ExprKind::WitnessCall { witness, args } => {
                for a in args {
                    let _ = self.lower_expr(a, param_vals, locals, guard);
                }
                let w = self.program.witness(*witness);
                let var_hint = hint.unwrap_or("t");
                let pi_guard = if guard.is_const_true() {
                    None
                } else {
                    Some(guard.clone())
                };
                let wtypes = wire_types(self.program, &w.ret_type);
                let constraints = wire_constraints(self.program, &w.ret_type);
                let mut out = Vec::with_capacity(constraints.len());
                for (wt, c) in wtypes.into_iter().zip(constraints) {
                    let v = self.fresh_var(var_hint);
                    self.instructions.push(CircuitInstr::PrivateInput {
                        guard: pi_guard.clone(),
                        val_t: wt,
                        output: v,
                    });
                    self.emit_wire_constraint(v, c);
                    out.push(CircuitVal::Var(v));
                }
                out
            }
            ExprKind::NativeWitness { kind, args } => {
                for a in args {
                    let _ = self.lower_expr(a, param_vals, locals, guard);
                }
                match kind {
                    NativeWitnessKind::OwnPublicKey => {
                        let var_hint = hint.unwrap_or("pk");
                        let pi_guard = if guard.is_const_true() {
                            None
                        } else {
                            Some(guard.clone())
                        };
                        let wtypes = wire_types(self.program, &expr.ty);
                        let constraints = wire_constraints(self.program, &expr.ty);
                        let mut out = Vec::with_capacity(constraints.len());
                        for (wt, c) in wtypes.into_iter().zip(constraints) {
                            let v = self.fresh_var(var_hint);
                            self.instructions.push(CircuitInstr::PrivateInput {
                                guard: pi_guard.clone(),
                                val_t: wt,
                                output: v,
                            });
                            self.emit_wire_constraint(v, c);
                            out.push(CircuitVal::Var(v));
                        }
                        out
                    }
                    NativeWitnessKind::CreateZswapInput | NativeWitnessKind::CreateZswapOutput => {
                        Vec::new()
                    }
                }
            }
            ExprKind::PersistentHash { input_ty, arg } => {
                let raw_inputs = self.lower_expr(arg, param_vals, locals, guard);
                let inputs = self.encode_to_native_wires(input_ty, raw_inputs);
                let alignment = AlignmentAtom::alignment_of(self.program, input_ty);
                let bytes_var = self.fresh_var("bytes");
                self.instructions.push(CircuitInstr::PersistentHash {
                    alignment,
                    inputs,
                    output: bytes_var,
                });
                // ZKIR `bytes_into_natives` outputs `[lo (248-bit), hi (8-bit)]`;
                // Compact's flattened `Bytes<32>` wire order is `[hi, lo]`.
                let out_hint = hint.unwrap_or("hash");
                let lo = self.fresh_var(out_hint);
                let hi = self.fresh_var(out_hint);
                self.instructions.push(CircuitInstr::BytesIntoNatives {
                    bytes: bytes_var,
                    outputs: vec![lo, hi],
                });
                vec![CircuitVal::Var(hi), CircuitVal::Var(lo)]
            }
            ExprKind::Keccak256 { input_ty, arg } => {
                let raw_inputs = self.lower_expr(arg, param_vals, locals, guard);
                let inputs = self.encode_to_native_wires(input_ty, raw_inputs);
                let alignment = AlignmentAtom::alignment_of(self.program, input_ty);
                let bytes_var = self.fresh_var("bytes");
                self.instructions.push(CircuitInstr::Keccak256 {
                    alignment,
                    inputs,
                    output: bytes_var,
                });
                let out_hint = hint.unwrap_or("hash");
                let lo = self.fresh_var(out_hint);
                let hi = self.fresh_var(out_hint);
                self.instructions.push(CircuitInstr::BytesIntoNatives {
                    bytes: bytes_var,
                    outputs: vec![lo, hi],
                });
                vec![CircuitVal::Var(hi), CircuitVal::Var(lo)]
            }
            ExprKind::Sha512 { input_ty, arg } => {
                let raw_inputs = self.lower_expr(arg, param_vals, locals, guard);
                let inputs = self.encode_to_native_wires(input_ty, raw_inputs);
                let alignment = AlignmentAtom::alignment_of(self.program, input_ty);
                let bytes_var = self.fresh_var("bytes");
                self.instructions.push(CircuitInstr::Sha512 {
                    alignment,
                    inputs,
                    output: bytes_var,
                });
                let out_hint = hint.unwrap_or("hash");
                let w0 = self.fresh_var(out_hint);
                let w1 = self.fresh_var(out_hint);
                let w2 = self.fresh_var(out_hint);
                self.instructions.push(CircuitInstr::BytesIntoNatives {
                    bytes: bytes_var,
                    outputs: vec![w0, w1, w2],
                });
                vec![
                    CircuitVal::Var(w2),
                    CircuitVal::Var(w1),
                    CircuitVal::Var(w0),
                ]
            }
            ExprKind::TransientHash { input_ty, arg } => {
                let raw_inputs = self.lower_expr(arg, param_vals, locals, guard);
                let inputs = self.encode_to_native_wires(input_ty, raw_inputs);
                let out = self.fresh_var(hint.unwrap_or("hash"));
                self.instructions.push(CircuitInstr::TransientHash {
                    inputs,
                    output: out,
                });
                vec![CircuitVal::Var(out)]
            }
            ExprKind::PersistentCommit {
                input_ty,
                value,
                rand,
            } => {
                // Upstream swaps `(value, rand)` so `rand` (`Bytes<32>`) comes first in `persistent_hash`.
                let raw_val_wires = self.lower_expr(value, param_vals, locals, guard);
                let val_wires = self.encode_to_native_wires(input_ty, raw_val_wires);
                let rand_wires = self.lower_expr(rand, param_vals, locals, guard);
                let mut alignment = vec![AlignmentAtom::Bytes(32)];
                alignment.extend(AlignmentAtom::alignment_of(self.program, input_ty));
                let mut inputs = rand_wires;
                inputs.extend(val_wires);
                let bytes_var = self.fresh_var("bytes");
                self.instructions.push(CircuitInstr::PersistentHash {
                    alignment,
                    inputs,
                    output: bytes_var,
                });
                let out_hint = hint.unwrap_or("commit");
                let lo = self.fresh_var(out_hint);
                let hi = self.fresh_var(out_hint);
                self.instructions.push(CircuitInstr::BytesIntoNatives {
                    bytes: bytes_var,
                    outputs: vec![lo, hi],
                });
                vec![CircuitVal::Var(hi), CircuitVal::Var(lo)]
            }
            ExprKind::TransientCommit {
                input_ty,
                value,
                rand,
            } => {
                // Upstream moves `rand` (`Field`) first before `value` wires in `transient_hash`.
                let raw_val_wires = self.lower_expr(value, param_vals, locals, guard);
                let val_wires = self.encode_to_native_wires(input_ty, raw_val_wires);
                let rand_wires = self.lower_expr(rand, param_vals, locals, guard);
                let mut inputs = rand_wires;
                inputs.extend(val_wires);
                let out = self.fresh_var(hint.unwrap_or("commit"));
                self.instructions.push(CircuitInstr::TransientHash {
                    inputs,
                    output: out,
                });
                vec![CircuitVal::Var(out)]
            }
            ExprKind::FieldInv(inner) => {
                let val = self
                    .lower_expr(inner, param_vals, locals, guard)
                    .into_iter()
                    .next()
                    .unwrap_or(CircuitVal::Imm(0));
                let out = self.fresh_var(hint.unwrap_or("inv"));
                self.instructions.push(CircuitInstr::Inv {
                    a: val,
                    output: out,
                });
                vec![CircuitVal::Var(out)]
            }
            ExprKind::EcAdd { lhs, rhs } => {
                let a = self
                    .lower_expr(lhs, param_vals, locals, guard)
                    .into_iter()
                    .next()
                    .unwrap_or(CircuitVal::Imm(0));
                let b = self
                    .lower_expr(rhs, param_vals, locals, guard)
                    .into_iter()
                    .next()
                    .unwrap_or(CircuitVal::Imm(0));
                let out = self.fresh_var(hint.unwrap_or("pt"));
                self.instructions
                    .push(CircuitInstr::Add { a, b, output: out });
                vec![CircuitVal::Var(out)]
            }
            ExprKind::EcNeg(inner) => {
                let pt = self
                    .lower_expr(inner, param_vals, locals, guard)
                    .into_iter()
                    .next()
                    .unwrap_or(CircuitVal::Imm(0));
                let x = self.fresh_var("x");
                let y = self.fresh_var("y");
                self.instructions
                    .push(CircuitInstr::IntoCoordinates { point: pt, x, y });
                let neg_x = self.fresh_var("neg");
                self.instructions.push(CircuitInstr::Neg {
                    a: CircuitVal::Var(x),
                    output: neg_x,
                });
                let out = self.fresh_var(hint.unwrap_or("pt"));
                self.instructions.push(CircuitInstr::FromCoordinates {
                    x: CircuitVal::Var(neg_x),
                    y: CircuitVal::Var(y),
                    output: out,
                });
                vec![CircuitVal::Var(out)]
            }
            ExprKind::EcMul { point, scalar } => {
                let pt = self
                    .lower_expr(point, param_vals, locals, guard)
                    .into_iter()
                    .next()
                    .unwrap_or(CircuitVal::Imm(0));
                let sc = self
                    .lower_expr(scalar, param_vals, locals, guard)
                    .into_iter()
                    .next()
                    .unwrap_or(CircuitVal::Imm(0));
                let out = self.fresh_var(hint.unwrap_or("pt"));
                self.instructions.push(CircuitInstr::EcMul {
                    a: pt,
                    scalar: sc,
                    output: out,
                });
                vec![CircuitVal::Var(out)]
            }
            ExprKind::EcMulGenerator(scalar) => {
                let sc = self
                    .lower_expr(scalar, param_vals, locals, guard)
                    .into_iter()
                    .next()
                    .unwrap_or(CircuitVal::Imm(0));
                let out = self.fresh_var(hint.unwrap_or("pt"));
                self.instructions.push(CircuitInstr::EcMulGenerator {
                    scalar: sc,
                    output: out,
                });
                vec![CircuitVal::Var(out)]
            }
            ExprKind::HashToCurve { input_ty, arg } => {
                let raw_inputs = self.lower_expr(arg, param_vals, locals, guard);
                let inputs = self.encode_to_native_wires(input_ty, raw_inputs);
                let out = self.fresh_var(hint.unwrap_or("pt"));
                self.instructions.push(CircuitInstr::HashToCurve {
                    inputs,
                    output: out,
                });
                vec![CircuitVal::Var(out)]
            }
            ExprKind::ConstructJubjubPoint { x, y } => {
                let xv = self
                    .lower_expr(x, param_vals, locals, guard)
                    .into_iter()
                    .next()
                    .unwrap_or(CircuitVal::Imm(0));
                let yv = self
                    .lower_expr(y, param_vals, locals, guard)
                    .into_iter()
                    .next()
                    .unwrap_or(CircuitVal::Imm(0));
                let out = self.fresh_var(hint.unwrap_or("pt"));
                self.instructions.push(CircuitInstr::FromCoordinates {
                    x: xv,
                    y: yv,
                    output: out,
                });
                vec![CircuitVal::Var(out)]
            }
            ExprKind::PointCoord { point, is_y } => {
                let pt = self
                    .lower_expr(point, param_vals, locals, guard)
                    .into_iter()
                    .next()
                    .unwrap_or(CircuitVal::Imm(0));
                let x = self.fresh_var(if *is_y { "ignore" } else { hint.unwrap_or("x") });
                let y = self.fresh_var(if *is_y { hint.unwrap_or("y") } else { "ignore" });
                self.instructions
                    .push(CircuitInstr::IntoCoordinates { point: pt, x, y });
                vec![CircuitVal::Var(if *is_y { y } else { x })]
            }
            ExprKind::DegradeToTransient(inner) => {
                let wires = self.lower_expr(inner, param_vals, locals, guard);
                let lo = wires.get(1).cloned().unwrap_or(CircuitVal::Imm(0));
                let out = self.fresh_var(hint.unwrap_or("t"));
                self.instructions.push(CircuitInstr::Copy {
                    val: lo,
                    output: out,
                });
                vec![CircuitVal::Var(out)]
            }
            ExprKind::UpgradeFromTransient(inner) => {
                let x = self
                    .lower_expr(inner, param_vals, locals, guard)
                    .into_iter()
                    .next()
                    .unwrap_or(CircuitVal::Imm(0));
                let tmp = self.fresh_var("tmp");
                let lo = self.fresh_var(hint.unwrap_or("t"));
                self.instructions.push(CircuitInstr::DivModPowerOfTwo {
                    val: x,
                    bits: 248,
                    quotient: tmp,
                    remainder: lo,
                });
                let hi = self.fresh_var(hint.unwrap_or("t"));
                self.instructions.push(CircuitInstr::Copy {
                    val: CircuitVal::Imm(0),
                    output: hi,
                });
                vec![CircuitVal::Var(hi), CircuitVal::Var(lo)]
            }
            ExprKind::MerkleTreePathRoot {
                depth,
                leaf_ty,
                path,
            } => {
                let path_vals = self.lower_expr(path, param_vals, locals, guard);
                let leaf_width = wire_count(self.program, leaf_ty);
                let leaf_vals = &path_vals[..leaf_width];

                // Leaf preimage hash: `persistentHash(LeafPreimage { domain_sep: "mdn:lh", data: path.leaf })`
                let mut alignment = vec![AlignmentAtom::Bytes(6)];
                alignment.extend(AlignmentAtom::alignment_of(self.program, leaf_ty));
                let encoded_leaf = self.encode_to_native_wires(leaf_ty, leaf_vals.to_vec());
                let mut hash_inputs = bytes_to_wires(b"mdn:lh");
                hash_inputs.extend(encoded_leaf);

                let bytes_var = self.fresh_var("bytes");
                self.instructions.push(CircuitInstr::PersistentHash {
                    alignment,
                    inputs: hash_inputs,
                    output: bytes_var,
                });
                let lo = self.fresh_var("t");
                let hi = self.fresh_var("t");
                self.instructions.push(CircuitInstr::BytesIntoNatives {
                    bytes: bytes_var,
                    outputs: vec![lo, hi],
                });
                // `degradeToTransient` projects the low 248-bit native field wire.
                let degraded = self.fresh_var("t");
                self.instructions.push(CircuitInstr::Copy {
                    val: CircuitVal::Var(lo),
                    output: degraded,
                });

                let mut acc = CircuitVal::Var(degraded);
                for level in 0..(*depth as usize) {
                    let base = leaf_width + level * 2;
                    let sibling = path_vals[base].clone();
                    let goes_left = path_vals[base + 1].clone();

                    let left = self.fresh_var("left");
                    self.instructions.push(CircuitInstr::CondSelect {
                        bit: goes_left.clone(),
                        a: acc.clone(),
                        b: sibling.clone(),
                        output: left,
                    });
                    let right = self.fresh_var("right");
                    self.instructions.push(CircuitInstr::CondSelect {
                        bit: goes_left,
                        a: sibling,
                        b: acc,
                        output: right,
                    });
                    let next = self.fresh_var(if level + 1 == *depth as usize {
                        "t"
                    } else {
                        "recursiveDigest"
                    });
                    self.instructions.push(CircuitInstr::TransientHash {
                        inputs: vec![CircuitVal::Var(left), CircuitVal::Var(right)],
                        output: next,
                    });
                    acc = CircuitVal::Var(next);
                }
                vec![acc]
            }
            ExprKind::CircuitCall { circuit, args } => {
                let lowered_args: Vec<Vec<CircuitVal>> = args
                    .iter()
                    .map(|a| self.lower_expr(a, param_vals, locals, guard))
                    .collect();
                let callee = self.program.circuit(*circuit);
                self.lower_circuit_body(callee, &lowered_args, guard)
            }
            ExprKind::ContractCall {
                contract,
                receiver,
                method,
                args,
            } => {
                let recv_vals = self.lower_expr(receiver, param_vals, locals, guard);
                let mut encoded_args = Vec::new();
                for a in args {
                    let raw = self.lower_expr(a, param_vals, locals, guard);
                    encoded_args.extend(self.encode_to_native_wires(&a.ty, raw));
                }
                let sig = self
                    .program
                    .contract_decl(*contract)
                    .circuits
                    .iter()
                    .find(|c| c.name == *method)
                    .expect("sema validated contract method");
                let ret_ty = sig.ret_type.clone();
                let pi_guard = if guard.is_const_true() {
                    None
                } else {
                    Some(guard.clone())
                };
                let ret_wtypes = wire_types(self.program, &ret_ty);
                let ret_constraints = wire_constraints(self.program, &ret_ty);
                let mut ret_vals = Vec::with_capacity(ret_wtypes.len());
                for (wt, c) in ret_wtypes.into_iter().zip(ret_constraints) {
                    let v = self.fresh_var(hint.unwrap_or("cc"));
                    self.instructions.push(CircuitInstr::PrivateInput {
                        guard: pi_guard.clone(),
                        val_t: wt,
                        output: v,
                    });
                    self.emit_wire_constraint(v, c);
                    ret_vals.push(CircuitVal::Var(v));
                }
                let cc_rand = self.fresh_var("cc_rand");
                self.instructions.push(CircuitInstr::PrivateInput {
                    guard: pi_guard,
                    val_t: WireType::Native,
                    output: cc_rand,
                });
                let encoded_ret = self.encode_to_native_wires(&ret_ty, ret_vals.clone());
                let mut commit_inputs = vec![CircuitVal::Var(cc_rand)];
                commit_inputs.extend(encoded_args);
                commit_inputs.extend(encoded_ret);
                let comm = self.fresh_var("comm");
                self.instructions.push(CircuitInstr::TransientHash {
                    inputs: commit_inputs,
                    output: comm,
                });
                let ep_vals = bytes_to_wires(&entry_point_hash(method));
                self.emit_kernel_claim_contract_call(
                    recv_vals,
                    ep_vals,
                    vec![CircuitVal::Var(comm)],
                    guard,
                );
                ret_vals
            }
            ExprKind::Emit {
                event_tag,
                payload_len,
                event_ty,
                value,
                ..
            } => {
                let raw_vals = self.lower_expr(value, param_vals, locals, guard);
                let payload_wires = self.lower_serialize_wires(event_ty, &raw_vals, *payload_len);
                self.emit_impact(
                    guard,
                    ImpactVmOp::Push {
                        storage: false,
                        value: ImpactStateValue::Array(vec![
                            ImpactStateValue::cell_u32(1),
                            ImpactStateValue::cell_u8(*event_tag),
                            ImpactStateValue::Cell {
                                alignment: vec![AlignmentAtom::Bytes(*payload_len)],
                                values: payload_wires,
                            },
                        ]),
                    },
                );
                self.emit_impact(guard, ImpactVmOp::Log);
                Vec::new()
            }
            ExprKind::Serialize {
                len,
                input_ty,
                value,
            } => {
                let raw_vals = self.lower_expr(value, param_vals, locals, guard);
                self.lower_serialize_wires(input_ty, &raw_vals, *len)
            }
            ExprKind::Deserialize {
                len,
                target_ty,
                bytes,
            } => {
                let raw_bytes = self.lower_expr(bytes, param_vals, locals, guard);
                let byte_vals = self.unpack_bytes_wires(&raw_bytes, *len);
                let mut offset = 0usize;
                self.lower_deserialize_from_bytes(target_ty, &byte_vals, &mut offset)
            }
            ExprKind::LedgerCall {
                field,
                key_path,
                target_adt,
                op,
                args,
            } => {
                let ledger_field = self.program.ledger_field(*field);
                let mut full_path: Vec<PathSegment> = ledger_field
                    .path
                    .iter()
                    .map(|&s| PathSegment::Static(s))
                    .collect();
                for key_expr in key_path {
                    let raw_vals = self.lower_expr(key_expr, param_vals, locals, guard);
                    let vals = self.encode_to_native_wires(&key_expr.ty, raw_vals);
                    let align = AlignmentAtom::alignment_of(self.program, &key_expr.ty);
                    full_path.push(PathSegment::Dynamic {
                        alignment: align,
                        values: vals,
                    });
                }
                let depth = full_path.len() as u8;
                let pi_guard = if guard.is_const_true() {
                    None
                } else {
                    Some(guard.clone())
                };
                match op {
                    LedgerOp::CellRead => {
                        let cell_ty = target_adt
                            .cell_type()
                            .expect("sema validated CellRead target");
                        let alignment = AlignmentAtom::alignment_of(self.program, cell_ty);
                        let wtypes = wire_types(self.program, cell_ty);
                        let mut results = Vec::with_capacity(wtypes.len());
                        for wt in wtypes {
                            let out = self.fresh_var(&ledger_field.name);
                            self.instructions.push(CircuitInstr::PublicInput {
                                guard: pi_guard.clone(),
                                val_t: wt,
                                output: out,
                            });
                            results.push(CircuitVal::Var(out));
                        }
                        let popeq_results = self.encode_to_native_wires(cell_ty, results.clone());
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: full_path,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Popeq {
                                cached: false,
                                alignment,
                                results: popeq_results,
                            },
                        );
                        results
                    }
                    LedgerOp::CellWrite | LedgerOp::CellWriteCoin => {
                        let cell_ty = target_adt
                            .cell_type()
                            .expect("sema validated CellWrite target");
                        let alignment = AlignmentAtom::alignment_of(self.program, cell_ty);
                        let values = if *op == LedgerOp::CellWriteCoin {
                            let mut coin_vals =
                                self.lower_expr(&args[0], param_vals, locals, guard);
                            let _recip_vals = self.lower_expr(&args[1], param_vals, locals, guard);
                            // Append placeholder mt_index (Uint<64> = 1 wire) to match QualifiedShieldedCoinInfo.
                            coin_vals.push(CircuitVal::Imm(0));
                            self.encode_to_native_wires(cell_ty, coin_vals)
                        } else {
                            let raw_values = self.lower_expr(&args[0], param_vals, locals, guard);
                            self.encode_to_native_wires(cell_ty, raw_values)
                        };
                        self.emit_write_at_path(
                            full_path,
                            ImpactStateValue::Cell { alignment, values },
                            false,
                            guard,
                        );
                        Vec::new()
                    }
                    LedgerOp::CellResetToDefault
                    | LedgerOp::CounterResetToDefault
                    | LedgerOp::SetResetToDefault
                    | LedgerOp::MapResetToDefault
                    | LedgerOp::ListResetToDefault
                    | LedgerOp::MerkleTreeResetToDefault
                    | LedgerOp::HistoricMerkleTreeResetToDefault => {
                        let init_val = adt_initial_state_value(self.program, target_adt);
                        let is_hmt = matches!(target_adt, LedgerAdt::HistoricMerkleTree { .. });
                        self.emit_write_at_path(full_path, init_val, is_hmt, guard);
                        Vec::new()
                    }
                    LedgerOp::CounterIncrement => {
                        let immediate = if let Some(v) = eval_const_u128(&args[0]) {
                            CircuitVal::Imm(v as i128)
                        } else {
                            self.lower_expr(&args[0], param_vals, locals, guard)
                                .into_iter()
                                .next()
                                .unwrap_or(CircuitVal::Imm(0))
                        };
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: true,
                                path: full_path,
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Addi { immediate });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Ins {
                                cached: true,
                                n: depth,
                            },
                        );
                        Vec::new()
                    }
                    LedgerOp::CounterDecrement => {
                        let immediate = if let Some(v) = eval_const_u128(&args[0]) {
                            CircuitVal::Imm(v as i128)
                        } else {
                            self.lower_expr(&args[0], param_vals, locals, guard)
                                .into_iter()
                                .next()
                                .unwrap_or(CircuitVal::Imm(0))
                        };
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: true,
                                path: full_path,
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Subi { immediate });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Ins {
                                cached: true,
                                n: depth,
                            },
                        );
                        Vec::new()
                    }
                    LedgerOp::CounterRead => {
                        let out = self.fresh_var(&ledger_field.name);
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
                            val_t: WireType::Native,
                            output: out,
                        });
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: full_path,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Popeq {
                                cached: true,
                                alignment: vec![AlignmentAtom::Bytes(8)],
                                results: vec![CircuitVal::Var(out)],
                            },
                        );
                        vec![CircuitVal::Var(out)]
                    }
                    LedgerOp::SetIsEmpty | LedgerOp::MapIsEmpty => {
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
                            val_t: WireType::Native,
                            output: out,
                        });
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: full_path,
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Size);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::cell_u64(0),
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Eq);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Popeq {
                                cached: true,
                                alignment: vec![AlignmentAtom::Bytes(1)],
                                results: vec![CircuitVal::Var(out)],
                            },
                        );
                        vec![CircuitVal::Var(out)]
                    }
                    LedgerOp::SetSize | LedgerOp::MapSize => {
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
                            val_t: WireType::Native,
                            output: out,
                        });
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: full_path,
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Size);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Popeq {
                                cached: true,
                                alignment: vec![AlignmentAtom::Bytes(8)],
                                results: vec![CircuitVal::Var(out)],
                            },
                        );
                        vec![CircuitVal::Var(out)]
                    }
                    LedgerOp::SetMember | LedgerOp::MapMember => {
                        let key_ty = match target_adt {
                            LedgerAdt::Set(t) => t.as_ref(),
                            LedgerAdt::Map { key, .. } => key.as_ref(),
                            _ => unreachable!("sema validated member target"),
                        };
                        let key_align = AlignmentAtom::alignment_of(self.program, key_ty);
                        let raw_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        let elem_vals = self.encode_to_native_wires(key_ty, raw_vals);
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
                            val_t: WireType::Native,
                            output: out,
                        });
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: full_path,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::Cell {
                                    alignment: key_align,
                                    values: elem_vals,
                                },
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Member);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Popeq {
                                cached: true,
                                alignment: vec![AlignmentAtom::Bytes(1)],
                                results: vec![CircuitVal::Var(out)],
                            },
                        );
                        vec![CircuitVal::Var(out)]
                    }
                    LedgerOp::SetInsert | LedgerOp::SetInsertCoin => {
                        let LedgerAdt::Set(elem_ty) = target_adt else {
                            unreachable!("sema validated SetInsert target");
                        };
                        let alignment = AlignmentAtom::alignment_of(self.program, elem_ty);
                        let elem_vals = if *op == LedgerOp::SetInsertCoin {
                            let mut coin_vals =
                                self.lower_expr(&args[0], param_vals, locals, guard);
                            let _recip_vals = self.lower_expr(&args[1], param_vals, locals, guard);
                            coin_vals.push(CircuitVal::Imm(0));
                            self.encode_to_native_wires(elem_ty, coin_vals)
                        } else {
                            let raw_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                            self.encode_to_native_wires(elem_ty, raw_vals)
                        };
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: true,
                                path: full_path,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::Cell {
                                    alignment,
                                    values: elem_vals,
                                },
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: true,
                                value: ImpactStateValue::Null,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Ins {
                                cached: false,
                                n: 1,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Ins {
                                cached: true,
                                n: depth,
                            },
                        );
                        Vec::new()
                    }
                    LedgerOp::SetRemove | LedgerOp::MapRemove => {
                        let key_ty = match target_adt {
                            LedgerAdt::Set(t) => t.as_ref(),
                            LedgerAdt::Map { key, .. } => key.as_ref(),
                            _ => unreachable!("sema validated remove target"),
                        };
                        let key_align = AlignmentAtom::alignment_of(self.program, key_ty);
                        let raw_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        let elem_vals = self.encode_to_native_wires(key_ty, raw_vals);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: true,
                                path: full_path,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::Cell {
                                    alignment: key_align,
                                    values: elem_vals,
                                },
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Rem { cached: false });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Ins {
                                cached: true,
                                n: depth,
                            },
                        );
                        Vec::new()
                    }
                    LedgerOp::MapLookup => {
                        let LedgerAdt::Map { key, value } = target_adt else {
                            unreachable!("sema validated MapLookup target");
                        };
                        let val_ty = value
                            .cell_type()
                            .expect("sema validated MapLookup value is Cell");
                        let key_align = AlignmentAtom::alignment_of(self.program, key);
                        let raw_key_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        let key_vals = self.encode_to_native_wires(key, raw_key_vals);
                        let val_align = AlignmentAtom::alignment_of(self.program, val_ty);
                        let wtypes = wire_types(self.program, val_ty);
                        let mut results = Vec::with_capacity(wtypes.len());
                        for wt in wtypes {
                            let out = self.fresh_var("t");
                            self.instructions.push(CircuitInstr::PublicInput {
                                guard: pi_guard.clone(),
                                val_t: wt,
                                output: out,
                            });
                            results.push(CircuitVal::Var(out));
                        }
                        let popeq_results = self.encode_to_native_wires(val_ty, results.clone());
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: full_path,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: vec![PathSegment::Dynamic {
                                    alignment: key_align,
                                    values: key_vals,
                                }],
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Popeq {
                                cached: false,
                                alignment: val_align,
                                results: popeq_results,
                            },
                        );
                        results
                    }
                    LedgerOp::MapInsert | LedgerOp::MapInsertCoin => {
                        let LedgerAdt::Map { key, value } = target_adt else {
                            unreachable!("sema validated MapInsert target");
                        };
                        let key_align = AlignmentAtom::alignment_of(self.program, key);
                        let raw_key_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        let key_vals = self.encode_to_native_wires(key, raw_key_vals);
                        let val_state = if *op == LedgerOp::MapInsertCoin {
                            let val_ty = value
                                .cell_type()
                                .expect("sema validated MapInsertCoin value type");
                            let val_align = AlignmentAtom::alignment_of(self.program, val_ty);
                            let mut coin_vals =
                                self.lower_expr(&args[1], param_vals, locals, guard);
                            let _recip_vals = self.lower_expr(&args[2], param_vals, locals, guard);
                            coin_vals.push(CircuitVal::Imm(0));
                            let val_wires = self.encode_to_native_wires(val_ty, coin_vals);
                            ImpactStateValue::Cell {
                                alignment: val_align,
                                values: val_wires,
                            }
                        } else {
                            match &args[1].kind {
                                ExprKind::DefaultAdt(val_adt) => {
                                    adt_initial_state_value(self.program, val_adt)
                                }
                                _ => {
                                    let val_ty = value
                                        .cell_type()
                                        .expect("sema validated MapInsert value type");
                                    let val_align =
                                        AlignmentAtom::alignment_of(self.program, val_ty);
                                    let raw_val_wires =
                                        self.lower_expr(&args[1], param_vals, locals, guard);
                                    let val_wires =
                                        self.encode_to_native_wires(val_ty, raw_val_wires);
                                    ImpactStateValue::Cell {
                                        alignment: val_align,
                                        values: val_wires,
                                    }
                                }
                            }
                        };
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: true,
                                path: full_path,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::Cell {
                                    alignment: key_align,
                                    values: key_vals,
                                },
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: true,
                                value: val_state,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Ins {
                                cached: false,
                                n: 1,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Ins {
                                cached: true,
                                n: depth,
                            },
                        );
                        Vec::new()
                    }
                    LedgerOp::MapInsertDefault => {
                        let LedgerAdt::Map { key, value } = target_adt else {
                            unreachable!("sema validated MapInsertDefault target");
                        };
                        let key_align = AlignmentAtom::alignment_of(self.program, key);
                        let raw_key_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        let key_vals = self.encode_to_native_wires(key, raw_key_vals);
                        let val_state = adt_initial_state_value(self.program, value);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: true,
                                path: full_path,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::Cell {
                                    alignment: key_align,
                                    values: key_vals,
                                },
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: true,
                                value: val_state,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Ins {
                                cached: false,
                                n: 1,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Ins {
                                cached: true,
                                n: depth,
                            },
                        );
                        Vec::new()
                    }
                    LedgerOp::ListIsEmpty => {
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
                            val_t: WireType::Native,
                            output: out,
                        });
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: full_path,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: vec![PathSegment::Static(1)],
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Type);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::cell_u8(1),
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Eq);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Popeq {
                                cached: true,
                                alignment: vec![AlignmentAtom::Bytes(1)],
                                results: vec![CircuitVal::Var(out)],
                            },
                        );
                        vec![CircuitVal::Var(out)]
                    }
                    LedgerOp::ListLength => {
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
                            val_t: WireType::Native,
                            output: out,
                        });
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: full_path,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: vec![PathSegment::Static(2)],
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Popeq {
                                cached: true,
                                alignment: vec![AlignmentAtom::Bytes(8)],
                                results: vec![CircuitVal::Var(out)],
                            },
                        );
                        vec![CircuitVal::Var(out)]
                    }
                    LedgerOp::ListHead => {
                        let LedgerAdt::List(elem_ty) = target_adt else {
                            unreachable!("sema validated ListHead target");
                        };
                        let maybe_ty = Type::Maybe(elem_ty.clone());
                        let elem_align = AlignmentAtom::alignment_of(self.program, elem_ty);
                        let mut maybe_align = vec![AlignmentAtom::Bytes(1)];
                        maybe_align.extend(elem_align.iter().copied());
                        let wtypes = wire_types(self.program, &maybe_ty);
                        let mut results = Vec::with_capacity(wtypes.len());
                        for wt in wtypes {
                            let out = self.fresh_var("t");
                            self.instructions.push(CircuitInstr::PublicInput {
                                guard: pi_guard.clone(),
                                val_t: wt,
                                output: out,
                            });
                            results.push(CircuitVal::Var(out));
                        }
                        let popeq_results = self.encode_to_native_wires(&maybe_ty, results.clone());
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: full_path,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: vec![PathSegment::Static(0)],
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 0 });
                        self.emit_impact(guard, ImpactVmOp::Type);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::cell_u8(1),
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Eq);
                        self.emit_impact(guard, ImpactVmOp::Branch { skip: 4 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::cell_u8(1),
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Swap { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Concat {
                                cached: false,
                                n: 2 + max_sizeof(&elem_align),
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Jmp { skip: 2 });
                        self.emit_impact(guard, ImpactVmOp::Pop);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::Cell {
                                    alignment: maybe_align.clone(),
                                    values: default_encoded_native_values(self.program, &maybe_ty),
                                },
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Popeq {
                                cached: true,
                                alignment: maybe_align,
                                results: popeq_results,
                            },
                        );
                        results
                    }
                    LedgerOp::ListPopFront => {
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: true,
                                path: full_path,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: vec![PathSegment::Static(1)],
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Ins {
                                cached: true,
                                n: depth,
                            },
                        );
                        Vec::new()
                    }
                    LedgerOp::ListPushFront | LedgerOp::ListPushFrontCoin => {
                        let LedgerAdt::List(elem_ty) = target_adt else {
                            unreachable!("sema validated ListPushFront target");
                        };
                        let val_align = AlignmentAtom::alignment_of(self.program, elem_ty);
                        let val_wires = if *op == LedgerOp::ListPushFrontCoin {
                            let mut coin_vals =
                                self.lower_expr(&args[0], param_vals, locals, guard);
                            let _recip_vals = self.lower_expr(&args[1], param_vals, locals, guard);
                            coin_vals.push(CircuitVal::Imm(0));
                            self.encode_to_native_wires(elem_ty, coin_vals)
                        } else {
                            let raw_val_wires =
                                self.lower_expr(&args[0], param_vals, locals, guard);
                            self.encode_to_native_wires(elem_ty, raw_val_wires)
                        };
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: true,
                                path: full_path,
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: vec![PathSegment::Static(2)],
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Addi {
                                immediate: CircuitVal::Imm(1),
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: true,
                                value: ImpactStateValue::Array(vec![
                                    ImpactStateValue::Cell {
                                        alignment: val_align,
                                        values: val_wires,
                                    },
                                    ImpactStateValue::Null,
                                    ImpactStateValue::Null,
                                ]),
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Swap { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::cell_u8(2),
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Swap { n: 0 });
                        self.emit_impact(guard, ImpactVmOp::Ins { cached: true, n: 1 });
                        self.emit_impact(guard, ImpactVmOp::Swap { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::cell_u8(1),
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Swap { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Ins {
                                cached: true,
                                n: depth + 1,
                            },
                        );
                        Vec::new()
                    }
                    LedgerOp::MerkleTreeInsert
                    | LedgerOp::MerkleTreeInsertHash
                    | LedgerOp::MerkleTreeInsertIndex
                    | LedgerOp::MerkleTreeInsertHashIndex
                    | LedgerOp::MerkleTreeInsertIndexDefault => {
                        let LedgerAdt::MerkleTree { value: elem_ty, .. } = target_adt else {
                            unreachable!("sema validated MerkleTree insert target");
                        };
                        let hash_pair: Vec<CircuitVal> = match op {
                            LedgerOp::MerkleTreeInsertHash
                            | LedgerOp::MerkleTreeInsertHashIndex => {
                                self.lower_expr(&args[0], param_vals, locals, guard)
                            }
                            _ => {
                                let alignment = AlignmentAtom::alignment_of(self.program, elem_ty);
                                let raw_item_vals = if *op == LedgerOp::MerkleTreeInsertIndexDefault
                                {
                                    self.lower_default(elem_ty)
                                } else {
                                    self.lower_expr(&args[0], param_vals, locals, guard)
                                };
                                let item_vals = self.encode_to_native_wires(elem_ty, raw_item_vals);
                                let mut leaf_align = vec![AlignmentAtom::Bytes(6)];
                                leaf_align.extend(alignment);
                                let mut hash_inputs = bytes_to_wires(b"mdn:lh");
                                hash_inputs.extend(item_vals);

                                let bytes_var = self.fresh_var("bytes");
                                self.instructions.push(CircuitInstr::PersistentHash {
                                    alignment: leaf_align,
                                    inputs: hash_inputs,
                                    output: bytes_var,
                                });
                                let lo = self.fresh_var("hash");
                                let hi = self.fresh_var("hash");
                                self.instructions.push(CircuitInstr::BytesIntoNatives {
                                    bytes: bytes_var,
                                    outputs: vec![lo, hi],
                                });
                                vec![CircuitVal::Var(hi), CircuitVal::Var(lo)]
                            }
                        };
                        let explicit_idx: Option<CircuitVal> = match op {
                            LedgerOp::MerkleTreeInsertIndex
                            | LedgerOp::MerkleTreeInsertHashIndex => self
                                .lower_expr(&args[1], param_vals, locals, guard)
                                .into_iter()
                                .next(),
                            LedgerOp::MerkleTreeInsertIndexDefault => self
                                .lower_expr(&args[0], param_vals, locals, guard)
                                .into_iter()
                                .next(),
                            _ => None,
                        };

                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: true,
                                path: full_path,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: true,
                                path: vec![PathSegment::Static(0)],
                            },
                        );
                        if let Some(idx_val) = explicit_idx {
                            self.emit_impact(
                                guard,
                                ImpactVmOp::Push {
                                    storage: false,
                                    value: ImpactStateValue::Cell {
                                        alignment: vec![AlignmentAtom::Bytes(8)],
                                        values: vec![idx_val],
                                    },
                                },
                            );
                        } else {
                            self.emit_impact(guard, ImpactVmOp::Dup { n: 2 });
                            self.emit_impact(
                                guard,
                                ImpactVmOp::Idx {
                                    cached: false,
                                    push_path: false,
                                    path: vec![PathSegment::Static(1)],
                                },
                            );
                        }
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: true,
                                value: ImpactStateValue::Cell {
                                    alignment: vec![AlignmentAtom::Bytes(32)],
                                    values: hash_pair,
                                },
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Ins {
                                cached: false,
                                n: 1,
                            },
                        );
                        if matches!(
                            op,
                            LedgerOp::MerkleTreeInsert | LedgerOp::MerkleTreeInsertHash
                        ) {
                            self.emit_impact(guard, ImpactVmOp::Ins { cached: true, n: 1 });
                            self.emit_impact(
                                guard,
                                ImpactVmOp::Idx {
                                    cached: false,
                                    push_path: true,
                                    path: vec![PathSegment::Static(1)],
                                },
                            );
                            self.emit_impact(
                                guard,
                                ImpactVmOp::Addi {
                                    immediate: CircuitVal::Imm(1),
                                },
                            );
                            self.emit_impact(
                                guard,
                                ImpactVmOp::Ins {
                                    cached: true,
                                    n: depth + 1,
                                },
                            );
                        } else {
                            self.emit_impact(
                                guard,
                                ImpactVmOp::Ins {
                                    cached: true,
                                    n: depth + 1,
                                },
                            );
                        }
                        Vec::new()
                    }
                    LedgerOp::MerkleTreeIsFull | LedgerOp::HistoricMerkleTreeIsFull => {
                        let tree_depth = match target_adt {
                            LedgerAdt::MerkleTree { depth, .. }
                            | LedgerAdt::HistoricMerkleTree { depth, .. } => *depth,
                            _ => unreachable!("sema validated isFull target"),
                        };
                        let capacity = 1u64 << tree_depth;
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
                            val_t: WireType::Native,
                            output: out,
                        });
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: full_path,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: vec![PathSegment::Static(1)],
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::cell_u64(capacity),
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Lt);
                        self.emit_impact(guard, ImpactVmOp::Neg);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Popeq {
                                cached: true,
                                alignment: vec![AlignmentAtom::Bytes(1)],
                                results: vec![CircuitVal::Var(out)],
                            },
                        );
                        vec![CircuitVal::Var(out)]
                    }
                    LedgerOp::MerkleTreeCheckRoot => {
                        let rt_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
                            val_t: WireType::Native,
                            output: out,
                        });
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: full_path,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: vec![PathSegment::Static(0)],
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Root);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::Cell {
                                    alignment: vec![AlignmentAtom::Field],
                                    values: rt_vals,
                                },
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Eq);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Popeq {
                                cached: true,
                                alignment: vec![AlignmentAtom::Bytes(1)],
                                results: vec![CircuitVal::Var(out)],
                            },
                        );
                        vec![CircuitVal::Var(out)]
                    }
                    LedgerOp::HistoricMerkleTreeInsert
                    | LedgerOp::HistoricMerkleTreeInsertHash
                    | LedgerOp::HistoricMerkleTreeInsertIndex
                    | LedgerOp::HistoricMerkleTreeInsertHashIndex
                    | LedgerOp::HistoricMerkleTreeInsertIndexDefault => {
                        let LedgerAdt::HistoricMerkleTree { value: elem_ty, .. } = target_adt
                        else {
                            unreachable!("sema validated HistoricMerkleTree insert target");
                        };
                        let hash_pair: Vec<CircuitVal> = match op {
                            LedgerOp::HistoricMerkleTreeInsertHash
                            | LedgerOp::HistoricMerkleTreeInsertHashIndex => {
                                self.lower_expr(&args[0], param_vals, locals, guard)
                            }
                            _ => {
                                let alignment = AlignmentAtom::alignment_of(self.program, elem_ty);
                                let raw_item_vals =
                                    if *op == LedgerOp::HistoricMerkleTreeInsertIndexDefault {
                                        self.lower_default(elem_ty)
                                    } else {
                                        self.lower_expr(&args[0], param_vals, locals, guard)
                                    };
                                let item_vals = self.encode_to_native_wires(elem_ty, raw_item_vals);
                                let mut leaf_align = vec![AlignmentAtom::Bytes(6)];
                                leaf_align.extend(alignment);
                                let mut hash_inputs = bytes_to_wires(b"mdn:lh");
                                hash_inputs.extend(item_vals);

                                let bytes_var = self.fresh_var("bytes");
                                self.instructions.push(CircuitInstr::PersistentHash {
                                    alignment: leaf_align,
                                    inputs: hash_inputs,
                                    output: bytes_var,
                                });
                                let lo = self.fresh_var("hash");
                                let hi = self.fresh_var("hash");
                                self.instructions.push(CircuitInstr::BytesIntoNatives {
                                    bytes: bytes_var,
                                    outputs: vec![lo, hi],
                                });
                                vec![CircuitVal::Var(hi), CircuitVal::Var(lo)]
                            }
                        };
                        let explicit_idx: Option<CircuitVal> = match op {
                            LedgerOp::HistoricMerkleTreeInsertIndex
                            | LedgerOp::HistoricMerkleTreeInsertHashIndex => self
                                .lower_expr(&args[1], param_vals, locals, guard)
                                .into_iter()
                                .next(),
                            LedgerOp::HistoricMerkleTreeInsertIndexDefault => self
                                .lower_expr(&args[0], param_vals, locals, guard)
                                .into_iter()
                                .next(),
                            _ => None,
                        };

                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: true,
                                path: full_path,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: true,
                                path: vec![PathSegment::Static(0)],
                            },
                        );
                        if let Some(idx_val) = explicit_idx {
                            self.emit_impact(
                                guard,
                                ImpactVmOp::Push {
                                    storage: false,
                                    value: ImpactStateValue::Cell {
                                        alignment: vec![AlignmentAtom::Bytes(8)],
                                        values: vec![idx_val],
                                    },
                                },
                            );
                        } else {
                            self.emit_impact(guard, ImpactVmOp::Dup { n: 2 });
                            self.emit_impact(
                                guard,
                                ImpactVmOp::Idx {
                                    cached: false,
                                    push_path: false,
                                    path: vec![PathSegment::Static(1)],
                                },
                            );
                        }
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: true,
                                value: ImpactStateValue::Cell {
                                    alignment: vec![AlignmentAtom::Bytes(32)],
                                    values: hash_pair,
                                },
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Ins {
                                cached: false,
                                n: 1,
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Ins { cached: true, n: 1 });
                        if matches!(
                            op,
                            LedgerOp::HistoricMerkleTreeInsert
                                | LedgerOp::HistoricMerkleTreeInsertHash
                        ) {
                            self.emit_impact(
                                guard,
                                ImpactVmOp::Idx {
                                    cached: false,
                                    push_path: true,
                                    path: vec![PathSegment::Static(1)],
                                },
                            );
                            self.emit_impact(
                                guard,
                                ImpactVmOp::Addi {
                                    immediate: CircuitVal::Imm(1),
                                },
                            );
                            self.emit_impact(guard, ImpactVmOp::Ins { cached: true, n: 1 });
                        }
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: true,
                                path: vec![PathSegment::Static(2)],
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 2 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: vec![PathSegment::Static(0)],
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Root);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: true,
                                value: ImpactStateValue::Null,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Ins {
                                cached: false,
                                n: 1,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Ins {
                                cached: true,
                                n: depth + 1,
                            },
                        );
                        Vec::new()
                    }
                    LedgerOp::HistoricMerkleTreeResetHistory => {
                        let mut hist_path = full_path;
                        hist_path.push(PathSegment::Static(2));
                        self.emit_write_at_path(
                            hist_path,
                            ImpactStateValue::EmptyMap,
                            false,
                            guard,
                        );
                        Vec::new()
                    }
                    LedgerOp::HistoricMerkleTreeCheckRoot => {
                        let rt_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
                            val_t: WireType::Native,
                            output: out,
                        });
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: full_path,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: vec![PathSegment::Static(2)],
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::Cell {
                                    alignment: vec![AlignmentAtom::Field],
                                    values: rt_vals,
                                },
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Member);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Popeq {
                                cached: true,
                                alignment: vec![AlignmentAtom::Bytes(1)],
                                results: vec![CircuitVal::Var(out)],
                            },
                        );
                        vec![CircuitVal::Var(out)]
                    }
                    LedgerOp::CounterLessThan => {
                        let threshold_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
                            val_t: WireType::Native,
                            output: out,
                        });
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: full_path,
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::Cell {
                                    alignment: vec![AlignmentAtom::Bytes(8)],
                                    values: threshold_vals,
                                },
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Lt);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Popeq {
                                cached: true,
                                alignment: vec![AlignmentAtom::Bytes(1)],
                                results: vec![CircuitVal::Var(out)],
                            },
                        );
                        vec![CircuitVal::Var(out)]
                    }
                    LedgerOp::KernelSelf => {
                        let alignment = AlignmentAtom::alignment_of(self.program, &expr.ty);
                        let count = wire_count(self.program, &expr.ty);
                        let mut results = Vec::with_capacity(count);
                        for _ in 0..count {
                            let out = self.fresh_var("self");
                            self.instructions.push(CircuitInstr::PublicInput {
                                guard: pi_guard.clone(),
                                val_t: WireType::Native,
                                output: out,
                            });
                            results.push(CircuitVal::Var(out));
                        }
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 2 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: true,
                                push_path: false,
                                path: vec![PathSegment::Static(0)],
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Popeq {
                                cached: true,
                                alignment,
                                results: results.clone(),
                            },
                        );
                        results
                    }
                    LedgerOp::KernelCaller => {
                        let alignment = AlignmentAtom::alignment_of(self.program, &expr.ty);
                        let count = wire_count(self.program, &expr.ty);
                        let max_sz = max_sizeof(&alignment);
                        let mut results = Vec::with_capacity(count);
                        for _ in 0..count {
                            let out = self.fresh_var("caller");
                            self.instructions.push(CircuitInstr::PublicInput {
                                guard: pi_guard.clone(),
                                val_t: WireType::Native,
                                output: out,
                            });
                            results.push(CircuitVal::Var(out));
                        }
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 2 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: true,
                                push_path: false,
                                path: vec![PathSegment::Static(6)],
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 0 });
                        self.emit_impact(guard, ImpactVmOp::Type);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::cell_u8(1),
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Eq);
                        self.emit_impact(guard, ImpactVmOp::Branch { skip: 4 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::cell_u8(1),
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Swap { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Concat {
                                cached: false,
                                n: max_sz,
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Jmp { skip: 2 });
                        self.emit_impact(guard, ImpactVmOp::Pop);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::Cell {
                                    alignment: alignment.clone(),
                                    values: vec![CircuitVal::Imm(0); count],
                                },
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Popeq {
                                cached: true,
                                alignment,
                                results: results.clone(),
                            },
                        );
                        results
                    }
                    LedgerOp::KernelCheckpoint => {
                        self.emit_impact(guard, ImpactVmOp::Ckpt);
                        Vec::new()
                    }
                    LedgerOp::KernelClaimZswapNullifier
                    | LedgerOp::KernelClaimZswapCoinReceive
                    | LedgerOp::KernelClaimZswapCoinSpend => {
                        let slot = match op {
                            LedgerOp::KernelClaimZswapNullifier => 0,
                            LedgerOp::KernelClaimZswapCoinReceive => 1,
                            LedgerOp::KernelClaimZswapCoinSpend => 2,
                            _ => unreachable!(),
                        };
                        let vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        self.emit_impact(guard, ImpactVmOp::Swap { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: true,
                                push_path: true,
                                path: vec![PathSegment::Static(slot)],
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::Cell {
                                    alignment: vec![AlignmentAtom::Bytes(32)],
                                    values: vals,
                                },
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::Null,
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Ins { cached: true, n: 2 });
                        self.emit_impact(guard, ImpactVmOp::Swap { n: 0 });
                        Vec::new()
                    }
                    LedgerOp::KernelClaimContractCall => {
                        let addr_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        let ep_vals = self.lower_expr(&args[1], param_vals, locals, guard);
                        let comm_vals = self.lower_expr(&args[2], param_vals, locals, guard);
                        self.emit_kernel_claim_contract_call(addr_vals, ep_vals, comm_vals, guard);
                        Vec::new()
                    }
                    LedgerOp::KernelMintShielded
                    | LedgerOp::KernelMintUnshielded
                    | LedgerOp::KernelIncUnshieldedInputs
                    | LedgerOp::KernelIncUnshieldedOutputs => {
                        let (slot, amt_bytes) = match op {
                            LedgerOp::KernelMintShielded => (4, 8),
                            LedgerOp::KernelMintUnshielded => (5, 8),
                            LedgerOp::KernelIncUnshieldedInputs => (6, 16),
                            LedgerOp::KernelIncUnshieldedOutputs => (7, 16),
                            _ => unreachable!(),
                        };
                        let key_align = AlignmentAtom::alignment_of(self.program, &args[0].ty);
                        let key_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        let amt_vals = self.lower_expr(&args[1], param_vals, locals, guard);
                        self.emit_kernel_effects_map_add(
                            slot, key_align, key_vals, amt_bytes, amt_vals, guard,
                        );
                        Vec::new()
                    }
                    LedgerOp::KernelClaimUnshieldedCoinSpend => {
                        let tok_align = AlignmentAtom::alignment_of(self.program, &args[0].ty);
                        let addr_align = AlignmentAtom::alignment_of(self.program, &args[1].ty);
                        let mut key_align = tok_align;
                        key_align.extend(addr_align);
                        let mut key_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        key_vals.extend(self.lower_expr(&args[1], param_vals, locals, guard));
                        let amt_vals = self.lower_expr(&args[2], param_vals, locals, guard);
                        self.emit_kernel_effects_map_add(
                            8, key_align, key_vals, 16, amt_vals, guard,
                        );
                        Vec::new()
                    }
                    LedgerOp::KernelBalance => {
                        let tok_align = AlignmentAtom::alignment_of(self.program, &args[0].ty);
                        let tok_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        let out = self.fresh_var("balance");
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
                            val_t: WireType::Native,
                            output: out,
                        });
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 2 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: true,
                                push_path: false,
                                path: vec![PathSegment::Static(5)],
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::Cell {
                                    alignment: tok_align.clone(),
                                    values: tok_vals.clone(),
                                },
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Member);
                        self.emit_impact(guard, ImpactVmOp::Branch { skip: 3 });
                        self.emit_impact(guard, ImpactVmOp::Pop);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::Cell {
                                    alignment: vec![AlignmentAtom::Bytes(16)],
                                    values: vec![CircuitVal::Imm(0)],
                                },
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Jmp { skip: 1 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: true,
                                push_path: false,
                                path: vec![PathSegment::Dynamic {
                                    alignment: tok_align,
                                    values: tok_vals,
                                }],
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Popeq {
                                cached: true,
                                alignment: vec![AlignmentAtom::Bytes(16)],
                                results: vec![CircuitVal::Var(out)],
                            },
                        );
                        vec![CircuitVal::Var(out)]
                    }
                    LedgerOp::KernelBalanceLessThan => {
                        let tok_align = AlignmentAtom::alignment_of(self.program, &args[0].ty);
                        let tok_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        let amt_vals = self.lower_expr(&args[1], param_vals, locals, guard);
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
                            val_t: WireType::Native,
                            output: out,
                        });
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 2 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: true,
                                push_path: false,
                                path: vec![PathSegment::Static(5)],
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::Cell {
                                    alignment: tok_align.clone(),
                                    values: tok_vals.clone(),
                                },
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Member);
                        self.emit_impact(guard, ImpactVmOp::Branch { skip: 3 });
                        self.emit_impact(guard, ImpactVmOp::Pop);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::Cell {
                                    alignment: vec![AlignmentAtom::Bytes(16)],
                                    values: vec![CircuitVal::Imm(0)],
                                },
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Jmp { skip: 1 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: true,
                                push_path: false,
                                path: vec![PathSegment::Dynamic {
                                    alignment: tok_align,
                                    values: tok_vals,
                                }],
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::Cell {
                                    alignment: vec![AlignmentAtom::Bytes(16)],
                                    values: amt_vals,
                                },
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Lt);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Popeq {
                                cached: true,
                                alignment: vec![AlignmentAtom::Bytes(1)],
                                results: vec![CircuitVal::Var(out)],
                            },
                        );
                        vec![CircuitVal::Var(out)]
                    }
                    LedgerOp::KernelBalanceGreaterThan => {
                        let tok_align = AlignmentAtom::alignment_of(self.program, &args[0].ty);
                        let tok_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        let amt_vals = self.lower_expr(&args[1], param_vals, locals, guard);
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
                            val_t: WireType::Native,
                            output: out,
                        });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::Cell {
                                    alignment: vec![AlignmentAtom::Bytes(16)],
                                    values: amt_vals,
                                },
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 3 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: true,
                                push_path: false,
                                path: vec![PathSegment::Static(5)],
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 0 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::Cell {
                                    alignment: tok_align.clone(),
                                    values: tok_vals.clone(),
                                },
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Member);
                        self.emit_impact(guard, ImpactVmOp::Branch { skip: 3 });
                        self.emit_impact(guard, ImpactVmOp::Pop);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::Cell {
                                    alignment: vec![AlignmentAtom::Bytes(16)],
                                    values: vec![CircuitVal::Imm(0)],
                                },
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Jmp { skip: 1 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: true,
                                push_path: false,
                                path: vec![PathSegment::Dynamic {
                                    alignment: tok_align,
                                    values: tok_vals,
                                }],
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Lt);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Popeq {
                                cached: true,
                                alignment: vec![AlignmentAtom::Bytes(1)],
                                results: vec![CircuitVal::Var(out)],
                            },
                        );
                        vec![CircuitVal::Var(out)]
                    }
                    LedgerOp::KernelBlockTimeLessThan => {
                        let time_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
                            val_t: WireType::Native,
                            output: out,
                        });
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 2 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: true,
                                push_path: false,
                                path: vec![PathSegment::Static(2)],
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::Cell {
                                    alignment: vec![AlignmentAtom::Bytes(8)],
                                    values: time_vals,
                                },
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Lt);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Popeq {
                                cached: true,
                                alignment: vec![AlignmentAtom::Bytes(1)],
                                results: vec![CircuitVal::Var(out)],
                            },
                        );
                        vec![CircuitVal::Var(out)]
                    }
                    LedgerOp::KernelBlockTimeGreaterThan => {
                        let time_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
                            val_t: WireType::Native,
                            output: out,
                        });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Push {
                                storage: false,
                                value: ImpactStateValue::Cell {
                                    alignment: vec![AlignmentAtom::Bytes(8)],
                                    values: time_vals,
                                },
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 3 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Idx {
                                cached: true,
                                push_path: false,
                                path: vec![PathSegment::Static(2)],
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Lt);
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Popeq {
                                cached: true,
                                alignment: vec![AlignmentAtom::Bytes(1)],
                                results: vec![CircuitVal::Var(out)],
                            },
                        );
                        vec![CircuitVal::Var(out)]
                    }
                }
            }
        }
    }

    /// Serialize `vals` of Compact type `ty` into `Bytes<target_len>` ZKIR scalar wires.
    fn lower_serialize_wires(
        &mut self,
        ty: &Type,
        vals: &[CircuitVal],
        target_len: u32,
    ) -> Vec<CircuitVal> {
        if target_len == 0 {
            return Vec::new();
        }
        // Fast path: a `Bytes<N>` or a single-field struct wrapping `Bytes<N>` (e.g. `ShieldedSpend`)
        // whose length matches `target_len` needs zero byte unpacking/repacking.
        match self.program.underlying_type(ty) {
            Type::Bytes(n) if *n == target_len => return vals.to_vec(),
            Type::Struct(_) => {
                if let Some(fields) = self.program.struct_fields_of(ty)
                    && fields.len() == 1
                    && let Type::Bytes(n) = self.program.underlying_type(&fields[0].1)
                    && *n == target_len
                {
                    return vals.to_vec();
                }
            }
            _ => {}
        }
        let mut bytes = Vec::with_capacity(target_len as usize);
        let mut cursor = 0usize;
        self.serialize_type_to_bytes(ty, vals, &mut cursor, &mut bytes);
        while bytes.len() < target_len as usize {
            bytes.push(CircuitVal::Imm(0));
        }
        self.pack_bytes_wires(&bytes)
    }

    fn serialize_type_to_bytes(
        &mut self,
        ty: &Type,
        vals: &[CircuitVal],
        cursor: &mut usize,
        out: &mut Vec<CircuitVal>,
    ) {
        match self.program.underlying_type(ty).clone() {
            Type::Boolean => {
                out.push(vals[*cursor].clone());
                *cursor += 1;
            }
            Type::Uint(bits) => {
                let v = vals[*cursor].clone();
                *cursor += 1;
                let nbytes = if bits == 0 { 0 } else { bits.div_ceil(8) };
                if nbytes == 1 {
                    out.push(v);
                } else if nbytes > 1 {
                    let unpacked = self.unpack_bytes_wires(&[v], nbytes);
                    out.extend(unpacked);
                }
            }
            Type::Enum(id) => {
                let v = vals[*cursor].clone();
                *cursor += 1;
                let count = self.program.enum_decl(id).variants.len() as u32;
                let maxval = count.saturating_sub(1);
                let nbytes = if maxval == 0 {
                    0
                } else {
                    (u32::BITS - maxval.leading_zeros()).div_ceil(8)
                };
                if nbytes == 1 {
                    out.push(v);
                } else if nbytes > 1 {
                    let unpacked = self.unpack_bytes_wires(&[v], nbytes);
                    out.extend(unpacked);
                }
            }
            Type::Field => {
                let v = vals[*cursor].clone();
                *cursor += 1;
                let hi = self.fresh_var("hi");
                let lo = self.fresh_var("lo");
                self.instructions.push(CircuitInstr::DivModPowerOfTwo {
                    val: v,
                    bits: FIELD_BYTES * 8,
                    quotient: hi,
                    remainder: lo,
                });
                let unpacked =
                    self.unpack_bytes_wires(&[CircuitVal::Var(hi), CircuitVal::Var(lo)], 32);
                out.extend(unpacked);
            }
            Type::CurveField(_) => {
                let v = vals[*cursor].clone();
                *cursor += 1;
                let tmp = self.fresh_var("bytes");
                self.instructions.push(CircuitInstr::ToBytes {
                    input: v,
                    output: tmp,
                });
                let lo = self.fresh_var("lo");
                let hi = self.fresh_var("hi");
                self.instructions.push(CircuitInstr::BytesIntoNatives {
                    bytes: tmp,
                    outputs: vec![lo, hi],
                });
                let unpacked =
                    self.unpack_bytes_wires(&[CircuitVal::Var(hi), CircuitVal::Var(lo)], 32);
                out.extend(unpacked);
            }
            Type::Bytes(n) => {
                let w = wire_count(self.program, &Type::Bytes(n));
                let slice = &vals[*cursor..*cursor + w];
                *cursor += w;
                if n > 0 {
                    let unpacked = self.unpack_bytes_wires(slice, n);
                    out.extend(unpacked);
                }
            }
            Type::Vector(len, elem) => {
                for _ in 0..len {
                    self.serialize_type_to_bytes(&elem, vals, cursor, out);
                }
            }
            Type::Tuple(elems) => {
                for e in elems {
                    self.serialize_type_to_bytes(&e, vals, cursor, out);
                }
            }
            Type::Struct(_)
            | Type::Maybe(_)
            | Type::Either(_, _)
            | Type::MerkleTreeDigest
            | Type::MerkleTreePathEntry
            | Type::MerkleTreePath(_, _) => {
                for (_, fty) in self.program.struct_fields_of(ty).unwrap_or_default() {
                    self.serialize_type_to_bytes(&fty, vals, cursor, out);
                }
            }
            Type::CurvePoint(_) | Type::Contract(_) | Type::Opaque(_) => {
                unreachable!("sema validated serializable type")
            }
            Type::NewType(_) => unreachable!("underlying_type peeled all NewType layers"),
        }
    }

    fn lower_deserialize_from_bytes(
        &mut self,
        ty: &Type,
        byte_vals: &[CircuitVal],
        offset: &mut usize,
    ) -> Vec<CircuitVal> {
        match self.program.underlying_type(ty).clone() {
            Type::Boolean => {
                let b = byte_vals[*offset].clone();
                *offset += 1;
                let out = self.fresh_var("t");
                self.instructions.push(CircuitInstr::TestEq {
                    a: b,
                    b: CircuitVal::Imm(1),
                    output: out,
                });
                vec![CircuitVal::Var(out)]
            }
            Type::Uint(bits) => {
                let nbytes = if bits == 0 { 0 } else { bits.div_ceil(8) } as usize;
                if nbytes == 0 {
                    return vec![CircuitVal::Imm(0)];
                }
                let slice = &byte_vals[*offset..*offset + nbytes];
                *offset += nbytes;
                let packed = self.pack_bytes_wires(slice);
                if bits < (nbytes as u32) * 8 {
                    self.instructions.push(CircuitInstr::ConstrainBits {
                        val: packed[0].clone(),
                        bits,
                    });
                }
                packed
            }
            Type::Enum(id) => {
                let count = self.program.enum_decl(id).variants.len() as u32;
                let maxval = count.saturating_sub(1);
                let nbytes = if maxval == 0 {
                    0
                } else {
                    (u32::BITS - maxval.leading_zeros()).div_ceil(8)
                } as usize;
                if nbytes == 0 {
                    return vec![CircuitVal::Imm(0)];
                }
                let slice = &byte_vals[*offset..*offset + nbytes];
                *offset += nbytes;
                self.pack_bytes_wires(slice)
            }
            Type::Field => {
                let slice = &byte_vals[*offset..*offset + 32];
                *offset += 32;
                let packed = self.pack_bytes_wires(slice);
                // Reconstitute `lo + hi * 2^248` in BLS12-381 scalar field.
                let mut pow = vec![0u8; 32];
                pow[31] = 1;
                let hi_scaled = self.fresh_var("t");
                self.instructions.push(CircuitInstr::Mul {
                    a: packed[0].clone(),
                    b: CircuitVal::ImmBytes(pow),
                    output: hi_scaled,
                });
                let out = self.fresh_var("t");
                self.instructions.push(CircuitInstr::Add {
                    a: packed[1].clone(),
                    b: CircuitVal::Var(hi_scaled),
                    output: out,
                });
                vec![CircuitVal::Var(out)]
            }
            Type::CurveField(f) => {
                let slice = &byte_vals[*offset..*offset + 32];
                *offset += 32;
                let mut packed = self.pack_bytes_wires(slice);
                packed.reverse();
                let tmp = self.fresh_var("bytes");
                self.instructions.push(CircuitInstr::BytesFromNatives {
                    inputs: packed,
                    len: 32,
                    output: tmp,
                });
                let out = self.fresh_var("t");
                self.instructions.push(CircuitInstr::FromBytes {
                    bytes: tmp,
                    val_t: WireType::from_field(f),
                    output: out,
                });
                vec![CircuitVal::Var(out)]
            }
            Type::Bytes(n) => {
                let slice = &byte_vals[*offset..*offset + (n as usize)];
                *offset += n as usize;
                self.pack_bytes_wires(slice)
            }
            Type::Vector(len, elem) => {
                let mut out = Vec::new();
                for _ in 0..len {
                    out.extend(self.lower_deserialize_from_bytes(&elem, byte_vals, offset));
                }
                out
            }
            Type::Tuple(elems) => {
                let mut out = Vec::new();
                for e in elems {
                    out.extend(self.lower_deserialize_from_bytes(&e, byte_vals, offset));
                }
                out
            }
            Type::Struct(_)
            | Type::Maybe(_)
            | Type::Either(_, _)
            | Type::MerkleTreeDigest
            | Type::MerkleTreePathEntry
            | Type::MerkleTreePath(_, _) => {
                let mut out = Vec::new();
                for (_, fty) in self.program.struct_fields_of(ty).unwrap_or_default() {
                    out.extend(self.lower_deserialize_from_bytes(&fty, byte_vals, offset));
                }
                out
            }
            Type::CurvePoint(_) | Type::Contract(_) | Type::Opaque(_) => {
                unreachable!("sema validated deserializable type")
            }
            Type::NewType(_) => unreachable!("underlying_type peeled all NewType layers"),
        }
    }

    fn emit_kernel_claim_contract_call(
        &mut self,
        addr_vals: Vec<CircuitVal>,
        ep_vals: Vec<CircuitVal>,
        comm_vals: Vec<CircuitVal>,
        guard: &CircuitVal,
    ) {
        let mut cell_vals = addr_vals;
        cell_vals.extend(ep_vals);
        cell_vals.extend(comm_vals);
        self.emit_impact(guard, ImpactVmOp::Swap { n: 0 });
        self.emit_impact(
            guard,
            ImpactVmOp::Idx {
                cached: true,
                push_path: true,
                path: vec![PathSegment::Static(3)],
            },
        );
        self.emit_impact(guard, ImpactVmOp::Dup { n: 0 });
        self.emit_impact(guard, ImpactVmOp::Size);
        self.emit_impact(
            guard,
            ImpactVmOp::Push {
                storage: false,
                value: ImpactStateValue::Cell {
                    alignment: vec![
                        AlignmentAtom::Bytes(32),
                        AlignmentAtom::Bytes(32),
                        AlignmentAtom::Field,
                    ],
                    values: cell_vals,
                },
            },
        );
        self.emit_impact(
            guard,
            ImpactVmOp::Concat {
                cached: true,
                n: 160,
            },
        );
        self.emit_impact(
            guard,
            ImpactVmOp::Push {
                storage: false,
                value: ImpactStateValue::Null,
            },
        );
        self.emit_impact(guard, ImpactVmOp::Ins { cached: true, n: 2 });
        self.emit_impact(guard, ImpactVmOp::Swap { n: 0 });
    }

    fn emit_kernel_effects_map_add(
        &mut self,
        effects_slot: u32,
        key_align: Vec<AlignmentAtom>,
        key_vals: Vec<CircuitVal>,
        amt_bytes: u32,
        amt_vals: Vec<CircuitVal>,
        guard: &CircuitVal,
    ) {
        self.emit_impact(guard, ImpactVmOp::Swap { n: 0 });
        self.emit_impact(
            guard,
            ImpactVmOp::Idx {
                cached: true,
                push_path: true,
                path: vec![PathSegment::Static(effects_slot)],
            },
        );
        self.emit_impact(
            guard,
            ImpactVmOp::Push {
                storage: false,
                value: ImpactStateValue::Cell {
                    alignment: key_align,
                    values: key_vals,
                },
            },
        );
        self.emit_impact(guard, ImpactVmOp::Dup { n: 1 });
        self.emit_impact(guard, ImpactVmOp::Dup { n: 1 });
        self.emit_impact(guard, ImpactVmOp::Member);
        self.emit_impact(
            guard,
            ImpactVmOp::Push {
                storage: false,
                value: ImpactStateValue::Cell {
                    alignment: vec![AlignmentAtom::Bytes(amt_bytes)],
                    values: amt_vals,
                },
            },
        );
        self.emit_impact(guard, ImpactVmOp::Swap { n: 0 });
        self.emit_impact(guard, ImpactVmOp::Neg);
        self.emit_impact(guard, ImpactVmOp::Branch { skip: 4 });
        self.emit_impact(guard, ImpactVmOp::Dup { n: 2 });
        self.emit_impact(guard, ImpactVmOp::Dup { n: 2 });
        self.emit_impact(
            guard,
            ImpactVmOp::Idx {
                cached: true,
                push_path: false,
                path: vec![PathSegment::Stack],
            },
        );
        self.emit_impact(guard, ImpactVmOp::Add);
        self.emit_impact(guard, ImpactVmOp::Ins { cached: true, n: 2 });
        self.emit_impact(guard, ImpactVmOp::Swap { n: 0 });
    }

    fn emit_impact(&mut self, guard: &CircuitVal, op: ImpactVmOp) {
        self.instructions.push(CircuitInstr::Impact {
            guard: guard.clone(),
            op,
        });
    }

    /// Emit the standard Impact VM overwrite pattern for `Cell.write` and `<ADT>.resetToDefault`
    /// along an arbitrary static/dynamic path `full_path`.
    fn emit_write_at_path(
        &mut self,
        mut full_path: Vec<PathSegment>,
        value: ImpactStateValue,
        init_historic_root: bool,
        guard: &CircuitVal,
    ) {
        let len = full_path.len();
        let last = full_path.pop().expect("non-empty ledger path");
        if len > 1 {
            self.emit_impact(
                guard,
                ImpactVmOp::Idx {
                    cached: false,
                    push_path: true,
                    path: full_path,
                },
            );
        }
        self.emit_impact(
            guard,
            ImpactVmOp::Push {
                storage: false,
                value: last.into_cell_state_value(),
            },
        );
        self.emit_impact(
            guard,
            ImpactVmOp::Push {
                storage: true,
                value,
            },
        );
        if init_historic_root {
            self.emit_impact(
                guard,
                ImpactVmOp::Idx {
                    cached: false,
                    push_path: true,
                    path: vec![PathSegment::Static(2)],
                },
            );
            self.emit_impact(guard, ImpactVmOp::Dup { n: 2 });
            self.emit_impact(
                guard,
                ImpactVmOp::Idx {
                    cached: false,
                    push_path: false,
                    path: vec![PathSegment::Static(0)],
                },
            );
            self.emit_impact(guard, ImpactVmOp::Root);
            self.emit_impact(
                guard,
                ImpactVmOp::Push {
                    storage: true,
                    value: ImpactStateValue::Null,
                },
            );
            self.emit_impact(guard, ImpactVmOp::Ins { cached: true, n: 2 });
        }
        self.emit_impact(
            guard,
            ImpactVmOp::Ins {
                cached: false,
                n: 1,
            },
        );
        if len > 1 {
            self.emit_impact(
                guard,
                ImpactVmOp::Ins {
                    cached: true,
                    n: (len - 1) as u8,
                },
            );
        }
    }
}

fn stmts_have_effects(stmts: &[Stmt], program: &Program) -> bool {
    stmts.iter().any(|s| match s {
        Stmt::Const { init, .. } => expr_has_effects(init, program),
        Stmt::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            expr_has_effects(cond, program)
                || stmts_have_effects(then_branch, program)
                || stmts_have_effects(else_branch, program)
        }
        Stmt::ForRange { body, .. } => stmts_have_effects(body, program),
        Stmt::ForEach { iter, body, .. } => {
            expr_has_effects(iter, program) || stmts_have_effects(body, program)
        }
        Stmt::Expr(e) => expr_has_effects(e, program),
        Stmt::Return { value: Some(e), .. } => expr_has_effects(e, program),
        Stmt::Return { value: None, .. } => false,
    })
}

fn expr_has_effects(expr: &Expr, program: &Program) -> bool {
    match &expr.kind {
        ExprKind::LedgerCall { .. }
        | ExprKind::WitnessCall { .. }
        | ExprKind::NativeWitness { .. }
        | ExprKind::ContractCall { .. }
        | ExprKind::Emit { .. }
        | ExprKind::Assert { .. } => true,
        ExprKind::CircuitCall { circuit, args } => {
            !program.circuit(*circuit).pure || args.iter().any(|a| expr_has_effects(a, program))
        }
        ExprKind::Tuple(elems) | ExprKind::Vector(elems) | ExprKind::BytesPack(elems) => {
            elems.iter().any(|e| expr_has_effects(e, program))
        }
        ExprKind::Block { stmts, tail } => {
            stmts_have_effects(stmts, program) || expr_has_effects(tail, program)
        }
        ExprKind::StructLit { fields } => fields.iter().any(|(_, e)| expr_has_effects(e, program)),
        ExprKind::Unary { operand, .. }
        | ExprKind::Cast { expr: operand, .. }
        | ExprKind::Disclose(operand)
        | ExprKind::PersistentHash { arg: operand, .. }
        | ExprKind::Keccak256 { arg: operand, .. }
        | ExprKind::Sha512 { arg: operand, .. }
        | ExprKind::TransientHash { arg: operand, .. }
        | ExprKind::DegradeToTransient(operand)
        | ExprKind::UpgradeFromTransient(operand)
        | ExprKind::FieldInv(operand)
        | ExprKind::EcNeg(operand)
        | ExprKind::EcMulGenerator(operand)
        | ExprKind::HashToCurve { arg: operand, .. }
        | ExprKind::PointCoord { point: operand, .. }
        | ExprKind::Serialize { value: operand, .. }
        | ExprKind::Deserialize { bytes: operand, .. }
        | ExprKind::MerkleTreePathRoot { path: operand, .. }
        | ExprKind::FieldAccess { base: operand, .. }
        | ExprKind::Slice { base: operand, .. }
        | ExprKind::MaybeSome(operand) => expr_has_effects(operand, program),
        ExprKind::EcAdd { lhs: a, rhs: b }
        | ExprKind::EcMul {
            point: a,
            scalar: b,
        }
        | ExprKind::ConstructJubjubPoint { x: a, y: b } => {
            expr_has_effects(a, program) || expr_has_effects(b, program)
        }
        ExprKind::PersistentCommit { value, rand, .. }
        | ExprKind::TransientCommit { value, rand, .. } => {
            expr_has_effects(value, program) || expr_has_effects(rand, program)
        }
        ExprKind::Index { base, index } => {
            expr_has_effects(base, program) || expr_has_effects(index, program)
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            expr_has_effects(lhs, program) || expr_has_effects(rhs, program)
        }
        ExprKind::Ternary {
            cond,
            then_branch,
            else_branch,
        } => {
            expr_has_effects(cond, program)
                || expr_has_effects(then_branch, program)
                || expr_has_effects(else_branch, program)
        }
        ExprKind::IntLit(_)
        | ExprKind::BoolLit(_)
        | ExprKind::BytesLit(_)
        | ExprKind::Default(_)
        | ExprKind::DefaultAdt(_)
        | ExprKind::ParamRef(_)
        | ExprKind::LocalRef(_)
        | ExprKind::EnumVariant { .. }
        | ExprKind::MaybeNone(_) => false,
    }
}
