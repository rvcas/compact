use std::collections::HashMap;

use compact_hir::{
    BinaryOp, Circuit, Expr, ExprKind, LedgerAdt, LedgerOp, LocalId, Program, Stmt, Type, UnaryOp,
};

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
        match ty {
            Type::Field => vec![Self::Field],
            Type::Boolean | Type::Enum(_) => vec![Self::Bytes(1)],
            Type::Uint(bits) => vec![Self::Bytes((*bits).div_ceil(8))],
            Type::Bytes(len) => vec![Self::Bytes(*len)],
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
            | Type::MerkleTreeDigest
            | Type::MerkleTreePathEntry
            | Type::MerkleTreePath(_, _) => program
                .struct_fields_of(ty)
                .unwrap_or_default()
                .iter()
                .flat_map(|(_, fty)| Self::alignment_of(program, fty))
                .collect(),
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

/// Number of native scalar field wires representing a Compact type in ZKIR.
pub fn wire_count(program: &Program, ty: &Type) -> usize {
    match ty {
        Type::Field | Type::Boolean | Type::Uint(_) | Type::Enum(_) | Type::Opaque(_) => 1,
        Type::Bytes(0) => 0,
        Type::Bytes(len) => (*len).div_ceil(FIELD_BYTES) as usize,
        Type::Vector(len, elem) => (*len as usize) * wire_count(program, elem),
        Type::Tuple(elems) => elems.iter().map(|e| wire_count(program, e)).sum(),
        Type::Struct(_)
        | Type::Maybe(_)
        | Type::MerkleTreeDigest
        | Type::MerkleTreePathEntry
        | Type::MerkleTreePath(_, _) => program
            .struct_fields_of(ty)
            .unwrap_or_default()
            .iter()
            .map(|(_, fty)| wire_count(program, fty))
            .sum(),
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
    match ty {
        Type::Field | Type::Opaque(_) => vec![WireConstraint::None],
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
        | Type::MerkleTreeDigest
        | Type::MerkleTreePathEntry
        | Type::MerkleTreePath(_, _) => program
            .struct_fields_of(ty)
            .unwrap_or_default()
            .iter()
            .flat_map(|(_, fty)| wire_constraints(program, fty))
            .collect(),
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
        }
    }

    fn into_cell_state_value(self) -> ImpactStateValue {
        match self {
            Self::Static(seg) => ImpactStateValue::Cell {
                alignment: vec![AlignmentAtom::Bytes(1)],
                values: vec![CircuitVal::Imm(seg as i128)],
            },
            Self::Dynamic { alignment, values } => ImpactStateValue::Cell { alignment, values },
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
            values: vec![CircuitVal::Imm(0); wire_count(program, ty)],
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
    /// `root` (`0x0a`) — pop a Merkle tree and push its root digest cell.
    Root,
    /// `pop` (`0x0b`) — discard top of stack.
    Pop,
    /// `branch` (`0x12`) — pop boolean and skip `skip` VM instructions if true.
    Branch { skip: u32 },
    /// `jmp` (`0x13`) — unconditionally skip `skip` VM instructions.
    Jmp { skip: u32 },
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
            Self::Root => vec![CircuitVal::Imm(0x0a)],
            Self::Pop => vec![CircuitVal::Imm(0x0b)],
            Self::Branch { skip } => vec![CircuitVal::Imm(0x12), CircuitVal::Imm(*skip as i128)],
            Self::Jmp { skip } => vec![CircuitVal::Imm(0x13), CircuitVal::Imm(*skip as i128)],
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
        }
    }
}

/// Flattened SSA instruction inside a proof circuit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CircuitInstr {
    PublicInput {
        guard: Option<CircuitVal>,
        output: CircuitVar,
    },
    PrivateInput {
        guard: Option<CircuitVal>,
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
    Impact {
        guard: CircuitVal,
        op: ImpactVmOp,
    },
    PersistentHash {
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
    /// Input SSA variables (each scalar wire).
    pub inputs: Vec<CircuitVar>,
    /// Number of scalar output wires produced by the final `Output` instruction.
    pub output_count: usize,
    pub instructions: Vec<CircuitInstr>,
}

/// Lowered circuit program containing all exported proof circuits.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CircuitProgram {
    pub circuits: Vec<ProofCircuit>,
}

pub fn lower_to_circuits(program: &Program) -> CircuitProgram {
    let circuits = program
        .proof_circuits()
        .map(|circuit| CircuitLowerer::new(program).lower_root_circuit(circuit))
        .collect();
    CircuitProgram { circuits }
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

    fn lower_root_circuit(mut self, circuit: &Circuit) -> ProofCircuit {
        let mut inputs = Vec::new();
        let mut param_vals: Vec<Vec<CircuitVal>> = Vec::with_capacity(circuit.params.len());
        let mut input_constraints: Vec<(CircuitVar, WireConstraint)> = Vec::new();
        for p in &circuit.params {
            let constraints = wire_constraints(self.program, &p.ty);
            let mut wires = Vec::with_capacity(constraints.len());
            for c in constraints {
                let var = self.fresh_var(&p.name);
                inputs.push(var);
                input_constraints.push((var, c));
                wires.push(CircuitVal::Var(var));
            }
            param_vals.push(wires);
        }
        for (var, c) in input_constraints {
            self.emit_wire_constraint(var, c);
        }

        let ret_vals = self.lower_circuit_body(circuit, &param_vals, &CircuitVal::TRUE);
        let output_count = wire_count(self.program, &circuit.ret_type);
        if output_count > 0 {
            self.instructions.push(CircuitInstr::Output { vals: ret_vals });
        }

        ProofCircuit {
            name: circuit.name.clone(),
            var_names: self.var_names,
            inputs,
            output_count,
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
                    if let Type::Vector(len, elem_ty) = &iter.ty {
                        let elem_width = wire_count(self.program, elem_ty);
                        for i in 0..(*len as usize) {
                            let mut iter_locals = locals.clone();
                            let slice = iter_vals[i * elem_width..(i + 1) * elem_width].to_vec();
                            iter_locals.insert(*local, slice);
                            if let Some(r) =
                                self.lower_stmts(body, param_vals, &mut iter_locals, guard)
                            {
                                ret_vals = Some(r);
                            }
                        }
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
            ExprKind::Default(ty) => vec![CircuitVal::Imm(0); wire_count(self.program, ty)],
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
            ExprKind::MaybeSome(inner) => {
                let mut out = vec![CircuitVal::TRUE];
                out.extend(self.lower_expr(inner, param_vals, locals, guard));
                out
            }
            ExprKind::MaybeNone(inner_ty) => {
                let mut out = vec![CircuitVal::FALSE];
                out.extend(vec![CircuitVal::Imm(0); wire_count(self.program, inner_ty)]);
                out
            }
            ExprKind::Disclose(inner) | ExprKind::Cast { expr: inner, .. } => {
                self.lower_expr_with_hint(inner, param_vals, locals, guard, hint)
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
                            self.instructions.push(CircuitInstr::TestEq {
                                a,
                                b,
                                output: eq,
                            });
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
                    self.instructions.push(CircuitInstr::Assert { cond: cond_val });
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
                let constraints = wire_constraints(self.program, &w.ret_type);
                let mut out = Vec::with_capacity(constraints.len());
                for c in constraints {
                    let v = self.fresh_var(var_hint);
                    self.instructions.push(CircuitInstr::PrivateInput {
                        guard: pi_guard.clone(),
                        output: v,
                    });
                    self.emit_wire_constraint(v, c);
                    out.push(CircuitVal::Var(v));
                }
                out
            }
            ExprKind::PersistentHash { input_ty, arg } => {
                let inputs = self.lower_expr(arg, param_vals, locals, guard);
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
                let mut hash_inputs = bytes_to_wires(b"mdn:lh");
                hash_inputs.extend_from_slice(leaf_vals);

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
                    let vals = self.lower_expr(key_expr, param_vals, locals, guard);
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
                        let count = wire_count(self.program, cell_ty);
                        let mut results = Vec::with_capacity(count);
                        for _ in 0..count {
                            let out = self.fresh_var(&ledger_field.name);
                            self.instructions.push(CircuitInstr::PublicInput {
                                guard: pi_guard.clone(),
                                output: out,
                            });
                            results.push(CircuitVal::Var(out));
                        }
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
                                results: results.clone(),
                            },
                        );
                        results
                    }
                    LedgerOp::CellWrite => {
                        let cell_ty = target_adt
                            .cell_type()
                            .expect("sema validated CellWrite target");
                        let alignment = AlignmentAtom::alignment_of(self.program, cell_ty);
                        let values = self.lower_expr(&args[0], param_vals, locals, guard);
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
                        let elem_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
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
                    LedgerOp::SetInsert => {
                        let LedgerAdt::Set(elem_ty) = target_adt else {
                            unreachable!("sema validated SetInsert target");
                        };
                        let alignment = AlignmentAtom::alignment_of(self.program, elem_ty);
                        let elem_vals = self.lower_expr(&args[0], param_vals, locals, guard);
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
                        self.emit_impact(guard, ImpactVmOp::Ins { cached: false, n: 1 });
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
                        let elem_vals = self.lower_expr(&args[0], param_vals, locals, guard);
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
                        let key_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        let val_align = AlignmentAtom::alignment_of(self.program, val_ty);
                        let count = wire_count(self.program, val_ty);
                        let mut results = Vec::with_capacity(count);
                        for _ in 0..count {
                            let out = self.fresh_var("t");
                            self.instructions.push(CircuitInstr::PublicInput {
                                guard: pi_guard.clone(),
                                output: out,
                            });
                            results.push(CircuitVal::Var(out));
                        }
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
                                results: results.clone(),
                            },
                        );
                        results
                    }
                    LedgerOp::MapInsert => {
                        let LedgerAdt::Map { key, value } = target_adt else {
                            unreachable!("sema validated MapInsert target");
                        };
                        let key_align = AlignmentAtom::alignment_of(self.program, key);
                        let key_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        let val_state = match &args[1].kind {
                            ExprKind::DefaultAdt(val_adt) => {
                                adt_initial_state_value(self.program, val_adt)
                            }
                            _ => {
                                let val_ty = value
                                    .cell_type()
                                    .expect("sema validated MapInsert value type");
                                let val_align = AlignmentAtom::alignment_of(self.program, val_ty);
                                let val_wires =
                                    self.lower_expr(&args[1], param_vals, locals, guard);
                                ImpactStateValue::Cell {
                                    alignment: val_align,
                                    values: val_wires,
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
                        self.emit_impact(guard, ImpactVmOp::Ins { cached: false, n: 1 });
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
                        let key_vals = self.lower_expr(&args[0], param_vals, locals, guard);
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
                        self.emit_impact(guard, ImpactVmOp::Ins { cached: false, n: 1 });
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
                        let elem_align = AlignmentAtom::alignment_of(self.program, elem_ty);
                        let elem_wires = wire_count(self.program, elem_ty);
                        let mut maybe_align = vec![AlignmentAtom::Bytes(1)];
                        maybe_align.extend(elem_align.iter().copied());
                        let total_wires = 1 + elem_wires;
                        let mut results = Vec::with_capacity(total_wires);
                        for _ in 0..total_wires {
                            let out = self.fresh_var("t");
                            self.instructions.push(CircuitInstr::PublicInput {
                                guard: pi_guard.clone(),
                                output: out,
                            });
                            results.push(CircuitVal::Var(out));
                        }
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
                                    values: vec![CircuitVal::Imm(0); total_wires],
                                },
                            },
                        );
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Popeq {
                                cached: true,
                                alignment: maybe_align,
                                results: results.clone(),
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
                    LedgerOp::ListPushFront => {
                        let LedgerAdt::List(elem_ty) = target_adt else {
                            unreachable!("sema validated ListPushFront target");
                        };
                        let val_align = AlignmentAtom::alignment_of(self.program, elem_ty);
                        let val_wires = self.lower_expr(&args[0], param_vals, locals, guard);
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
                    LedgerOp::MerkleTreeInsert => {
                        let LedgerAdt::MerkleTree { value: elem_ty, .. } = target_adt else {
                            unreachable!("sema validated MerkleTreeInsert target");
                        };
                        let alignment = AlignmentAtom::alignment_of(self.program, elem_ty);
                        let item_vals = self.lower_expr(&args[0], param_vals, locals, guard);
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
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 2 });
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
                                storage: true,
                                value: ImpactStateValue::Cell {
                                    alignment: vec![AlignmentAtom::Bytes(32)],
                                    values: vec![CircuitVal::Var(hi), CircuitVal::Var(lo)],
                                },
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Ins { cached: false, n: 1 });
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
                        Vec::new()
                    }
                    LedgerOp::MerkleTreeCheckRoot => {
                        let rt_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
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
                    LedgerOp::HistoricMerkleTreeInsert => {
                        let LedgerAdt::HistoricMerkleTree { value: elem_ty, .. } = target_adt
                        else {
                            unreachable!("sema validated HistoricMerkleTreeInsert target");
                        };
                        let alignment = AlignmentAtom::alignment_of(self.program, elem_ty);
                        let item_vals = self.lower_expr(&args[0], param_vals, locals, guard);
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
                        self.emit_impact(guard, ImpactVmOp::Dup { n: 2 });
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
                                storage: true,
                                value: ImpactStateValue::Cell {
                                    alignment: vec![AlignmentAtom::Bytes(32)],
                                    values: vec![CircuitVal::Var(hi), CircuitVal::Var(lo)],
                                },
                            },
                        );
                        self.emit_impact(guard, ImpactVmOp::Ins { cached: false, n: 1 });
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
                        self.emit_impact(guard, ImpactVmOp::Ins { cached: true, n: 1 });
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
                        self.emit_impact(guard, ImpactVmOp::Ins { cached: false, n: 1 });
                        self.emit_impact(
                            guard,
                            ImpactVmOp::Ins {
                                cached: true,
                                n: depth + 1,
                            },
                        );
                        Vec::new()
                    }
                    LedgerOp::HistoricMerkleTreeCheckRoot => {
                        let rt_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
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
                }
            }
        }
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
        self.emit_impact(guard, ImpactVmOp::Ins { cached: false, n: 1 });
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
        ExprKind::LedgerCall { .. } | ExprKind::WitnessCall { .. } | ExprKind::Assert { .. } => {
            true
        }
        ExprKind::CircuitCall { circuit, args } => {
            !program.circuit(*circuit).pure
                || args.iter().any(|a| expr_has_effects(a, program))
        }
        ExprKind::Tuple(elems) | ExprKind::Vector(elems) => {
            elems.iter().any(|e| expr_has_effects(e, program))
        }
        ExprKind::StructLit { fields } => fields.iter().any(|(_, e)| expr_has_effects(e, program)),
        ExprKind::Unary { operand, .. }
        | ExprKind::Cast { expr: operand, .. }
        | ExprKind::Disclose(operand)
        | ExprKind::PersistentHash { arg: operand, .. }
        | ExprKind::MerkleTreePathRoot { path: operand, .. }
        | ExprKind::FieldAccess { base: operand, .. }
        | ExprKind::MaybeSome(operand) => expr_has_effects(operand, program),
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
