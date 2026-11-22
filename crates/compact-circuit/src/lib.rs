use std::collections::HashMap;

use compact_hir::{
    BinaryOp, Circuit, Expr, ExprKind, LedgerOp, LocalId, Program, Stmt, Type, UnaryOp,
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

/// A single Impact VM instruction lowered for a ledger operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImpactVmOp {
    /// `dup n` — duplicate stack item at depth `n`.
    Dup { n: u8 },
    /// `idx` / `idxc` / `idxp` / `idxpc` — index into public ledger state along `path`.
    Idx {
        cached: bool,
        push_path: bool,
        path: Vec<u32>,
    },
    /// `popeq` / `popeqc` — pop state value from VM stack and constrain equal to `results`.
    Popeq {
        cached: bool,
        alignment: Vec<AlignmentAtom>,
        results: Vec<CircuitVal>,
    },
    /// `push` / `pushs` — push a cell-encoded value onto the VM stack.
    Push {
        storage: bool,
        alignment: Vec<AlignmentAtom>,
        values: Vec<CircuitVal>,
    },
    /// `push` / `pushs` with a `StateValue::Null` payload (`0x00`).
    PushNull { storage: bool },
    /// `eq` (`0x02`) — pop two stack items and push equality boolean.
    Eq,
    /// `root` (`0x0a`) — pop a Merkle tree and push its root digest cell.
    Root,
    /// `member` (`0x18`) — pop key & set/map and push membership boolean.
    Member,
    /// `rem` (`0x1a` / `0x1b`) — remove key from set/map.
    Rem { cached: bool },
    /// `addi` — add immediate `Uint<16>` to counter cell on stack.
    Addi { immediate: u16 },
    /// `subi` — subtract immediate `Uint<16>` from counter cell on stack.
    Subi { immediate: u16 },
    /// `ins` / `insc` — write updated value back up `n` path levels.
    Ins { cached: bool, n: u8 },
}

impl ImpactVmOp {
    /// Assemble this Impact VM instruction into the sequence of ZKIR `impact` operands
    /// (matching upstream `reduce-to-zkir.ss`).
    pub fn assemble(&self) -> Vec<CircuitVal> {
        match self {
            Self::Dup { n } => vec![CircuitVal::Imm(0x30 | (*n as i128))],
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
                for &seg in path {
                    words.push(CircuitVal::Imm(0x01));
                    words.push(CircuitVal::Imm(0x01));
                    words.push(CircuitVal::Imm(seg as i128));
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
            Self::Push {
                storage,
                alignment,
                values,
            } => {
                let op = if *storage { 0x11 } else { 0x10 };
                let mut words = vec![
                    CircuitVal::Imm(op),
                    CircuitVal::Imm(0x01), // StateValue::Cell tag
                    CircuitVal::Imm(alignment.len() as i128),
                ];
                for atom in alignment {
                    words.push(CircuitVal::Imm(atom.as_imm()));
                }
                words.extend(values.iter().cloned());
                words
            }
            Self::PushNull { storage } => {
                let op = if *storage { 0x11 } else { 0x10 };
                vec![CircuitVal::Imm(op), CircuitVal::Imm(0x00)]
            }
            Self::Eq => vec![CircuitVal::Imm(0x02)],
            Self::Root => vec![CircuitVal::Imm(0x0a)],
            Self::Member => vec![CircuitVal::Imm(0x18)],
            Self::Rem { cached } => vec![CircuitVal::Imm(if *cached { 0x1b } else { 0x1a })],
            Self::Addi { immediate } => {
                vec![CircuitVal::Imm(0x0e), CircuitVal::Imm(*immediate as i128)]
            }
            Self::Subi { immediate } => {
                vec![CircuitVal::Imm(0x0f), CircuitVal::Imm(*immediate as i128)]
            }
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
            ExprKind::LedgerCall { field, op, args } => {
                let ledger_field = self.program.ledger_field(*field);
                let path = ledger_field.path.clone();
                let depth = path.len() as u8;
                let alignment = AlignmentAtom::alignment_of(self.program, &ledger_field.value_type);
                match op {
                    LedgerOp::CellRead => {
                        let count = wire_count(self.program, &ledger_field.value_type);
                        let pi_guard = if guard.is_const_true() {
                            None
                        } else {
                            Some(guard.clone())
                        };
                        let mut results = Vec::with_capacity(count);
                        for _ in 0..count {
                            let out = self.fresh_var(&ledger_field.name);
                            self.instructions.push(CircuitInstr::PublicInput {
                                guard: pi_guard.clone(),
                                output: out,
                            });
                            results.push(CircuitVal::Var(out));
                        }
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Dup { n: 0 },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path,
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Popeq {
                                cached: false,
                                alignment,
                                results: results.clone(),
                            },
                        });
                        results
                    }
                    LedgerOp::CellWrite => {
                        let values = self.lower_expr(&args[0], param_vals, locals, guard);
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Push {
                                storage: false,
                                alignment: vec![AlignmentAtom::Bytes(1)],
                                values: vec![CircuitVal::Imm(path[0] as i128)],
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Push {
                                storage: true,
                                alignment,
                                values,
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Ins {
                                cached: false,
                                n: depth,
                            },
                        });
                        Vec::new()
                    }
                    LedgerOp::CounterIncrement => {
                        let immediate = match args.first().map(|a| &a.kind) {
                            Some(ExprKind::IntLit(v)) => *v as u16,
                            _ => unreachable!("sema validated Counter.increment immediate"),
                        };
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Idx {
                                cached: false,
                                push_path: true,
                                path,
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Addi { immediate },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Ins {
                                cached: true,
                                n: depth,
                            },
                        });
                        Vec::new()
                    }
                    LedgerOp::CounterDecrement => {
                        let immediate = match args.first().map(|a| &a.kind) {
                            Some(ExprKind::IntLit(v)) => *v as u16,
                            _ => unreachable!("sema validated Counter.decrement immediate"),
                        };
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Idx {
                                cached: false,
                                push_path: true,
                                path,
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Subi { immediate },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Ins {
                                cached: true,
                                n: depth,
                            },
                        });
                        Vec::new()
                    }
                    LedgerOp::CounterRead => {
                        let out = self.fresh_var(&ledger_field.name);
                        let pi_guard = if guard.is_const_true() {
                            None
                        } else {
                            Some(guard.clone())
                        };
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
                            output: out,
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Dup { n: 0 },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path,
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Popeq {
                                cached: true,
                                alignment: vec![AlignmentAtom::Bytes(8)],
                                results: vec![CircuitVal::Var(out)],
                            },
                        });
                        vec![CircuitVal::Var(out)]
                    }
                    LedgerOp::SetMember => {
                        let elem_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        let out = self.fresh_var("t");
                        let pi_guard = if guard.is_const_true() {
                            None
                        } else {
                            Some(guard.clone())
                        };
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
                            output: out,
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Dup { n: 0 },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path,
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Push {
                                storage: false,
                                alignment,
                                values: elem_vals,
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Member,
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Popeq {
                                cached: true,
                                alignment: vec![AlignmentAtom::Bytes(1)],
                                results: vec![CircuitVal::Var(out)],
                            },
                        });
                        vec![CircuitVal::Var(out)]
                    }
                    LedgerOp::SetInsert => {
                        let elem_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Idx {
                                cached: false,
                                push_path: true,
                                path,
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Push {
                                storage: false,
                                alignment,
                                values: elem_vals,
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::PushNull { storage: true },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Ins {
                                cached: false,
                                n: 1,
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Ins {
                                cached: true,
                                n: depth,
                            },
                        });
                        Vec::new()
                    }
                    LedgerOp::SetRemove => {
                        let elem_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Idx {
                                cached: false,
                                push_path: true,
                                path,
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Push {
                                storage: false,
                                alignment,
                                values: elem_vals,
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Rem { cached: false },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Ins {
                                cached: true,
                                n: depth,
                            },
                        });
                        Vec::new()
                    }
                    LedgerOp::MerkleTreeInsert => {
                        let item_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        // Compute leaf hash: `persistentHash(LeafPreimage { "mdn:lh", item })`
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

                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Idx {
                                cached: false,
                                push_path: true,
                                path,
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Idx {
                                cached: false,
                                push_path: true,
                                path: vec![0],
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Dup { n: 2 },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: vec![1],
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Push {
                                storage: true,
                                alignment: vec![AlignmentAtom::Bytes(32)],
                                values: vec![CircuitVal::Var(hi), CircuitVal::Var(lo)],
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Ins {
                                cached: false,
                                n: 1,
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Ins {
                                cached: true,
                                n: 1,
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Idx {
                                cached: false,
                                push_path: true,
                                path: vec![1],
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Addi { immediate: 1 },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Ins {
                                cached: true,
                                n: depth + 1,
                            },
                        });
                        Vec::new()
                    }
                    LedgerOp::MerkleTreeCheckRoot => {
                        let rt_vals = self.lower_expr(&args[0], param_vals, locals, guard);
                        let out = self.fresh_var("t");
                        let pi_guard = if guard.is_const_true() {
                            None
                        } else {
                            Some(guard.clone())
                        };
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
                            output: out,
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Dup { n: 0 },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path,
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path: vec![0],
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Root,
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Push {
                                storage: false,
                                alignment: vec![AlignmentAtom::Field],
                                values: rt_vals,
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Eq,
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard: guard.clone(),
                            op: ImpactVmOp::Popeq {
                                cached: true,
                                alignment: vec![AlignmentAtom::Bytes(1)],
                                results: vec![CircuitVal::Var(out)],
                            },
                        });
                        vec![CircuitVal::Var(out)]
                    }
                }
            }
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
        | ExprKind::ParamRef(_)
        | ExprKind::LocalRef(_)
        | ExprKind::EnumVariant { .. }
        | ExprKind::MaybeNone(_) => false,
    }
}
