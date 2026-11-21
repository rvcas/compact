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
}

impl AlignmentAtom {
    /// Flatten a Compact type into its Impact/ZKIR alignment atom sequence.
    pub fn alignment_of(ty: &Type) -> Vec<Self> {
        match ty {
            Type::Field => vec![Self::Field],
            Type::Boolean | Type::Enum(_) => vec![Self::Bytes(1)],
            Type::Uint(bits) => vec![Self::Bytes((*bits).div_ceil(8))],
            Type::Bytes(len) => vec![Self::Bytes(*len)],
            Type::Vector(len, elem) => {
                let single = Self::alignment_of(elem);
                let mut out = Vec::with_capacity(single.len() * (*len as usize));
                for _ in 0..*len {
                    out.extend_from_slice(&single);
                }
                out
            }
            Type::Tuple(elems) => elems.iter().flat_map(Self::alignment_of).collect(),
            Type::Maybe(inner) => {
                let mut out = vec![Self::Bytes(1)];
                out.extend(Self::alignment_of(inner));
                out
            }
        }
    }

    /// Encode alignment atom as a ZKIR Impact VM immediate (`abytes(n)` -> `n`, `afield` -> `-2`).
    pub fn as_imm(self) -> i128 {
        match self {
            Self::Bytes(n) => n as i128,
            Self::Field => -2,
        }
    }
}

/// Number of native scalar field wires representing a Compact type in ZKIR.
pub fn wire_count(ty: &Type) -> usize {
    match ty {
        Type::Field | Type::Boolean | Type::Uint(_) | Type::Enum(_) => 1,
        Type::Bytes(0) => 0,
        Type::Bytes(len) => (*len).div_ceil(FIELD_BYTES) as usize,
        Type::Vector(len, elem) => (*len as usize) * wire_count(elem),
        Type::Tuple(elems) => elems.iter().map(wire_count).sum(),
        Type::Maybe(inner) => 1 + wire_count(inner),
    }
}

/// Bit widths for each wire of a type when witnessing private inputs (`None` means unconstrained full field).
fn wire_bit_constraints(ty: &Type) -> Vec<Option<u32>> {
    match ty {
        Type::Field => vec![None],
        Type::Boolean => vec![Some(1)],
        Type::Uint(bits) => vec![Some(*bits)],
        Type::Enum(_) => vec![Some(8)],
        Type::Bytes(0) => Vec::new(),
        Type::Bytes(len) => {
            let full = *len / FIELD_BYTES;
            let rem = *len % FIELD_BYTES;
            let mut widths = Vec::new();
            if rem > 0 {
                widths.push(Some(rem * 8));
            }
            for _ in 0..full {
                widths.push(Some(FIELD_BYTES * 8));
            }
            widths
        }
        Type::Vector(len, elem) => {
            let single = wire_bit_constraints(elem);
            let mut out = Vec::with_capacity(single.len() * (*len as usize));
            for _ in 0..*len {
                out.extend_from_slice(&single);
            }
            out
        }
        Type::Tuple(elems) => elems.iter().flat_map(wire_bit_constraints).collect(),
        Type::Maybe(inner) => {
            let mut out = vec![Some(1)];
            out.extend(wire_bit_constraints(inner));
            out
        }
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
    ConstrainBits {
        val: CircuitVal,
        bits: u32,
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

    fn lower_root_circuit(mut self, circuit: &Circuit) -> ProofCircuit {
        let mut inputs = Vec::new();
        let mut param_vals: Vec<Vec<CircuitVal>> = Vec::with_capacity(circuit.params.len());
        for p in &circuit.params {
            let count = wire_count(&p.ty);
            let mut wires = Vec::with_capacity(count);
            for _ in 0..count {
                let var = self.fresh_var(&p.name);
                inputs.push(var);
                wires.push(CircuitVal::Var(var));
            }
            param_vals.push(wires);
        }

        let ret_vals = self.lower_circuit_body(circuit, &param_vals, &CircuitVal::TRUE);
        let output_count = wire_count(&circuit.ret_type);
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
        let mut ret_vals = Vec::new();

        for stmt in &circuit.body {
            match stmt {
                Stmt::Const {
                    local, name, init, ..
                } => {
                    let vals = self.lower_expr_with_hint(init, param_vals, &locals, guard, Some(name));
                    locals.insert(*local, vals);
                }
                Stmt::Expr(expr) => {
                    let _ = self.lower_expr(expr, param_vals, &locals, guard);
                }
                Stmt::Return { value, .. } => {
                    ret_vals = value
                        .as_ref()
                        .map(|e| self.lower_expr(e, param_vals, &locals, guard))
                        .unwrap_or_default();
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
            ExprKind::Default(ty) => vec![CircuitVal::Imm(0); wire_count(ty)],
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
            ExprKind::MaybeSome(inner) => {
                let mut out = vec![CircuitVal::TRUE];
                out.extend(self.lower_expr(inner, param_vals, locals, guard));
                out
            }
            ExprKind::MaybeNone(inner_ty) => {
                let mut out = vec![CircuitVal::FALSE];
                out.extend(vec![CircuitVal::Imm(0); wire_count(inner_ty)]);
                out
            }
            ExprKind::Disclose(inner) | ExprKind::Cast { expr: inner, .. } => {
                self.lower_expr_with_hint(inner, param_vals, locals, guard, hint)
            }
            ExprKind::Unary { op, operand } => {
                let vals = self.lower_expr(operand, param_vals, locals, guard);
                let val = vals.into_iter().next().unwrap_or(CircuitVal::FALSE);
                let out = self.fresh_var("t");
                match op {
                    UnaryOp::Not => self.instructions.push(CircuitInstr::Not {
                        a: val,
                        output: out,
                    }),
                    UnaryOp::Neg => self.instructions.push(CircuitInstr::Neg {
                        a: val,
                        output: out,
                    }),
                }
                vec![CircuitVal::Var(out)]
            }
            ExprKind::Binary { op, lhs, rhs } => {
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
                        let mut acc = eq_vars.into_iter().reduce(|acc, next| {
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
                            let neg = self.fresh_var("t");
                            self.instructions.push(CircuitInstr::Not {
                                a: acc,
                                output: neg,
                            });
                            acc = CircuitVal::Var(neg);
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
                let then_guard = self.combine_guard(guard, &cond_val);
                let then_vals = self.lower_expr(then_branch, param_vals, locals, &then_guard);

                let else_guard = if expr_has_effects(else_branch, self.program) {
                    let not_cond = self.fresh_var("t");
                    self.instructions.push(CircuitInstr::Not {
                        a: cond_val.clone(),
                        output: not_cond,
                    });
                    self.combine_guard(guard, &CircuitVal::Var(not_cond))
                } else {
                    guard.clone()
                };
                let else_vals = self.lower_expr(else_branch, param_vals, locals, &else_guard);

                let mut out = Vec::with_capacity(then_vals.len());
                for (a, b) in then_vals.into_iter().zip(else_vals) {
                    if a == b {
                        out.push(a);
                    } else if a.is_const_true() && b.is_const_false() {
                        // `cond ? 1 : 0` simplifies directly to `cond`.
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
                let var_hint = hint.unwrap_or("w");
                let pi_guard = if guard.is_const_true() {
                    None
                } else {
                    Some(guard.clone())
                };
                let constraints = wire_bit_constraints(&w.ret_type);
                let mut out = Vec::with_capacity(constraints.len());
                for bits in constraints {
                    let v = self.fresh_var(var_hint);
                    self.instructions.push(CircuitInstr::PrivateInput {
                        guard: pi_guard.clone(),
                        output: v,
                    });
                    if let Some(b) = bits {
                        self.instructions.push(CircuitInstr::ConstrainBits {
                            val: CircuitVal::Var(v),
                            bits: b,
                        });
                    }
                    out.push(CircuitVal::Var(v));
                }
                out
            }
            ExprKind::PersistentHash { input_ty, arg } => {
                let inputs = self.lower_expr(arg, param_vals, locals, guard);
                let alignment = AlignmentAtom::alignment_of(input_ty);
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
                let alignment = AlignmentAtom::alignment_of(&ledger_field.value_type);
                match op {
                    LedgerOp::CellRead => {
                        let count = wire_count(&ledger_field.value_type);
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
                }
            }
        }
    }
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
        ExprKind::Unary { operand, .. }
        | ExprKind::Cast { expr: operand, .. }
        | ExprKind::Disclose(operand)
        | ExprKind::PersistentHash { arg: operand, .. }
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
