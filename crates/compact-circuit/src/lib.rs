use std::collections::HashMap;

use compact_hir::{
    BinaryOp, Circuit, Expr, ExprKind, LedgerOp, LocalId, Program, Stmt, Type, UnaryOp,
};

/// SSA variable inside a flattened proof circuit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CircuitVar {
    pub id: u32,
}

/// SSA operand: either a variable reference or a signed field-element immediate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CircuitVal {
    Var(CircuitVar),
    Imm(i128),
}

impl CircuitVal {
    pub const TRUE: Self = Self::Imm(1);
    pub const FALSE: Self = Self::Imm(0);

    pub fn is_const_true(self) -> bool {
        matches!(self, Self::Imm(1))
    }
}

/// Alignment atom for Impact VM cell encoding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AlignmentAtom {
    Bytes(u32),
    Field,
}

impl AlignmentAtom {
    pub fn from_type(ty: &Type) -> Self {
        match ty {
            Type::Field => Self::Field,
            Type::Boolean | Type::Enum(_) => Self::Bytes(1),
            Type::Uint(bits) => Self::Bytes((*bits).div_ceil(8)),
            Type::Tuple(_) => Self::Bytes(1),
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
    /// `popeq` / `popeqc` — pop state value from VM stack and constrain equal to `result`.
    Popeq {
        cached: bool,
        alignment: AlignmentAtom,
        result: CircuitVal,
    },
    /// `push` / `pushs` — push a cell-encoded value onto the VM stack.
    Push {
        storage: bool,
        alignment: AlignmentAtom,
        value: CircuitVal,
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
                    // Path segment aligned as `bytes(1)`: [len=1, bytes(1)=1, seg].
                    words.push(CircuitVal::Imm(0x01));
                    words.push(CircuitVal::Imm(0x01));
                    words.push(CircuitVal::Imm(seg as i128));
                }
                words
            }
            Self::Popeq {
                cached,
                alignment,
                result,
            } => {
                let op = if *cached { 0x0d } else { 0x0c };
                vec![
                    CircuitVal::Imm(op),
                    CircuitVal::Imm(0x01),
                    CircuitVal::Imm(alignment.as_imm()),
                    *result,
                ]
            }
            Self::Push {
                storage,
                alignment,
                value,
            } => {
                let op = if *storage { 0x11 } else { 0x10 };
                vec![
                    CircuitVal::Imm(op),
                    CircuitVal::Imm(0x01), // StateValue::Cell tag
                    CircuitVal::Imm(0x01), // 1 alignment atom
                    CircuitVal::Imm(alignment.as_imm()),
                    *value,
                ]
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
    Impact {
        guard: CircuitVal,
        op: ImpactVmOp,
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
        let mut inputs = Vec::with_capacity(circuit.params.len());
        let mut param_vals = Vec::with_capacity(circuit.params.len());
        for p in &circuit.params {
            let var = self.fresh_var(&p.name);
            inputs.push(var);
            param_vals.push(CircuitVal::Var(var));
        }

        let ret_val = self.lower_circuit_body(circuit, &param_vals, CircuitVal::TRUE);
        let output_count = if circuit.ret_type.is_unit() {
            0
        } else {
            if let Some(val) = ret_val {
                self.instructions.push(CircuitInstr::Output {
                    vals: vec![val],
                });
            }
            1
        };

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
        param_vals: &[CircuitVal],
        guard: CircuitVal,
    ) -> Option<CircuitVal> {
        let mut locals: HashMap<LocalId, CircuitVal> = HashMap::new();
        let mut ret_val = None;

        for stmt in &circuit.body {
            match stmt {
                Stmt::Const { local, init, .. } => {
                    if let Some(val) = self.lower_expr(init, param_vals, &locals, guard) {
                        locals.insert(*local, val);
                    }
                }
                Stmt::Expr(expr) => {
                    let _ = self.lower_expr(expr, param_vals, &locals, guard);
                }
                Stmt::Return { value, .. } => {
                    ret_val = value
                        .as_ref()
                        .and_then(|e| self.lower_expr(e, param_vals, &locals, guard));
                }
            }
        }

        ret_val
    }

    fn combine_guard(&mut self, outer: CircuitVal, cond: CircuitVal) -> CircuitVal {
        if outer.is_const_true() {
            return cond;
        }
        let out = self.fresh_var("t");
        self.instructions.push(CircuitInstr::CondSelect {
            bit: outer,
            a: cond,
            b: CircuitVal::FALSE,
            output: out,
        });
        CircuitVal::Var(out)
    }

    fn lower_expr(
        &mut self,
        expr: &Expr,
        param_vals: &[CircuitVal],
        locals: &HashMap<LocalId, CircuitVal>,
        guard: CircuitVal,
    ) -> Option<CircuitVal> {
        match &expr.kind {
            ExprKind::IntLit(v) => Some(CircuitVal::Imm(*v as i128)),
            ExprKind::BoolLit(b) => Some(CircuitVal::Imm(i128::from(*b))),
            ExprKind::EnumVariant { variant_idx, .. } => Some(CircuitVal::Imm(*variant_idx as i128)),
            ExprKind::ParamRef(pid) => Some(param_vals[pid.0 as usize]),
            ExprKind::LocalRef(lid) => locals.get(lid).copied(),
            ExprKind::Tuple(elems) => {
                for e in elems {
                    let _ = self.lower_expr(e, param_vals, locals, guard);
                }
                None
            }
            ExprKind::Disclose(inner) | ExprKind::Cast { expr: inner, .. } => {
                self.lower_expr(inner, param_vals, locals, guard)
            }
            ExprKind::Unary { op, operand } => {
                let val = self.lower_expr(operand, param_vals, locals, guard)?;
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
                Some(CircuitVal::Var(out))
            }
            ExprKind::Binary { op, lhs, rhs } => {
                let l = self.lower_expr(lhs, param_vals, locals, guard)?;
                let r = self.lower_expr(rhs, param_vals, locals, guard)?;
                match op {
                    BinaryOp::Eq => {
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::TestEq {
                            a: l,
                            b: r,
                            output: out,
                        });
                        Some(CircuitVal::Var(out))
                    }
                    BinaryOp::Neq => {
                        let eq = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::TestEq {
                            a: l,
                            b: r,
                            output: eq,
                        });
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::Not {
                            a: CircuitVal::Var(eq),
                            output: out,
                        });
                        Some(CircuitVal::Var(out))
                    }
                    BinaryOp::Add => {
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::Add {
                            a: l,
                            b: r,
                            output: out,
                        });
                        Some(CircuitVal::Var(out))
                    }
                    BinaryOp::Sub => {
                        let neg = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::Neg {
                            a: r,
                            output: neg,
                        });
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::Add {
                            a: l,
                            b: CircuitVal::Var(neg),
                            output: out,
                        });
                        Some(CircuitVal::Var(out))
                    }
                }
            }
            ExprKind::Ternary {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond_val = self.lower_expr(cond, param_vals, locals, guard)?;
                let then_guard = self.combine_guard(guard, cond_val);
                let then_val = self.lower_expr(then_branch, param_vals, locals, then_guard);

                let else_guard = if expr_has_effects(else_branch, self.program) {
                    let not_cond = self.fresh_var("t");
                    self.instructions.push(CircuitInstr::Not {
                        a: cond_val,
                        output: not_cond,
                    });
                    self.combine_guard(guard, CircuitVal::Var(not_cond))
                } else {
                    guard
                };
                let else_val = self.lower_expr(else_branch, param_vals, locals, else_guard);

                match (then_val, else_val) {
                    (Some(a), Some(b)) => {
                        let out = self.fresh_var("t");
                        self.instructions.push(CircuitInstr::CondSelect {
                            bit: cond_val,
                            a,
                            b,
                            output: out,
                        });
                        Some(CircuitVal::Var(out))
                    }
                    _ => None,
                }
            }
            ExprKind::Assert { cond, .. } => {
                let cond_val = self.lower_expr(cond, param_vals, locals, guard)?;
                if guard.is_const_true() {
                    self.instructions.push(CircuitInstr::Assert { cond: cond_val });
                } else {
                    let guarded = self.fresh_var("t");
                    self.instructions.push(CircuitInstr::CondSelect {
                        bit: guard,
                        a: cond_val,
                        b: CircuitVal::TRUE,
                        output: guarded,
                    });
                    self.instructions.push(CircuitInstr::Assert {
                        cond: CircuitVal::Var(guarded),
                    });
                }
                None
            }
            // Inline helper circuit calls directly into the caller!
            ExprKind::CircuitCall { circuit, args } => {
                let mut lowered_args = Vec::with_capacity(args.len());
                for arg in args {
                    if let Some(v) = self.lower_expr(arg, param_vals, locals, guard) {
                        lowered_args.push(v);
                    }
                }
                let callee = self.program.circuit(*circuit);
                self.lower_circuit_body(callee, &lowered_args, guard)
            }
            ExprKind::LedgerCall { field, op, args } => {
                let ledger_field = self.program.ledger_field(*field);
                let path = ledger_field.path.clone();
                let depth = path.len() as u8;
                let alignment = AlignmentAtom::from_type(&ledger_field.value_type);
                match op {
                    LedgerOp::CellRead => {
                        let out = self.fresh_var(&ledger_field.name);
                        let pi_guard = if guard.is_const_true() {
                            None
                        } else {
                            Some(guard)
                        };
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
                            output: out,
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard,
                            op: ImpactVmOp::Dup { n: 0 },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard,
                            op: ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path,
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard,
                            op: ImpactVmOp::Popeq {
                                cached: false,
                                alignment,
                                result: CircuitVal::Var(out),
                            },
                        });
                        Some(CircuitVal::Var(out))
                    }
                    LedgerOp::CellWrite => {
                        let val = self.lower_expr(&args[0], param_vals, locals, guard)?;
                        self.instructions.push(CircuitInstr::Impact {
                            guard,
                            op: ImpactVmOp::Push {
                                storage: false,
                                alignment: AlignmentAtom::Bytes(1),
                                value: CircuitVal::Imm(path[0] as i128),
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard,
                            op: ImpactVmOp::Push {
                                storage: true,
                                alignment,
                                value: val,
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard,
                            op: ImpactVmOp::Ins {
                                cached: false,
                                n: depth,
                            },
                        });
                        None
                    }
                    LedgerOp::CounterIncrement => {
                        let immediate = match args.first().map(|a| &a.kind) {
                            Some(ExprKind::IntLit(v)) => *v as u16,
                            _ => unreachable!("sema validated Counter.increment immediate"),
                        };
                        self.instructions.push(CircuitInstr::Impact {
                            guard,
                            op: ImpactVmOp::Idx {
                                cached: false,
                                push_path: true,
                                path,
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard,
                            op: ImpactVmOp::Addi { immediate },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard,
                            op: ImpactVmOp::Ins {
                                cached: true,
                                n: depth,
                            },
                        });
                        None
                    }
                    LedgerOp::CounterDecrement => {
                        let immediate = match args.first().map(|a| &a.kind) {
                            Some(ExprKind::IntLit(v)) => *v as u16,
                            _ => unreachable!("sema validated Counter.decrement immediate"),
                        };
                        self.instructions.push(CircuitInstr::Impact {
                            guard,
                            op: ImpactVmOp::Idx {
                                cached: false,
                                push_path: true,
                                path,
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard,
                            op: ImpactVmOp::Subi { immediate },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard,
                            op: ImpactVmOp::Ins {
                                cached: true,
                                n: depth,
                            },
                        });
                        None
                    }
                    LedgerOp::CounterRead => {
                        let out = self.fresh_var(&ledger_field.name);
                        let pi_guard = if guard.is_const_true() {
                            None
                        } else {
                            Some(guard)
                        };
                        self.instructions.push(CircuitInstr::PublicInput {
                            guard: pi_guard,
                            output: out,
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard,
                            op: ImpactVmOp::Dup { n: 0 },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard,
                            op: ImpactVmOp::Idx {
                                cached: false,
                                push_path: false,
                                path,
                            },
                        });
                        self.instructions.push(CircuitInstr::Impact {
                            guard,
                            op: ImpactVmOp::Popeq {
                                cached: true,
                                alignment: AlignmentAtom::Bytes(8),
                                result: CircuitVal::Var(out),
                            },
                        });
                        Some(CircuitVal::Var(out))
                    }
                }
            }
        }
    }
}

fn expr_has_effects(expr: &Expr, program: &Program) -> bool {
    match &expr.kind {
        ExprKind::LedgerCall { .. } | ExprKind::Assert { .. } => true,
        ExprKind::CircuitCall { circuit, args } => {
            !program.circuit(*circuit).pure
                || args.iter().any(|a| expr_has_effects(a, program))
        }
        ExprKind::Tuple(elems) => elems.iter().any(|e| expr_has_effects(e, program)),
        ExprKind::Unary { operand, .. }
        | ExprKind::Cast { expr: operand, .. }
        | ExprKind::Disclose(operand) => expr_has_effects(operand, program),
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
        | ExprKind::ParamRef(_)
        | ExprKind::LocalRef(_)
        | ExprKind::EnumVariant { .. } => false,
    }
}
