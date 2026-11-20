use compact_hir::{Circuit, Expr, ExprKind, LedgerOp, Program, Stmt};

/// A single Impact VM instruction lowered for a ledger operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImpactVmOp {
    /// `idx` / `idxc` / `idxp` / `idxpc` — index into public ledger state along `path`.
    Idx {
        cached: bool,
        push_path: bool,
        path: Vec<u32>,
    },
    /// `addi` — add immediate `Uint<16>` to counter cell on stack.
    Addi { immediate: u16 },
    /// `subi` — subtract immediate `Uint<16>` from counter cell on stack.
    Subi { immediate: u16 },
    /// `ins` / `insc` — write updated value back up `n` path levels.
    Ins { cached: bool, n: u8 },
}

impl ImpactVmOp {
    /// Assemble this Impact VM instruction into the sequence of raw field-element
    /// operands emitted in a ZKIR v3 `impact` instruction (matching `reduce-to-zkir.ss`).
    pub fn assemble(&self) -> Vec<u64> {
        match self {
            Self::Idx {
                cached,
                push_path,
                path,
            } => {
                debug_assert!(!path.is_empty());
                let hi: u64 = match (*push_path, *cached) {
                    (false, false) => 0x5,
                    (false, true) => 0x6,
                    (true, false) => 0x7,
                    (true, true) => 0x8,
                };
                let lo = (path.len() - 1) as u64;
                let mut words = vec![(hi << 4) | lo];
                for &seg in path {
                    // Each path element is aligned as `bytes(1)` with 1 alignment atom:
                    // [length=1, alignment=bytes(1), value=seg].
                    words.push(0x01);
                    words.push(0x01);
                    words.push(seg as u64);
                }
                words
            }
            Self::Addi { immediate } => vec![0x0e, *immediate as u64],
            Self::Subi { immediate } => vec![0x0f, *immediate as u64],
            Self::Ins { cached, n } => {
                let hi: u64 = if *cached { 0xa } else { 0x9 };
                vec![(hi << 4) | (*n as u64)]
            }
        }
    }
}

/// Flattened instruction inside a proof circuit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CircuitInstr {
    Impact {
        guard: bool,
        op: ImpactVmOp,
    },
}

/// Flattened representation of an exported proof circuit ready for ZKIR codegen.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofCircuit {
    pub name: String,
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
        .map(|circuit| lower_circuit(program, circuit))
        .collect();
    CircuitProgram { circuits }
}

fn lower_circuit(program: &Program, circuit: &Circuit) -> ProofCircuit {
    let mut instructions = Vec::new();
    for stmt in &circuit.body {
        match stmt {
            Stmt::Expr(expr) => lower_expr(program, expr, &mut instructions),
            Stmt::Return {
                value: Some(expr), ..
            } => lower_expr(program, expr, &mut instructions),
            Stmt::Return { value: None, .. } => {}
        }
    }
    ProofCircuit {
        name: circuit.name.clone(),
        instructions,
    }
}

fn lower_expr(program: &Program, expr: &Expr, out: &mut Vec<CircuitInstr>) {
    if let ExprKind::LedgerCall { field, op, args } = &expr.kind {
        let ledger_field = program.ledger_field(*field);
        let path = ledger_field.path.clone();
        let depth = path.len() as u8;
        match op {
            LedgerOp::CounterIncrement => {
                let immediate = match args.first().map(|a| &a.kind) {
                    Some(ExprKind::IntLit(v)) => *v as u16,
                    _ => unreachable!("HIR validated Counter.increment immediate"),
                };
                out.push(CircuitInstr::Impact {
                    guard: true,
                    op: ImpactVmOp::Idx {
                        cached: false,
                        push_path: true,
                        path,
                    },
                });
                out.push(CircuitInstr::Impact {
                    guard: true,
                    op: ImpactVmOp::Addi { immediate },
                });
                out.push(CircuitInstr::Impact {
                    guard: true,
                    op: ImpactVmOp::Ins {
                        cached: true,
                        n: depth,
                    },
                });
            }
            LedgerOp::CounterDecrement => {
                let immediate = match args.first().map(|a| &a.kind) {
                    Some(ExprKind::IntLit(v)) => *v as u16,
                    _ => unreachable!("HIR validated Counter.decrement immediate"),
                };
                out.push(CircuitInstr::Impact {
                    guard: true,
                    op: ImpactVmOp::Idx {
                        cached: false,
                        push_path: true,
                        path,
                    },
                });
                out.push(CircuitInstr::Impact {
                    guard: true,
                    op: ImpactVmOp::Subi { immediate },
                });
                out.push(CircuitInstr::Impact {
                    guard: true,
                    op: ImpactVmOp::Ins {
                        cached: true,
                        n: depth,
                    },
                });
            }
            LedgerOp::CounterRead => {
                out.push(CircuitInstr::Impact {
                    guard: true,
                    op: ImpactVmOp::Idx {
                        cached: false,
                        push_path: false,
                        path,
                    },
                });
            }
        }
    }
}
