use std::collections::HashMap;

use compact_diagnostics::{CompactDiagnostic, DiagnosticBag};
use compact_hir::{Circuit, CircuitId, Expr, ExprKind, LocalId, Program, Stmt};
use compact_span::{SourceFile, Span};

/// Origin of a private/witness value entering a contract (e.g. an exported circuit parameter).
#[derive(Debug, Clone, PartialEq, Eq)]
struct WitnessOrigin {
    description: String,
    span: Span,
}

/// Abstract taint set for witness-protection-program (WPP) tracking.
#[derive(Debug, Clone, Default)]
struct Taint {
    origins: Vec<WitnessOrigin>,
}

impl Taint {
    fn clean() -> Self {
        Self {
            origins: Vec::new(),
        }
    }

    fn single(description: String, span: Span) -> Self {
        Self {
            origins: vec![WitnessOrigin { description, span }],
        }
    }

    fn is_tainted(&self) -> bool {
        !self.origins.is_empty()
    }

    fn merge(&self, other: &Self) -> Self {
        let mut origins = self.origins.clone();
        for origin in &other.origins {
            if !origins.contains(origin) {
                origins.push(origin.clone());
            }
        }
        Self { origins }
    }
}

/// Enforce Compact's Witness Protection Program (WPP): values originating from
/// exported circuit parameters (and later witnesses/constructors) cannot flow into
/// ledger writes or branch conditions guarding ledger operations unless wrapped in `disclose(...)`.
pub fn check_witness_disclosure(
    file: &SourceFile,
    program: &Program,
    diagnostics: &mut DiagnosticBag,
) {
    for circuit in &program.circuits {
        if !circuit.exported {
            continue;
        }
        let param_taints: Vec<Taint> = circuit
            .params
            .iter()
            .map(|p| {
                Taint::single(
                    format!(
                        "parameter `{}` of exported circuit `{}`",
                        p.name, circuit.name
                    ),
                    p.span,
                )
            })
            .collect();
        let mut checker = WitnessChecker {
            file,
            program,
            diagnostics,
        };
        let _ = checker.check_circuit(circuit, &param_taints, &Taint::clean());
    }
}

struct WitnessChecker<'a> {
    file: &'a SourceFile,
    program: &'a Program,
    diagnostics: &'a mut DiagnosticBag,
}

impl<'a> WitnessChecker<'a> {
    fn report_disclosure(&mut self, span: Span, taint: &Taint, context: &str) {
        if let Some(first) = taint.origins.first() {
            let diag = CompactDiagnostic::error(
                self.file,
                span,
                format!(
                    "potential witness-value disclosure in {context}: {} must be wrapped in `disclose(...)`",
                    first.description
                ),
            )
            .with_secondary_label(first.span, "private witness value originates here")
            .with_help("wrap the value explicitly in `disclose(...)` if publishing it is intentional");
            self.diagnostics.push(diag);
        }
    }

    fn check_circuit(
        &mut self,
        circuit: &Circuit,
        param_taints: &[Taint],
        guard_taint: &Taint,
    ) -> Taint {
        let mut locals: HashMap<LocalId, Taint> = HashMap::new();
        let mut ret_taint = Taint::clean();

        for stmt in &circuit.body {
            match stmt {
                Stmt::Const { local, init, .. } => {
                    let t = self.check_expr(init, param_taints, &locals, guard_taint);
                    locals.insert(*local, t);
                }
                Stmt::Expr(expr) => {
                    let _ = self.check_expr(expr, param_taints, &locals, guard_taint);
                }
                Stmt::Return { value: Some(expr), .. } => {
                    let t = self.check_expr(expr, param_taints, &locals, guard_taint);
                    ret_taint = ret_taint.merge(&t);
                }
                Stmt::Return { value: None, .. } => {}
            }
        }

        ret_taint
    }

    fn check_expr(
        &mut self,
        expr: &Expr,
        param_taints: &[Taint],
        locals: &HashMap<LocalId, Taint>,
        guard_taint: &Taint,
    ) -> Taint {
        match &expr.kind {
            ExprKind::IntLit(_) | ExprKind::BoolLit(_) | ExprKind::EnumVariant { .. } => {
                Taint::clean()
            }
            ExprKind::ParamRef(pid) => param_taints[pid.0 as usize].clone(),
            ExprKind::LocalRef(lid) => locals.get(lid).cloned().unwrap_or_default(),
            ExprKind::Tuple(elems) => elems.iter().fold(Taint::clean(), |acc, e| {
                acc.merge(&self.check_expr(e, param_taints, locals, guard_taint))
            }),
            ExprKind::Unary { operand, .. } => {
                self.check_expr(operand, param_taints, locals, guard_taint)
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                let lt = self.check_expr(lhs, param_taints, locals, guard_taint);
                let rt = self.check_expr(rhs, param_taints, locals, guard_taint);
                lt.merge(&rt)
            }
            ExprKind::Ternary {
                cond,
                then_branch,
                else_branch,
            } => {
                let ct = self.check_expr(cond, param_taints, locals, guard_taint);
                let branch_guard = guard_taint.merge(&ct);
                let tt = self.check_expr(then_branch, param_taints, locals, &branch_guard);
                let et = self.check_expr(else_branch, param_taints, locals, &branch_guard);
                ct.merge(&tt).merge(&et)
            }
            ExprKind::Cast { expr, .. } => self.check_expr(expr, param_taints, locals, guard_taint),
            ExprKind::Assert { cond, .. } => {
                let _ = self.check_expr(cond, param_taints, locals, guard_taint);
                Taint::clean()
            }
            ExprKind::Disclose(inner) => {
                let _ = self.check_expr(inner, param_taints, locals, guard_taint);
                Taint::clean()
            }
            ExprKind::CircuitCall { circuit, args } => {
                let arg_taints: Vec<_> = args
                    .iter()
                    .map(|a| self.check_expr(a, param_taints, locals, guard_taint))
                    .collect();
                let callee = self.program.circuit(*circuit);
                self.check_circuit(callee, &arg_taints, guard_taint)
            }
            ExprKind::LedgerCall { field, op, args } => {
                let field_name = &self.program.ledger_field(*field).name;
                if guard_taint.is_tainted() {
                    self.report_disclosure(
                        expr.span,
                        guard_taint,
                        &format!("ledger operation on `{field_name}` guarded by witness condition"),
                    );
                }
                for arg in args {
                    let arg_taint = self.check_expr(arg, param_taints, locals, guard_taint);
                    if arg_taint.is_tainted() {
                        self.report_disclosure(
                            arg.span,
                            &arg_taint,
                            &format!("ledger `{}.{}`", field_name, op.name()),
                        );
                    }
                }
                // Reading from the public ledger produces a public (untainted) value.
                Taint::clean()
            }
        }
    }
}

/// Helper to check whether a circuit call graph contains recursion.
pub fn reject_recursive_circuits(
    file: &SourceFile,
    program: &Program,
    diagnostics: &mut DiagnosticBag,
) {
    let n = program.circuits.len();
    let mut adj: Vec<Vec<(CircuitId, Span)>> = vec![Vec::new(); n];
    for c in &program.circuits {
        collect_calls_stmts(&c.body, &mut adj[c.id.0 as usize]);
    }

    // 0 = unvisited, 1 = visiting, 2 = done
    let mut state = vec![0u8; n];
    for id in 0..n {
        if state[id] == 0 {
            dfs_cycle(CircuitId(id as u32), &adj, &mut state, file, program, diagnostics);
        }
    }
}

fn dfs_cycle(
    u: CircuitId,
    adj: &[Vec<(CircuitId, Span)>],
    state: &mut [u8],
    file: &SourceFile,
    program: &Program,
    diagnostics: &mut DiagnosticBag,
) {
    state[u.0 as usize] = 1;
    for &(v, call_span) in &adj[u.0 as usize] {
        match state[v.0 as usize] {
            1 => {
                diagnostics.push(CompactDiagnostic::error(
                    file,
                    call_span,
                    format!(
                        "recursive circuit call to `{}` is not allowed",
                        program.circuit(v).name
                    ),
                ));
            }
            0 => dfs_cycle(v, adj, state, file, program, diagnostics),
            _ => {}
        }
    }
    state[u.0 as usize] = 2;
}

fn collect_calls_stmts(stmts: &[Stmt], out: &mut Vec<(CircuitId, Span)>) {
    for stmt in stmts {
        match stmt {
            Stmt::Const { init, .. } => collect_calls_expr(init, out),
            Stmt::Expr(e) => collect_calls_expr(e, out),
            Stmt::Return { value: Some(e), .. } => collect_calls_expr(e, out),
            Stmt::Return { value: None, .. } => {}
        }
    }
}

fn collect_calls_expr(expr: &Expr, out: &mut Vec<(CircuitId, Span)>) {
    match &expr.kind {
        ExprKind::CircuitCall { circuit, args } => {
            out.push((*circuit, expr.span));
            for a in args {
                collect_calls_expr(a, out);
            }
        }
        ExprKind::Tuple(elems) | ExprKind::LedgerCall { args: elems, .. } => {
            for e in elems {
                collect_calls_expr(e, out);
            }
        }
        ExprKind::Unary { operand, .. }
        | ExprKind::Cast { expr: operand, .. }
        | ExprKind::Assert { cond: operand, .. }
        | ExprKind::Disclose(operand) => collect_calls_expr(operand, out),
        ExprKind::Binary { lhs, rhs, .. } => {
            collect_calls_expr(lhs, out);
            collect_calls_expr(rhs, out);
        }
        ExprKind::Ternary {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_calls_expr(cond, out);
            collect_calls_expr(then_branch, out);
            collect_calls_expr(else_branch, out);
        }
        ExprKind::IntLit(_)
        | ExprKind::BoolLit(_)
        | ExprKind::ParamRef(_)
        | ExprKind::LocalRef(_)
        | ExprKind::EnumVariant { .. } => {}
    }
}
