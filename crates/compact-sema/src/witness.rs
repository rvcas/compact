use std::collections::HashMap;

use compact_diagnostics::{CompactDiagnostic, DiagnosticBag};
use compact_hir::{BinaryOp, CircuitId, Expr, ExprKind, LocalId, Program, Stmt};
use compact_span::{SourceFile, Span};

/// Origin of a private/witness value entering a contract (exported circuit params,
/// constructor params, or witness return values).
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
/// exported circuit parameters, constructor parameters, or witness return values
/// cannot flow into ledger writes or branch conditions guarding ledger operations
/// unless explicitly wrapped in `disclose(...)`.
pub fn check_witness_disclosure(
    file: &SourceFile,
    program: &Program,
    diagnostics: &mut DiagnosticBag,
) {
    let mut checker = WitnessChecker {
        file,
        program,
        diagnostics,
    };

    if let Some(ctor) = &program.constructor {
        let param_taints: Vec<Taint> = ctor
            .params
            .iter()
            .map(|p| Taint::single(format!("constructor parameter `{}`", p.name), p.span))
            .collect();
        let _ = checker.check_stmts(&ctor.body, &param_taints, &Taint::clean());
    }

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
        let _ = checker.check_stmts(&circuit.body, &param_taints, &Taint::clean());
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

    fn check_stmts(
        &mut self,
        stmts: &[Stmt],
        param_taints: &[Taint],
        guard_taint: &Taint,
    ) -> Taint {
        let mut locals: HashMap<LocalId, Taint> = HashMap::new();
        self.check_stmts_in_scope(stmts, param_taints, &mut locals, guard_taint)
    }

    fn check_stmts_in_scope(
        &mut self,
        stmts: &[Stmt],
        param_taints: &[Taint],
        locals: &mut HashMap<LocalId, Taint>,
        guard_taint: &Taint,
    ) -> Taint {
        let mut ret_taint = Taint::clean();

        for stmt in stmts {
            match stmt {
                Stmt::Const { local, init, .. } => {
                    let t = self.check_expr(init, param_taints, locals, guard_taint);
                    locals.insert(*local, t);
                }
                Stmt::If {
                    cond,
                    then_branch,
                    else_branch,
                    ..
                } => {
                    let ct = self.check_expr(cond, param_taints, locals, guard_taint);
                    let branch_guard = guard_taint.merge(&ct);
                    let mut then_locals = locals.clone();
                    let tt = self.check_stmts_in_scope(
                        then_branch,
                        param_taints,
                        &mut then_locals,
                        &branch_guard,
                    );
                    let mut else_locals = locals.clone();
                    let et = self.check_stmts_in_scope(
                        else_branch,
                        param_taints,
                        &mut else_locals,
                        &branch_guard,
                    );
                    ret_taint = ret_taint.merge(&tt).merge(&et);
                }
                Stmt::ForRange { local, body, .. } => {
                    let mut loop_locals = locals.clone();
                    loop_locals.insert(*local, Taint::clean());
                    let bt = self.check_stmts_in_scope(
                        body,
                        param_taints,
                        &mut loop_locals,
                        guard_taint,
                    );
                    ret_taint = ret_taint.merge(&bt);
                }
                Stmt::ForEach {
                    local, iter, body, ..
                } => {
                    let it = self.check_expr(iter, param_taints, locals, guard_taint);
                    let mut loop_locals = locals.clone();
                    loop_locals.insert(*local, it);
                    let bt = self.check_stmts_in_scope(
                        body,
                        param_taints,
                        &mut loop_locals,
                        guard_taint,
                    );
                    ret_taint = ret_taint.merge(&bt);
                }
                Stmt::Expr(expr) => {
                    let _ = self.check_expr(expr, param_taints, locals, guard_taint);
                }
                Stmt::Return {
                    value: Some(expr), ..
                } => {
                    let t = self.check_expr(expr, param_taints, locals, guard_taint);
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
            ExprKind::IntLit(_)
            | ExprKind::BoolLit(_)
            | ExprKind::BytesLit(_)
            | ExprKind::Default(_)
            | ExprKind::DefaultAdt(_)
            | ExprKind::EnumVariant { .. }
            | ExprKind::MaybeNone(_) => Taint::clean(),
            ExprKind::ParamRef(pid) => param_taints[pid.0 as usize].clone(),
            ExprKind::LocalRef(lid) => locals.get(lid).cloned().unwrap_or_default(),
            ExprKind::Tuple(elems) | ExprKind::Vector(elems) | ExprKind::BytesPack(elems) => {
                elems.iter().fold(Taint::clean(), |acc, e| {
                    acc.merge(&self.check_expr(e, param_taints, locals, guard_taint))
                })
            }
            ExprKind::Block { stmts, tail } => {
                let mut block_locals = locals.clone();
                let st =
                    self.check_stmts_in_scope(stmts, param_taints, &mut block_locals, guard_taint);
                let tt = self.check_expr(tail, param_taints, &block_locals, guard_taint);
                st.merge(&tt)
            }
            ExprKind::Unary { operand, .. }
            | ExprKind::Cast { expr: operand, .. }
            | ExprKind::PersistentHash { arg: operand, .. }
            | ExprKind::TransientHash { arg: operand, .. }
            | ExprKind::DegradeToTransient(operand)
            | ExprKind::UpgradeFromTransient(operand)
            | ExprKind::MerkleTreePathRoot { path: operand, .. }
            | ExprKind::FieldAccess { base: operand, .. }
            | ExprKind::Slice { base: operand, .. }
            | ExprKind::MaybeSome(operand) => {
                self.check_expr(operand, param_taints, locals, guard_taint)
            }
            ExprKind::PersistentCommit { value, rand, .. }
            | ExprKind::TransientCommit { value, rand, .. } => {
                // Cryptographic commitments hide both value and randomness (`discloses nothing`).
                let _ = self.check_expr(value, param_taints, locals, guard_taint);
                let _ = self.check_expr(rand, param_taints, locals, guard_taint);
                Taint::clean()
            }
            ExprKind::Index { base, index } => {
                let bt = self.check_expr(base, param_taints, locals, guard_taint);
                let it = self.check_expr(index, param_taints, locals, guard_taint);
                bt.merge(&it)
            }
            ExprKind::StructLit { fields } => fields.iter().fold(Taint::clean(), |acc, (_, e)| {
                acc.merge(&self.check_expr(e, param_taints, locals, guard_taint))
            }),
            ExprKind::Binary { op, lhs, rhs } => {
                let lt = self.check_expr(lhs, param_taints, locals, guard_taint);
                let rhs_guard = if matches!(op, BinaryOp::And | BinaryOp::Or) {
                    guard_taint.merge(&lt)
                } else {
                    guard_taint.clone()
                };
                let rt = self.check_expr(rhs, param_taints, locals, &rhs_guard);
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
            ExprKind::Assert { cond, .. } => {
                let _ = self.check_expr(cond, param_taints, locals, guard_taint);
                Taint::clean()
            }
            ExprKind::Disclose(inner) => {
                let _ = self.check_expr(inner, param_taints, locals, guard_taint);
                Taint::clean()
            }
            ExprKind::WitnessCall { witness, args } => {
                for a in args {
                    let _ = self.check_expr(a, param_taints, locals, guard_taint);
                }
                let w = self.program.witness(*witness);
                Taint::single(format!("return value of witness `{}`", w.name), expr.span)
            }
            ExprKind::NativeWitness { kind, args } => {
                for a in args {
                    let _ = self.check_expr(a, param_taints, locals, guard_taint);
                }
                match kind {
                    compact_hir::NativeWitnessKind::OwnPublicKey => Taint::single(
                        "return value of native witness `ownPublicKey`".to_owned(),
                        expr.span,
                    ),
                    compact_hir::NativeWitnessKind::CreateZswapInput
                    | compact_hir::NativeWitnessKind::CreateZswapOutput => Taint::clean(),
                }
            }
            ExprKind::CircuitCall { circuit, args } => {
                let arg_taints: Vec<_> = args
                    .iter()
                    .map(|a| self.check_expr(a, param_taints, locals, guard_taint))
                    .collect();
                let callee = self.program.circuit(*circuit);
                self.check_stmts(&callee.body, &arg_taints, guard_taint)
            }
            ExprKind::LedgerCall {
                field,
                key_path,
                op,
                args,
                ..
            } => {
                let field_name = &self.program.ledger_field(*field).name;
                if guard_taint.is_tainted() {
                    self.report_disclosure(
                        expr.span,
                        guard_taint,
                        &format!("ledger operation on `{field_name}` guarded by witness condition"),
                    );
                }
                for key in key_path {
                    let key_taint = self.check_expr(key, param_taints, locals, guard_taint);
                    if key_taint.is_tainted() {
                        self.report_disclosure(
                            key.span,
                            &key_taint,
                            &format!("ledger `{field_name}.lookup`"),
                        );
                    }
                }
                for (arg_idx, arg) in args.iter().enumerate() {
                    let arg_taint = self.check_expr(arg, param_taints, locals, guard_taint);
                    // `kernel.claimContractCall(addr, entry_point, comm)`: `comm` is a commitment (`discloses nothing`).
                    if matches!(op, compact_hir::LedgerOp::KernelClaimContractCall) && arg_idx == 2
                    {
                        continue;
                    }
                    if arg_taint.is_tainted() {
                        self.report_disclosure(
                            arg.span,
                            &arg_taint,
                            &format!("ledger `{}.{}`", field_name, op.name()),
                        );
                    }
                }
                Taint::clean()
            }
        }
    }
}

/// Reject any cyclic/recursive circuit call graph.
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

    let mut state = vec![0u8; n];
    for id in 0..n {
        if state[id] == 0 {
            dfs_cycle(
                CircuitId(id as u32),
                &adj,
                &mut state,
                file,
                program,
                diagnostics,
            );
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
            Stmt::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                collect_calls_expr(cond, out);
                collect_calls_stmts(then_branch, out);
                collect_calls_stmts(else_branch, out);
            }
            Stmt::ForRange { body, .. } => collect_calls_stmts(body, out),
            Stmt::ForEach { iter, body, .. } => {
                collect_calls_expr(iter, out);
                collect_calls_stmts(body, out);
            }
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
        ExprKind::LedgerCall { key_path, args, .. } => {
            for k in key_path {
                collect_calls_expr(k, out);
            }
            for a in args {
                collect_calls_expr(a, out);
            }
        }
        ExprKind::Tuple(elems)
        | ExprKind::Vector(elems)
        | ExprKind::BytesPack(elems)
        | ExprKind::WitnessCall { args: elems, .. }
        | ExprKind::NativeWitness { args: elems, .. } => {
            for e in elems {
                collect_calls_expr(e, out);
            }
        }
        ExprKind::Block { stmts, tail } => {
            collect_calls_stmts(stmts, out);
            collect_calls_expr(tail, out);
        }
        ExprKind::StructLit { fields } => {
            for (_, e) in fields {
                collect_calls_expr(e, out);
            }
        }
        ExprKind::Unary { operand, .. }
        | ExprKind::Cast { expr: operand, .. }
        | ExprKind::Assert { cond: operand, .. }
        | ExprKind::Disclose(operand)
        | ExprKind::PersistentHash { arg: operand, .. }
        | ExprKind::TransientHash { arg: operand, .. }
        | ExprKind::DegradeToTransient(operand)
        | ExprKind::UpgradeFromTransient(operand)
        | ExprKind::MerkleTreePathRoot { path: operand, .. }
        | ExprKind::FieldAccess { base: operand, .. }
        | ExprKind::Slice { base: operand, .. }
        | ExprKind::MaybeSome(operand) => collect_calls_expr(operand, out),
        ExprKind::PersistentCommit { value, rand, .. }
        | ExprKind::TransientCommit { value, rand, .. } => {
            collect_calls_expr(value, out);
            collect_calls_expr(rand, out);
        }
        ExprKind::Index { base, index } => {
            collect_calls_expr(base, out);
            collect_calls_expr(index, out);
        }
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
        | ExprKind::BytesLit(_)
        | ExprKind::Default(_)
        | ExprKind::DefaultAdt(_)
        | ExprKind::ParamRef(_)
        | ExprKind::LocalRef(_)
        | ExprKind::EnumVariant { .. }
        | ExprKind::MaybeNone(_) => {}
    }
}
