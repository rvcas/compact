mod witness;

use std::collections::HashMap;

use compact_ast::{Ast, NodeIndex, NodeTag, TokenIndex, TokenTag};
use compact_diagnostics::{CompactDiagnostic, DiagnosticBag};
use compact_hir::{
    BinaryOp, Circuit, CircuitId, EnumDecl, EnumId, Expr, ExprKind, LedgerAdt, LedgerField,
    LedgerFieldId, LedgerOp, LocalId, Param, ParamId, Program, Stmt, Type, UnaryOp,
};
use compact_span::{SourceFile, Span};

pub struct CheckResult {
    pub program: Program,
    pub diagnostics: DiagnosticBag,
}

/// Lower an AST into a type-checked, witness-checked [`Program`].
pub fn check(file: &SourceFile, ast: &Ast) -> CheckResult {
    let mut analyzer = Analyzer {
        file,
        ast,
        diagnostics: DiagnosticBag::new(),
        enums: Vec::new(),
        enum_by_name: HashMap::new(),
        ledger_fields: Vec::new(),
        ledger_by_name: HashMap::new(),
        circuit_sigs: Vec::new(),
        circuit_by_name: HashMap::new(),
        circuits: Vec::new(),
    };
    analyzer.run();

    let mut program = Program {
        enums: analyzer.enums,
        ledger_fields: analyzer.ledger_fields,
        circuits: analyzer.circuits,
    };

    // Pass 3: Reject recursive circuits, propagate transitive purity, and run WPP witness checks.
    witness::reject_recursive_circuits(file, &program, &mut analyzer.diagnostics);
    propagate_purity(file, &mut program, &analyzer.circuit_sigs, &mut analyzer.diagnostics);
    if !analyzer.diagnostics.has_errors() {
        witness::check_witness_disclosure(file, &program, &mut analyzer.diagnostics);
    }

    CheckResult {
        program,
        diagnostics: analyzer.diagnostics,
    }
}

struct CircuitSig {
    id: CircuitId,
    name: String,
    name_span: Span,
    params: Vec<Param>,
    ret_type: Type,
    body_node: NodeIndex,
    exported: bool,
    declared_pure: bool,
    span: Span,
}

#[derive(Clone)]
enum ValueBinding {
    Param(ParamId, Type),
    Local(LocalId, Type),
}

struct Analyzer<'a> {
    file: &'a SourceFile,
    ast: &'a Ast,
    diagnostics: DiagnosticBag,
    enums: Vec<EnumDecl>,
    enum_by_name: HashMap<String, EnumId>,
    ledger_fields: Vec<LedgerField>,
    ledger_by_name: HashMap<String, LedgerFieldId>,
    circuit_sigs: Vec<CircuitSig>,
    circuit_by_name: HashMap<String, CircuitId>,
    circuits: Vec<Circuit>,
}

impl<'a> Analyzer<'a> {
    fn text(&self, tok: TokenIndex) -> &'a str {
        self.ast.token_text(tok, self.file.text())
    }

    fn run(&mut self) {
        let decls: Vec<_> = self.ast.root_decls().collect();

        // Pass 1a: imports and enums (types must exist before ledger/circuit signatures).
        for &decl in &decls {
            match self.ast.node_tag(decl) {
                NodeTag::ImportDecl => {
                    let import = self.ast.import_decl(decl);
                    let name = self.text(import.name_token);
                    if name != "CompactStandardLibrary" {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            self.ast.token_span(import.name_token),
                            format!("unknown module `{name}`"),
                        ));
                    }
                }
                NodeTag::EnumDecl => self.register_enum(decl),
                _ => {}
            }
        }

        // Pass 1b: ledger declarations and circuit signatures.
        for &decl in &decls {
            match self.ast.node_tag(decl) {
                NodeTag::LedgerDecl => self.register_ledger(decl),
                NodeTag::CircuitDecl => self.register_circuit_sig(decl),
                _ => {}
            }
        }

        // Pass 2: type-check circuit bodies.
        for sig_idx in 0..self.circuit_sigs.len() {
            self.check_circuit_body(sig_idx);
        }
    }

    fn register_enum(&mut self, node: NodeIndex) {
        let decl = self.ast.enum_decl(node);
        let name = self.text(decl.name_token).to_owned();
        let name_span = self.ast.token_span(decl.name_token);
        if self.enum_by_name.contains_key(&name) {
            self.diagnostics.push(CompactDiagnostic::error(
                self.file,
                name_span,
                format!("duplicate enum `{name}`"),
            ));
            return;
        }
        let mut variants = Vec::new();
        for vtok in self.ast.extra_tokens(decl.variants_start, decl.variants_end) {
            let vname = self.text(vtok).to_owned();
            if variants.contains(&vname) {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    self.ast.token_span(vtok),
                    format!("duplicate variant `{vname}` in enum `{name}`"),
                ));
                continue;
            }
            variants.push(vname);
        }
        if variants.is_empty() {
            self.diagnostics.push(CompactDiagnostic::error(
                self.file,
                name_span,
                format!("enum `{name}` must declare at least one variant"),
            ));
            return;
        }
        let id = EnumId(self.enums.len() as u32);
        self.enums.push(EnumDecl {
            id,
            name: name.clone(),
            variants,
            exported: decl.exported,
            span: self.ast.node_span(node),
        });
        self.enum_by_name.insert(name, id);
    }

    fn register_ledger(&mut self, node: NodeIndex) {
        let decl = self.ast.ledger_decl(node);
        let name = self.text(decl.name_token).to_owned();
        let name_span = self.ast.token_span(decl.name_token);

        if self.ledger_by_name.contains_key(&name) {
            self.diagnostics.push(CompactDiagnostic::error(
                self.file,
                name_span,
                format!("duplicate ledger field `{name}`"),
            ));
            return;
        }

        let (adt, value_type) = match self.ast.node_tag(decl.type_node) {
            NodeTag::TypeNamed
                if self.text(self.ast.node_main_token(decl.type_node)) == "Counter" =>
            {
                (LedgerAdt::Counter, Type::Uint(64))
            }
            _ => {
                let Some(ty) = self.resolve_type(decl.type_node) else {
                    return;
                };
                (LedgerAdt::Cell, ty)
            }
        };

        let id = LedgerFieldId(self.ledger_fields.len() as u32);
        let path = vec![id.0];
        self.ledger_fields.push(LedgerField {
            id,
            name: name.clone(),
            adt,
            value_type,
            path,
            exported: decl.exported,
            sealed: decl.sealed,
            span: self.ast.node_span(node),
        });
        self.ledger_by_name.insert(name, id);
    }

    fn register_circuit_sig(&mut self, node: NodeIndex) {
        let decl = self.ast.circuit_decl(node);
        let name = self.text(decl.name_token).to_owned();
        let name_span = self.ast.token_span(decl.name_token);

        if self.circuit_by_name.contains_key(&name) {
            self.diagnostics.push(CompactDiagnostic::error(
                self.file,
                name_span,
                format!("duplicate circuit `{name}`"),
            ));
            return;
        }

        let mut params = Vec::new();
        let mut seen = HashMap::new();
        let param_nodes: Vec<_> = self
            .ast
            .extra_nodes(decl.params_start, decl.params_end)
            .collect();
        for pnode in param_nodes {
            let p = self.ast.param(pnode);
            let pname = self.text(p.name_token).to_owned();
            if seen.contains_key(&pname) {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    self.ast.token_span(p.name_token),
                    format!("duplicate parameter `{pname}`"),
                ));
                continue;
            }
            let Some(pty) = self.resolve_type(p.type_node) else {
                continue;
            };
            let pid = ParamId(params.len() as u32);
            seen.insert(pname.clone(), pid);
            params.push(Param {
                id: pid,
                name: pname,
                ty: pty,
                span: self.ast.node_span(pnode),
            });
        }

        let Some(ret_type) = self.resolve_type(decl.ret_type) else {
            return;
        };

        let id = CircuitId(self.circuit_sigs.len() as u32);
        self.circuit_by_name.insert(name.clone(), id);
        self.circuit_sigs.push(CircuitSig {
            id,
            name,
            name_span,
            params,
            ret_type,
            body_node: decl.body,
            exported: decl.exported,
            declared_pure: decl.pure,
            span: self.ast.node_span(node),
        });
    }

    fn resolve_type(&mut self, node: NodeIndex) -> Option<Type> {
        match self.ast.node_tag(node) {
            NodeTag::TypeNamed => {
                let tok = self.ast.node_main_token(node);
                let name = self.text(tok);
                match name {
                    "Field" => Some(Type::Field),
                    "Boolean" => Some(Type::Boolean),
                    _ => {
                        if let Some(&eid) = self.enum_by_name.get(name) {
                            Some(Type::Enum(eid))
                        } else {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.file,
                                self.ast.token_span(tok),
                                format!("unknown type `{name}`"),
                            ));
                            None
                        }
                    }
                }
            }
            NodeTag::TypeTuple => {
                let data = self.ast.node_data(node);
                let elem_nodes: Vec<_> = self.ast.extra_nodes(data.lhs, data.rhs).collect();
                let mut elems = Vec::with_capacity(elem_nodes.len());
                for enode in elem_nodes {
                    elems.push(self.resolve_type(enode)?);
                }
                Some(Type::Tuple(elems))
            }
            _ => None,
        }
    }

    fn format_type(&self, ty: &Type) -> String {
        match ty {
            Type::Field => "Field".into(),
            Type::Boolean => "Boolean".into(),
            Type::Uint(bits) => format!("Uint<{bits}>"),
            Type::Tuple(elems) => {
                let inner: Vec<_> = elems.iter().map(|e| self.format_type(e)).collect();
                format!("[{}]", inner.join(", "))
            }
            Type::Enum(id) => self.enums[id.0 as usize].name.clone(),
        }
    }

    fn check_circuit_body(&mut self, sig_idx: usize) {
        let id = self.circuit_sigs[sig_idx].id;
        let name = self.circuit_sigs[sig_idx].name.clone();
        let params = self.circuit_sigs[sig_idx].params.clone();
        let ret_type = self.circuit_sigs[sig_idx].ret_type.clone();
        let body_node = self.circuit_sigs[sig_idx].body_node;
        let exported = self.circuit_sigs[sig_idx].exported;
        let span = self.circuit_sigs[sig_idx].span;

        let mut scope: HashMap<String, ValueBinding> = HashMap::new();
        for p in &params {
            scope.insert(p.name.clone(), ValueBinding::Param(p.id, p.ty.clone()));
        }
        let mut next_local: u32 = 0;

        let block_data = self.ast.node_data(body_node);
        let stmt_nodes: Vec<_> = self
            .ast
            .extra_nodes(block_data.lhs, block_data.rhs)
            .collect();

        let mut body = Vec::new();
        for snode in stmt_nodes {
            if let Some(stmt) = self.check_stmt(snode, &mut scope, &mut next_local, &ret_type) {
                body.push(stmt);
            }
        }

        self.circuits.push(Circuit {
            id,
            name,
            params,
            ret_type,
            body,
            exported,
            pure: true,  // computed in propagate_purity
            proof: false, // computed in propagate_purity
            span,
        });
    }

    fn check_stmt(
        &mut self,
        node: NodeIndex,
        scope: &mut HashMap<String, ValueBinding>,
        next_local: &mut u32,
        expected_ret: &Type,
    ) -> Option<Stmt> {
        let data = self.ast.node_data(node);
        match self.ast.node_tag(node) {
            NodeTag::ConstStmt => {
                let stmt = self.ast.const_stmt(node);
                let name = self.text(stmt.name_token).to_owned();
                let annotated = match stmt.ty {
                    Some(ty_node) => Some(self.resolve_type(ty_node)?),
                    None => None,
                };
                let mut init = self.check_expr(stmt.init, scope, annotated.as_ref())?;
                let ty = if let Some(ann) = annotated {
                    if !self.coerce_or_check(&mut init, &ann) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            init.span,
                            format!(
                                "type mismatch in `const {name}`: expected `{}`, found `{}`",
                                self.format_type(&ann),
                                self.format_type(&init.ty)
                            ),
                        ));
                    }
                    ann
                } else {
                    init.ty.clone()
                };
                let local = LocalId(*next_local);
                *next_local += 1;
                scope.insert(name.clone(), ValueBinding::Local(local, ty.clone()));
                Some(Stmt::Const {
                    local,
                    name,
                    ty,
                    init,
                    span: self.ast.node_span(node),
                })
            }
            NodeTag::AssignStmt => {
                let stmt = self.ast.assign_stmt(node);
                let assign_span = self.ast.node_span(node);
                if self.ast.node_tag(stmt.lhs) != NodeTag::IdentExpr {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        self.ast.node_span(stmt.lhs),
                        "left-hand side of assignment must be a ledger field",
                    ));
                    return None;
                }
                let lhs_tok = self.ast.node_main_token(stmt.lhs);
                let field_name = self.text(lhs_tok);
                let Some(&field_id) = self.ledger_by_name.get(field_name) else {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        self.ast.token_span(lhs_tok),
                        format!("cannot assign to `{field_name}`: not a ledger field"),
                    ));
                    return None;
                };
                let field = &self.ledger_fields[field_id.0 as usize];
                if field.adt != LedgerAdt::Cell {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        assign_span,
                        format!(
                            "cannot directly assign to ledger `{field_name}` of ADT type `{}`; use its methods instead",
                            field.adt.name()
                        ),
                    ));
                    return None;
                }
                let expected_val_ty = field.value_type.clone();
                let mut rhs = self.check_expr(stmt.rhs, scope, Some(&expected_val_ty))?;
                if !self.coerce_or_check(&mut rhs, &expected_val_ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        rhs.span,
                        format!(
                            "cannot assign `{}` to ledger field `{field_name}` of type `{}`",
                            self.format_type(&rhs.ty),
                            self.format_type(&expected_val_ty)
                        ),
                    ));
                    return None;
                }
                Some(Stmt::Expr(Expr {
                    kind: ExprKind::LedgerCall {
                        field: field_id,
                        op: LedgerOp::CellWrite,
                        args: vec![rhs],
                    },
                    ty: Type::unit(),
                    span: assign_span,
                }))
            }
            NodeTag::ExprStmt => {
                let expr = self.check_expr(NodeIndex(data.lhs), scope, None)?;
                Some(Stmt::Expr(expr))
            }
            NodeTag::ReturnStmt => {
                let span = self.ast.node_span(node);
                let value = if let Some(expr_node) = NodeIndex(data.lhs).into_option() {
                    let mut expr = self.check_expr(expr_node, scope, Some(expected_ret))?;
                    if !self.coerce_or_check(&mut expr, expected_ret) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            expr.span,
                            format!(
                                "mismatched return type: expected `{}`, found `{}`",
                                self.format_type(expected_ret),
                                self.format_type(&expr.ty)
                            ),
                        ));
                    }
                    Some(expr)
                } else {
                    if !expected_ret.is_unit() {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            span,
                            format!(
                                "empty `return` in circuit returning `{}`",
                                self.format_type(expected_ret)
                            ),
                        ));
                    }
                    None
                };
                Some(Stmt::Return { value, span })
            }
            _ => None,
        }
    }

    fn coerce_or_check(&self, expr: &mut Expr, expected: &Type) -> bool {
        if expr.ty == *expected {
            return true;
        }
        // Allow unsuffixed integer literals to narrow/coerce to expected Uint<N>.
        if let (ExprKind::IntLit(v), Type::Uint(bits)) = (&expr.kind, expected)
            && *bits < 128
            && *v < (1u128 << bits)
        {
            expr.ty = expected.clone();
            return true;
        }
        false
    }

    fn check_expr(
        &mut self,
        node: NodeIndex,
        scope: &HashMap<String, ValueBinding>,
        expected: Option<&Type>,
    ) -> Option<Expr> {
        let span = self.ast.node_span(node);
        match self.ast.node_tag(node) {
            NodeTag::IntLitExpr => {
                let tok = self.ast.node_main_token(node);
                let raw = self.text(tok);
                let val: u128 = match raw.parse() {
                    Ok(v) => v,
                    Err(_) => {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            span,
                            format!("integer literal `{raw}` is out of range"),
                        ));
                        return None;
                    }
                };
                let ty = match expected {
                    Some(Type::Uint(bits)) if *bits < 128 && val < (1u128 << bits) => {
                        Type::Uint(*bits)
                    }
                    _ => Type::Uint(64),
                };
                Some(Expr {
                    kind: ExprKind::IntLit(val),
                    ty,
                    span,
                })
            }
            NodeTag::BoolLitExpr => {
                let tok = self.ast.node_main_token(node);
                let val = self.ast.token_tag(tok) == TokenTag::True;
                Some(Expr {
                    kind: ExprKind::BoolLit(val),
                    ty: Type::Boolean,
                    span,
                })
            }
            NodeTag::IdentExpr => {
                let tok = self.ast.node_main_token(node);
                let name = self.text(tok);
                if let Some(binding) = scope.get(name) {
                    return Some(match binding {
                        ValueBinding::Param(pid, ty) => Expr {
                            kind: ExprKind::ParamRef(*pid),
                            ty: ty.clone(),
                            span,
                        },
                        ValueBinding::Local(lid, ty) => Expr {
                            kind: ExprKind::LocalRef(*lid),
                            ty: ty.clone(),
                            span,
                        },
                    });
                }
                // Implicit Cell read sugar: referencing a Cell ledger field reads it.
                if let Some(&field_id) = self.ledger_by_name.get(name) {
                    let field = &self.ledger_fields[field_id.0 as usize];
                    if field.adt == LedgerAdt::Cell {
                        return Some(Expr {
                            kind: ExprKind::LedgerCall {
                                field: field_id,
                                op: LedgerOp::CellRead,
                                args: Vec::new(),
                            },
                            ty: field.value_type.clone(),
                            span,
                        });
                    }
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        span,
                        format!(
                            "ledger field `{name}` of type `{}` cannot be read directly as a value",
                            field.adt.name()
                        ),
                    ));
                    return None;
                }
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    span,
                    format!("unbound identifier `{name}`"),
                ));
                None
            }
            NodeTag::MemberExpr => {
                let data = self.ast.node_data(node);
                let lhs = NodeIndex(data.lhs);
                let field_tok = TokenIndex(data.rhs);
                if self.ast.node_tag(lhs) == NodeTag::IdentExpr {
                    let type_name = self.text(self.ast.node_main_token(lhs));
                    if let Some(&enum_id) = self.enum_by_name.get(type_name) {
                        let variant_name = self.text(field_tok);
                        if let Some(idx) = self.enums[enum_id.0 as usize]
                            .variants
                            .iter()
                            .position(|v| v == variant_name)
                        {
                            return Some(Expr {
                                kind: ExprKind::EnumVariant {
                                    enum_id,
                                    variant_idx: idx as u32,
                                },
                                ty: Type::Enum(enum_id),
                                span,
                            });
                        }
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            self.ast.token_span(field_tok),
                            format!("enum `{type_name}` has no variant `{variant_name}`"),
                        ));
                        return None;
                    }
                }
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    span,
                    "unsupported member access",
                ));
                None
            }
            NodeTag::TupleExpr => {
                let data = self.ast.node_data(node);
                let elem_nodes: Vec<_> = self.ast.extra_nodes(data.lhs, data.rhs).collect();
                let mut exprs = Vec::with_capacity(elem_nodes.len());
                let mut tys = Vec::with_capacity(elem_nodes.len());
                for enode in elem_nodes {
                    let e = self.check_expr(enode, scope, None)?;
                    tys.push(e.ty.clone());
                    exprs.push(e);
                }
                Some(Expr {
                    kind: ExprKind::Tuple(exprs),
                    ty: Type::Tuple(tys),
                    span,
                })
            }
            NodeTag::UnaryExpr => {
                let op_tok = self.ast.node_main_token(node);
                let data = self.ast.node_data(node);
                let operand = self.check_expr(NodeIndex(data.lhs), scope, expected)?;
                match self.ast.token_tag(op_tok) {
                    TokenTag::Bang => {
                        if operand.ty != Type::Boolean {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.file,
                                operand.span,
                                format!(
                                    "logical `!` expects `Boolean`, found `{}`",
                                    self.format_type(&operand.ty)
                                ),
                            ));
                            return None;
                        }
                        Some(Expr {
                            kind: ExprKind::Unary {
                                op: UnaryOp::Not,
                                operand: Box::new(operand),
                            },
                            ty: Type::Boolean,
                            span,
                        })
                    }
                    TokenTag::Minus => {
                        if operand.ty != Type::Field {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.file,
                                operand.span,
                                format!(
                                    "unary `-` expects `Field`, found `{}`",
                                    self.format_type(&operand.ty)
                                ),
                            ));
                            return None;
                        }
                        Some(Expr {
                            kind: ExprKind::Unary {
                                op: UnaryOp::Neg,
                                operand: Box::new(operand),
                            },
                            ty: Type::Field,
                            span,
                        })
                    }
                    _ => None,
                }
            }
            NodeTag::BinaryExpr => {
                let op_tok = self.ast.node_main_token(node);
                let op = match self.ast.token_tag(op_tok) {
                    TokenTag::Plus => BinaryOp::Add,
                    TokenTag::Minus => BinaryOp::Sub,
                    TokenTag::EqEq => BinaryOp::Eq,
                    TokenTag::BangEq => BinaryOp::Neq,
                    other => {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            self.ast.token_span(op_tok),
                            format!("unsupported binary operator `{}`", other.as_str()),
                        ));
                        return None;
                    }
                };
                let data = self.ast.node_data(node);
                let lhs = self.check_expr(NodeIndex(data.lhs), scope, None)?;
                let mut rhs = self.check_expr(NodeIndex(data.rhs), scope, Some(&lhs.ty))?;
                if !self.coerce_or_check(&mut rhs, &lhs.ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        span,
                        format!(
                            "incompatible operand types `{}` and `{}`",
                            self.format_type(&lhs.ty),
                            self.format_type(&rhs.ty)
                        ),
                    ));
                    return None;
                }
                let ty = match op {
                    BinaryOp::Eq | BinaryOp::Neq => Type::Boolean,
                    BinaryOp::Add | BinaryOp::Sub => lhs.ty.clone(),
                };
                Some(Expr {
                    kind: ExprKind::Binary {
                        op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    },
                    ty,
                    span,
                })
            }
            NodeTag::TernaryExpr => {
                let t = self.ast.ternary_expr(node);
                let cond = self.check_expr(t.cond, scope, Some(&Type::Boolean))?;
                if cond.ty != Type::Boolean {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        cond.span,
                        format!(
                            "ternary condition must be `Boolean`, found `{}`",
                            self.format_type(&cond.ty)
                        ),
                    ));
                    return None;
                }
                let then_branch = self.check_expr(t.then_branch, scope, expected)?;
                let mut else_branch =
                    self.check_expr(t.else_branch, scope, Some(&then_branch.ty))?;
                if !self.coerce_or_check(&mut else_branch, &then_branch.ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        span,
                        format!(
                            "ternary branches have incompatible types `{}` and `{}`",
                            self.format_type(&then_branch.ty),
                            self.format_type(&else_branch.ty)
                        ),
                    ));
                    return None;
                }
                let ty = then_branch.ty.clone();
                Some(Expr {
                    kind: ExprKind::Ternary {
                        cond: Box::new(cond),
                        then_branch: Box::new(then_branch),
                        else_branch: Box::new(else_branch),
                    },
                    ty,
                    span,
                })
            }
            NodeTag::CastExpr => {
                let data = self.ast.node_data(node);
                let target = self.resolve_type(NodeIndex(data.rhs))?;
                let inner = self.check_expr(NodeIndex(data.lhs), scope, None)?;
                let valid = matches!(
                    (&inner.ty, &target),
                    (Type::Uint(_), Type::Field)
                        | (Type::Boolean, Type::Field)
                        | (Type::Enum(_), Type::Field)
                        | (Type::Field, Type::Field)
                ) || inner.ty == target;
                if !valid {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        span,
                        format!(
                            "cannot cast `{}` to `{}`",
                            self.format_type(&inner.ty),
                            self.format_type(&target)
                        ),
                    ));
                    return None;
                }
                Some(Expr {
                    kind: ExprKind::Cast {
                        expr: Box::new(inner),
                        target: target.clone(),
                    },
                    ty: target,
                    span,
                })
            }
            NodeTag::AssertExpr => {
                let a = self.ast.assert_expr(node);
                let cond = self.check_expr(a.cond, scope, Some(&Type::Boolean))?;
                if cond.ty != Type::Boolean {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        cond.span,
                        format!(
                            "`assert` condition must be `Boolean`, found `{}`",
                            self.format_type(&cond.ty)
                        ),
                    ));
                    return None;
                }
                if self.ast.node_tag(a.msg) != NodeTag::StringLitExpr {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        self.ast.node_span(a.msg),
                        "`assert` message must be a string literal",
                    ));
                    return None;
                }
                let raw_msg = self.text(self.ast.node_main_token(a.msg));
                let message = unquote_string(raw_msg);
                Some(Expr {
                    kind: ExprKind::Assert {
                        cond: Box::new(cond),
                        message,
                    },
                    ty: Type::unit(),
                    span,
                })
            }
            NodeTag::DiscloseExpr => {
                let data = self.ast.node_data(node);
                let inner = self.check_expr(NodeIndex(data.lhs), scope, expected)?;
                let ty = inner.ty.clone();
                Some(Expr {
                    kind: ExprKind::Disclose(Box::new(inner)),
                    ty,
                    span,
                })
            }
            NodeTag::CallExpr => {
                let call = self.ast.call_expr(node);
                let arg_nodes: Vec<_> = self
                    .ast
                    .extra_nodes(call.args_start, call.args_end)
                    .collect();

                // 1. Direct circuit call: `in_state(STATE.unset)`
                if self.ast.node_tag(call.callee) == NodeTag::IdentExpr {
                    let callee_tok = self.ast.node_main_token(call.callee);
                    let callee_name = self.text(callee_tok);
                    if let Some(&cid) = self.circuit_by_name.get(callee_name) {
                        return self.check_circuit_call(cid, &arg_nodes, span, scope);
                    }
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        self.ast.token_span(callee_tok),
                        format!("unknown circuit `{callee_name}`"),
                    ));
                    return None;
                }

                // 2. Ledger ADT method call: `round.increment(1)` or `value.read()` / `value.write(x)`
                if self.ast.node_tag(call.callee) == NodeTag::MemberExpr {
                    let mdata = self.ast.node_data(call.callee);
                    let recv = NodeIndex(mdata.lhs);
                    let method_tok = TokenIndex(mdata.rhs);
                    if self.ast.node_tag(recv) == NodeTag::IdentExpr {
                        let recv_name = self.text(self.ast.node_main_token(recv));
                        if let Some(&field_id) = self.ledger_by_name.get(recv_name) {
                            let method_name = self.text(method_tok);
                            return self.check_ledger_call(
                                field_id,
                                method_name,
                                self.ast.token_span(method_tok),
                                &arg_nodes,
                                span,
                                scope,
                            );
                        }
                    }
                }

                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    span,
                    "unsupported call target",
                ));
                None
            }
            _ => {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    span,
                    "unsupported expression",
                ));
                None
            }
        }
    }

    fn check_circuit_call(
        &mut self,
        cid: CircuitId,
        arg_nodes: &[NodeIndex],
        call_span: Span,
        scope: &HashMap<String, ValueBinding>,
    ) -> Option<Expr> {
        let cname = self.circuit_sigs[cid.0 as usize].name.clone();
        let expected_params: Vec<Type> = self.circuit_sigs[cid.0 as usize]
            .params
            .iter()
            .map(|p| p.ty.clone())
            .collect();
        let ret_type = self.circuit_sigs[cid.0 as usize].ret_type.clone();

        if arg_nodes.len() != expected_params.len() {
            self.diagnostics.push(CompactDiagnostic::error(
                self.file,
                call_span,
                format!(
                    "circuit `{cname}` expects {} argument(s), found {}",
                    expected_params.len(),
                    arg_nodes.len()
                ),
            ));
            return None;
        }

        let mut args = Vec::with_capacity(arg_nodes.len());
        for (&anode, expected_ty) in arg_nodes.iter().zip(&expected_params) {
            let mut arg = self.check_expr(anode, scope, Some(expected_ty))?;
            if !self.coerce_or_check(&mut arg, expected_ty) {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    arg.span,
                    format!(
                        "argument type mismatch calling `{cname}`: expected `{}`, found `{}`",
                        self.format_type(expected_ty),
                        self.format_type(&arg.ty)
                    ),
                ));
                return None;
            }
            args.push(arg);
        }

        Some(Expr {
            kind: ExprKind::CircuitCall { circuit: cid, args },
            ty: ret_type,
            span: call_span,
        })
    }

    fn check_ledger_call(
        &mut self,
        field_id: LedgerFieldId,
        method_name: &str,
        method_span: Span,
        arg_nodes: &[NodeIndex],
        call_span: Span,
        scope: &HashMap<String, ValueBinding>,
    ) -> Option<Expr> {
        let adt = self.ledger_fields[field_id.0 as usize].adt;
        let value_type = self.ledger_fields[field_id.0 as usize].value_type.clone();

        match adt {
            LedgerAdt::Counter => {
                let (op, expected_args, ret_ty) = match method_name {
                    "increment" => (LedgerOp::CounterIncrement, 1usize, Type::unit()),
                    "decrement" => (LedgerOp::CounterDecrement, 1usize, Type::unit()),
                    "read" => (LedgerOp::CounterRead, 0usize, Type::Uint(64)),
                    other => {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            method_span,
                            format!("`Counter` has no method `{other}`"),
                        ));
                        return None;
                    }
                };

                if arg_nodes.len() != expected_args {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        call_span,
                        format!(
                            "`Counter.{method_name}` expects {expected_args} argument(s), found {}",
                            arg_nodes.len()
                        ),
                    ));
                    return None;
                }

                let mut args = Vec::with_capacity(arg_nodes.len());
                for &anode in arg_nodes {
                    let mut arg = self.check_expr(anode, scope, Some(&Type::Uint(16)))?;
                    if matches!(op, LedgerOp::CounterIncrement | LedgerOp::CounterDecrement)
                        && let ExprKind::IntLit(v) = arg.kind
                    {
                        if v > u16::MAX as u128 {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.file,
                                arg.span,
                                format!(
                                    "`Counter.{method_name}` expects a `Uint<16>` argument (0..=65535), found {v}"
                                ),
                            ));
                            return None;
                        }
                        arg.ty = Type::Uint(16);
                    }
                    args.push(arg);
                }

                Some(Expr {
                    kind: ExprKind::LedgerCall {
                        field: field_id,
                        op,
                        args,
                    },
                    ty: ret_ty,
                    span: call_span,
                })
            }
            LedgerAdt::Cell => match method_name {
                "read" => {
                    if !arg_nodes.is_empty() {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            call_span,
                            "`Cell.read` takes 0 arguments",
                        ));
                        return None;
                    }
                    Some(Expr {
                        kind: ExprKind::LedgerCall {
                            field: field_id,
                            op: LedgerOp::CellRead,
                            args: Vec::new(),
                        },
                        ty: value_type,
                        span: call_span,
                    })
                }
                "write" => {
                    if arg_nodes.len() != 1 {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            call_span,
                            "`Cell.write` takes 1 argument",
                        ));
                        return None;
                    }
                    let mut val = self.check_expr(arg_nodes[0], scope, Some(&value_type))?;
                    if !self.coerce_or_check(&mut val, &value_type) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            val.span,
                            format!(
                                "`Cell.write` expects `{}`, found `{}`",
                                self.format_type(&value_type),
                                self.format_type(&val.ty)
                            ),
                        ));
                        return None;
                    }
                    Some(Expr {
                        kind: ExprKind::LedgerCall {
                            field: field_id,
                            op: LedgerOp::CellWrite,
                            args: vec![val],
                        },
                        ty: Type::unit(),
                        span: call_span,
                    })
                }
                other => {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        method_span,
                        format!("`Cell` has no method `{other}`"),
                    ));
                    None
                }
            },
        }
    }
}

fn unquote_string(raw: &str) -> String {
    if raw.len() >= 2 {
        raw[1..raw.len() - 1].to_owned()
    } else {
        raw.to_owned()
    }
}

fn propagate_purity(
    file: &SourceFile,
    program: &mut Program,
    sigs: &[CircuitSig],
    diagnostics: &mut DiagnosticBag,
) {
    let n = program.circuits.len();
    let mut impure = vec![false; n];
    let mut direct_calls: Vec<Vec<CircuitId>> = vec![Vec::new(); n];

    for c in &program.circuits {
        let idx = c.id.0 as usize;
        impure[idx] = stmts_touch_ledger(&c.body, &mut direct_calls[idx]);
    }

    // Fixed-point propagation: if A calls impure B, A is impure.
    let mut changed = true;
    while changed {
        changed = false;
        for idx in 0..n {
            if !impure[idx] && direct_calls[idx].iter().any(|callee| impure[callee.0 as usize]) {
                impure[idx] = true;
                changed = true;
            }
        }
    }

    for c in &mut program.circuits {
        let idx = c.id.0 as usize;
        c.pure = !impure[idx];
        c.proof = c.exported && !c.pure;
        if sigs[idx].declared_pure && !c.pure {
            diagnostics.push(CompactDiagnostic::error(
                file,
                sigs[idx].name_span,
                format!("circuit `{}` is declared `pure` but accesses ledger state", c.name),
            ));
        }
    }
}

fn stmts_touch_ledger(stmts: &[Stmt], calls: &mut Vec<CircuitId>) -> bool {
    let mut touches = false;
    for stmt in stmts {
        match stmt {
            Stmt::Const { init, .. } => touches |= expr_touches_ledger(init, calls),
            Stmt::Expr(e) => touches |= expr_touches_ledger(e, calls),
            Stmt::Return { value: Some(e), .. } => touches |= expr_touches_ledger(e, calls),
            Stmt::Return { value: None, .. } => {}
        }
    }
    touches
}

fn expr_touches_ledger(expr: &Expr, calls: &mut Vec<CircuitId>) -> bool {
    match &expr.kind {
        ExprKind::LedgerCall { args, .. } => {
            for a in args {
                let _ = expr_touches_ledger(a, calls);
            }
            true
        }
        ExprKind::CircuitCall { circuit, args } => {
            calls.push(*circuit);
            let mut t = false;
            for a in args {
                t |= expr_touches_ledger(a, calls);
            }
            t
        }
        ExprKind::Tuple(elems) => elems.iter().fold(false, |acc, e| acc | expr_touches_ledger(e, calls)),
        ExprKind::Unary { operand, .. }
        | ExprKind::Cast { expr: operand, .. }
        | ExprKind::Assert { cond: operand, .. }
        | ExprKind::Disclose(operand) => expr_touches_ledger(operand, calls),
        ExprKind::Binary { lhs, rhs, .. } => {
            expr_touches_ledger(lhs, calls) | expr_touches_ledger(rhs, calls)
        }
        ExprKind::Ternary {
            cond,
            then_branch,
            else_branch,
        } => {
            expr_touches_ledger(cond, calls)
                | expr_touches_ledger(then_branch, calls)
                | expr_touches_ledger(else_branch, calls)
        }
        ExprKind::IntLit(_)
        | ExprKind::BoolLit(_)
        | ExprKind::ParamRef(_)
        | ExprKind::LocalRef(_)
        | ExprKind::EnumVariant { .. } => false,
    }
}

#[cfg(test)]
mod tests {
    use compact_parser::parse;
    use compact_span::SourceMap;
    use compact_test_utils::assert_compact_snapshot;

    use super::check;

    fn check_and_dump(src: &str) -> String {
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
        checked.program.dump()
    }

    #[test]
    fn check_counter_contract() {
        assert_compact_snapshot!(
            r#"
            import CompactStandardLibrary;

            export ledger round: Counter;

            export circuit increment(): [] {
              round.increment(1);
            }
            "#,
            check_and_dump
        );
    }

    #[test]
    fn check_cell_enum_and_helper() {
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
              const is_set = in_state(STATE.set);
              return is_set ? value : 0 as Field;
            }
            "#,
            check_and_dump
        );
    }

    #[test]
    fn rejects_undisclosed_witness_param_write() {
        let mut sm = SourceMap::new();
        let src = r#"
            export ledger value: Field;
            export circuit set(v: Field): [] {
              value = v;
            }
        "#;
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let checked = check(file, &parsed.ast);
        assert!(checked.diagnostics.has_errors());
        assert!(
            checked.diagnostics.diagnostics[0]
                .message
                .contains("disclose")
        );
    }

    #[test]
    fn rejects_out_of_range_counter_increment() {
        let mut sm = SourceMap::new();
        let src = "export ledger round: Counter; export circuit inc(): [] { round.increment(70000); }";
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        let checked = check(file, &parsed.ast);
        assert!(checked.diagnostics.has_errors());
        assert!(checked.diagnostics.diagnostics[0].message.contains("Uint<16>"));
    }
}
