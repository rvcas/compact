use std::collections::HashMap;
use std::fmt::Write as _;

use compact_ast::{Ast, NodeIndex, NodeTag, TokenIndex, TokenTag};
use compact_diagnostics::{CompactDiagnostic, DiagnosticBag};
use compact_span::{SourceFile, Span};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LedgerFieldId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CircuitId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ParamId(pub u32);

/// Built-in ledger Abstract Data Types from Midnight's ledger specification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LedgerAdt {
    Counter,
}

impl LedgerAdt {
    pub fn name(self) -> &'static str {
        match self {
            Self::Counter => "Counter",
        }
    }
}

/// Resolved operations on ledger ADTs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LedgerOp {
    CounterIncrement,
    CounterDecrement,
    CounterRead,
}

impl LedgerOp {
    pub fn name(self) -> &'static str {
        match self {
            Self::CounterIncrement => "increment",
            Self::CounterDecrement => "decrement",
            Self::CounterRead => "read",
        }
    }

    pub fn is_mutating(self) -> bool {
        matches!(self, Self::CounterIncrement | Self::CounterDecrement)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Field,
    Boolean,
    Uint(u32),
    Tuple(Vec<Type>),
    Adt(LedgerAdt),
}

impl Type {
    pub fn unit() -> Self {
        Self::Tuple(Vec::new())
    }

    pub fn is_unit(&self) -> bool {
        matches!(self, Self::Tuple(elems) if elems.is_empty())
    }
}

#[derive(Debug, Clone)]
pub struct LedgerField {
    pub id: LedgerFieldId,
    pub name: String,
    pub ty: Type,
    pub path: Vec<u32>,
    pub exported: bool,
    pub sealed: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub id: ParamId,
    pub name: String,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    IntLit(u128),
    ParamRef(ParamId),
    Tuple(Vec<Expr>),
    Binary {
        op: BinaryOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    LedgerCall {
        field: LedgerFieldId,
        op: LedgerOp,
        args: Vec<Expr>,
    },
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Expr(Expr),
    Return { value: Option<Expr>, span: Span },
}

#[derive(Debug, Clone)]
pub struct Circuit {
    pub id: CircuitId,
    pub name: String,
    pub params: Vec<Param>,
    pub ret_type: Type,
    pub body: Vec<Stmt>,
    pub exported: bool,
    /// True when the circuit performs no ledger/emit/witness/cross-contract operations.
    pub pure: bool,
    /// True when the circuit is exported and requires a ZK proof (i.e. impure).
    pub proof: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Program {
    pub ledger_fields: Vec<LedgerField>,
    pub circuits: Vec<Circuit>,
}

impl Program {
    pub fn ledger_field(&self, id: LedgerFieldId) -> &LedgerField {
        &self.ledger_fields[id.0 as usize]
    }

    pub fn proof_circuits(&self) -> impl Iterator<Item = &Circuit> {
        self.circuits.iter().filter(|c| c.proof)
    }

    pub fn dump(&self) -> String {
        let mut out = String::new();
        writeln!(out, "HirProgram").unwrap();
        for field in &self.ledger_fields {
            writeln!(
                out,
                "  LedgerField #{} {}{} {}: {:?} @ path={:?}",
                field.id.0,
                if field.exported { "export " } else { "" },
                if field.sealed { "sealed " } else { "" },
                field.name,
                field.ty,
                field.path
            )
            .unwrap();
        }
        for circuit in &self.circuits {
            writeln!(
                out,
                "  Circuit #{} {} (exported={}, pure={}, proof={}) -> {:?}",
                circuit.id.0, circuit.name, circuit.exported, circuit.pure, circuit.proof, circuit.ret_type
            )
            .unwrap();
            for p in &circuit.params {
                writeln!(out, "    Param #{} {}: {:?}", p.id.0, p.name, p.ty).unwrap();
            }
            for stmt in &circuit.body {
                match stmt {
                    Stmt::Expr(e) => writeln!(out, "    ExprStmt {:?}", e.kind).unwrap(),
                    Stmt::Return { value, .. } => writeln!(out, "    Return {:?}", value.as_ref().map(|v| &v.kind)).unwrap(),
                }
            }
        }
        out
    }
}

pub struct LowerResult {
    pub program: Program,
    pub diagnostics: DiagnosticBag,
}

pub fn lower(file: &SourceFile, ast: &Ast) -> LowerResult {
    let mut lowerer = Lowerer {
        file,
        ast,
        diagnostics: DiagnosticBag::new(),
        ledger_fields: Vec::new(),
        ledger_by_name: HashMap::new(),
        circuits: Vec::new(),
        circuits_by_name: HashMap::new(),
    };
    lowerer.lower_program();
    LowerResult {
        program: Program {
            ledger_fields: lowerer.ledger_fields,
            circuits: lowerer.circuits,
        },
        diagnostics: lowerer.diagnostics,
    }
}

struct Lowerer<'a> {
    file: &'a SourceFile,
    ast: &'a Ast,
    diagnostics: DiagnosticBag,
    ledger_fields: Vec<LedgerField>,
    ledger_by_name: HashMap<String, LedgerFieldId>,
    circuits: Vec<Circuit>,
    circuits_by_name: HashMap<String, CircuitId>,
}

impl<'a> Lowerer<'a> {
    fn text(&self, tok: TokenIndex) -> &'a str {
        self.ast.token_text(tok, self.file.text())
    }

    fn lower_program(&mut self) {
        let decls: Vec<_> = self.ast.root_decls().collect();

        // Pass 1: imports & ledger declarations (assign sequential ledger paths [0], [1], ...).
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
                NodeTag::LedgerDecl => self.lower_ledger_decl(decl),
                _ => {}
            }
        }

        // Pass 2: circuits (can reference any ledger field).
        for &decl in &decls {
            if self.ast.node_tag(decl) == NodeTag::CircuitDecl {
                self.lower_circuit_decl(decl);
            }
        }
    }

    fn lower_ledger_decl(&mut self, node: NodeIndex) {
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

        let Some(ty) = self.lower_type(decl.type_node) else {
            return;
        };

        let id = LedgerFieldId(self.ledger_fields.len() as u32);
        let path = vec![id.0];
        self.ledger_fields.push(LedgerField {
            id,
            name: name.clone(),
            ty,
            path,
            exported: decl.exported,
            sealed: decl.sealed,
            span: self.ast.node_span(node),
        });
        self.ledger_by_name.insert(name, id);
    }

    fn lower_circuit_decl(&mut self, node: NodeIndex) {
        let decl = self.ast.circuit_decl(node);
        let name = self.text(decl.name_token).to_owned();
        let name_span = self.ast.token_span(decl.name_token);

        if self.circuits_by_name.contains_key(&name) {
            self.diagnostics.push(CompactDiagnostic::error(
                self.file,
                name_span,
                format!("duplicate circuit `{name}`"),
            ));
            return;
        }

        let mut params = Vec::new();
        let mut param_map = HashMap::new();
        let param_nodes: Vec<_> = self
            .ast
            .extra_nodes(decl.params_start, decl.params_end)
            .collect();
        for pnode in param_nodes {
            let p = self.ast.param(pnode);
            let pname = self.text(p.name_token).to_owned();
            let pspan = self.ast.node_span(pnode);
            if param_map.contains_key(&pname) {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    self.ast.token_span(p.name_token),
                    format!("duplicate parameter `{pname}`"),
                ));
                continue;
            }
            let Some(pty) = self.lower_type(p.type_node) else {
                continue;
            };
            let pid = ParamId(params.len() as u32);
            params.push(Param {
                id: pid,
                name: pname.clone(),
                ty: pty,
                span: pspan,
            });
            param_map.insert(pname, pid);
        }

        let Some(ret_type) = self.lower_type(decl.ret_type) else {
            return;
        };

        let mut touches_ledger = false;
        let mut body = Vec::new();
        let block_data = self.ast.node_data(decl.body);
        let stmt_nodes: Vec<_> = self
            .ast
            .extra_nodes(block_data.lhs, block_data.rhs)
            .collect();

        for snode in stmt_nodes {
            if let Some(stmt) =
                self.lower_stmt(snode, &params, &param_map, &ret_type, &mut touches_ledger)
            {
                body.push(stmt);
            }
        }

        if decl.pure && touches_ledger {
            self.diagnostics.push(CompactDiagnostic::error(
                self.file,
                name_span,
                format!("circuit `{name}` is declared `pure` but accesses ledger state"),
            ));
        }

        let pure = !touches_ledger;
        let proof = decl.exported && !pure;

        let id = CircuitId(self.circuits.len() as u32);
        self.circuits.push(Circuit {
            id,
            name: name.clone(),
            params,
            ret_type,
            body,
            exported: decl.exported,
            pure,
            proof,
            span: self.ast.node_span(node),
        });
        self.circuits_by_name.insert(name, id);
    }

    fn lower_type(&mut self, node: NodeIndex) -> Option<Type> {
        match self.ast.node_tag(node) {
            NodeTag::TypeNamed => {
                let tok = self.ast.node_main_token(node);
                match self.text(tok) {
                    "Field" => Some(Type::Field),
                    "Boolean" => Some(Type::Boolean),
                    "Counter" => Some(Type::Adt(LedgerAdt::Counter)),
                    other => {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            self.ast.token_span(tok),
                            format!("unknown type `{other}`"),
                        ));
                        None
                    }
                }
            }
            NodeTag::TypeTuple => {
                let data = self.ast.node_data(node);
                let elem_nodes: Vec<_> = self.ast.extra_nodes(data.lhs, data.rhs).collect();
                let mut elems = Vec::with_capacity(elem_nodes.len());
                for enode in elem_nodes {
                    elems.push(self.lower_type(enode)?);
                }
                Some(Type::Tuple(elems))
            }
            _ => None,
        }
    }

    fn lower_stmt(
        &mut self,
        node: NodeIndex,
        params: &[Param],
        param_map: &HashMap<String, ParamId>,
        expected_ret: &Type,
        touches_ledger: &mut bool,
    ) -> Option<Stmt> {
        let data = self.ast.node_data(node);
        match self.ast.node_tag(node) {
            NodeTag::ExprStmt => {
                let expr = self.lower_expr(NodeIndex(data.lhs), params, param_map, touches_ledger)?;
                Some(Stmt::Expr(expr))
            }
            NodeTag::ReturnStmt => {
                let span = self.ast.node_span(node);
                let value = if let Some(expr_node) = NodeIndex(data.lhs).into_option() {
                    let expr = self.lower_expr(expr_node, params, param_map, touches_ledger)?;
                    if expr.ty != *expected_ret {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            expr.span,
                            format!(
                                "mismatched return type: expected `{expected_ret:?}`, found `{:?}`",
                                expr.ty
                            ),
                        ));
                    }
                    Some(expr)
                } else {
                    if !expected_ret.is_unit() {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            span,
                            format!("empty `return` in circuit returning `{expected_ret:?}`"),
                        ));
                    }
                    None
                };
                Some(Stmt::Return { value, span })
            }
            _ => None,
        }
    }

    fn lower_expr(
        &mut self,
        node: NodeIndex,
        params: &[Param],
        param_map: &HashMap<String, ParamId>,
        touches_ledger: &mut bool,
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
                Some(Expr {
                    kind: ExprKind::IntLit(val),
                    ty: Type::Uint(64),
                    span,
                })
            }
            NodeTag::IdentExpr => {
                let tok = self.ast.node_main_token(node);
                let name = self.text(tok);
                if let Some(&pid) = param_map.get(name) {
                    return Some(Expr {
                        kind: ExprKind::ParamRef(pid),
                        ty: params[pid.0 as usize].ty.clone(),
                        span,
                    });
                }
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    span,
                    format!("unbound identifier `{name}`"),
                ));
                None
            }
            NodeTag::TupleExpr => {
                let data = self.ast.node_data(node);
                let elem_nodes: Vec<_> = self.ast.extra_nodes(data.lhs, data.rhs).collect();
                let mut exprs = Vec::with_capacity(elem_nodes.len());
                let mut tys = Vec::with_capacity(elem_nodes.len());
                for enode in elem_nodes {
                    let e = self.lower_expr(enode, params, param_map, touches_ledger)?;
                    tys.push(e.ty.clone());
                    exprs.push(e);
                }
                Some(Expr {
                    kind: ExprKind::Tuple(exprs),
                    ty: Type::Tuple(tys),
                    span,
                })
            }
            NodeTag::BinaryExpr => {
                let op_tok = self.ast.node_main_token(node);
                let op = match self.ast.token_tag(op_tok) {
                    TokenTag::Plus => BinaryOp::Add,
                    TokenTag::Minus => BinaryOp::Sub,
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
                let lhs = self.lower_expr(NodeIndex(data.lhs), params, param_map, touches_ledger)?;
                let rhs = self.lower_expr(NodeIndex(data.rhs), params, param_map, touches_ledger)?;
                if lhs.ty != rhs.ty {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        span,
                        format!(
                            "incompatible operand types `{:?}` and `{:?}`",
                            lhs.ty, rhs.ty
                        ),
                    ));
                    return None;
                }
                let ty = lhs.ty.clone();
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
            NodeTag::CallExpr => {
                let call = self.ast.call_expr(node);
                let arg_nodes: Vec<_> = self
                    .ast
                    .extra_nodes(call.args_start, call.args_end)
                    .collect();

                // Ledger ADT method call: `<ledger_field>.<op>(<args>)`
                if self.ast.node_tag(call.callee) == NodeTag::MemberExpr {
                    let mdata = self.ast.node_data(call.callee);
                    let recv = NodeIndex(mdata.lhs);
                    let method_tok = TokenIndex(mdata.rhs);
                    if self.ast.node_tag(recv) == NodeTag::IdentExpr {
                        let recv_name = self.text(self.ast.node_main_token(recv));
                        if let Some(&field_id) = self.ledger_by_name.get(recv_name) {
                            let method_name = self.text(method_tok);
                            return self.lower_ledger_call(
                                field_id,
                                method_name,
                                self.ast.token_span(method_tok),
                                &arg_nodes,
                                span,
                                params,
                                param_map,
                                touches_ledger,
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

    #[allow(clippy::too_many_arguments)]
    fn lower_ledger_call(
        &mut self,
        field_id: LedgerFieldId,
        method_name: &str,
        method_span: Span,
        arg_nodes: &[NodeIndex],
        call_span: Span,
        params: &[Param],
        param_map: &HashMap<String, ParamId>,
        touches_ledger: &mut bool,
    ) -> Option<Expr> {
        let field_ty = self.ledger_fields[field_id.0 as usize].ty.clone();
        match field_ty {
            Type::Adt(LedgerAdt::Counter) => {
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
                    let mut arg = self.lower_expr(anode, params, param_map, touches_ledger)?;
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

                *touches_ledger = true;
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
            other => {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    method_span,
                    format!("ledger type `{other:?}` has no method `{method_name}`"),
                ));
                None
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use compact_parser::parse;
    use compact_span::SourceMap;
    use compact_test_utils::assert_compact_snapshot;

    use super::lower;

    fn lower_and_dump(src: &str) -> String {
        let mut sm = SourceMap::new();
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let lowered = lower(file, &parsed.ast);
        assert!(
            !lowered.diagnostics.has_errors(),
            "unexpected HIR errors: {:?}",
            lowered.diagnostics
        );
        lowered.program.dump()
    }

    #[test]
    fn lower_counter_contract() {
        assert_compact_snapshot!(
            r#"
            import CompactStandardLibrary;

            export ledger round: Counter;

            export circuit increment(): [] {
              round.increment(1);
            }
            "#,
            lower_and_dump
        );
    }

    #[test]
    fn rejects_out_of_range_counter_increment() {
        let mut sm = SourceMap::new();
        let src = "export ledger round: Counter; export circuit inc(): [] { round.increment(70000); }";
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        let lowered = lower(file, &parsed.ast);
        assert!(lowered.diagnostics.has_errors());
        assert!(lowered.diagnostics.diagnostics[0].message.contains("Uint<16>"));
    }
}
