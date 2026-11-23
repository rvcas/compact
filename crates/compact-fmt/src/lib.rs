use std::fmt::Write as _;

use compact_ast::{Ast, NodeIndex, NodeTag, TokenIndex};

pub struct FormatOptions {
    pub line_length: usize,
}

impl Default for FormatOptions {
    fn default() -> Self {
        Self { line_length: 100 }
    }
}

/// Format a parsed Compact AST back into canonical source code, preserving comments.
pub fn format_ast(ast: &Ast, source: &str, _options: &FormatOptions) -> String {
    let mut fmt = Formatter {
        ast,
        source,
        out: String::with_capacity(source.len()),
        next_comment: 0,
    };
    fmt.format_root();
    fmt.flush_trailing_comments();
    fmt.out
}

struct Formatter<'a> {
    ast: &'a Ast,
    source: &'a str,
    out: String,
    next_comment: usize,
}

impl<'a> Formatter<'a> {
    fn emit_comments_before(&mut self, tok: TokenIndex, indent: usize) {
        let before_tokens = self.ast.comments.before_token();
        let spans = self.ast.comments.span();
        let pad = "  ".repeat(indent);
        while self.next_comment < before_tokens.len() && before_tokens[self.next_comment] <= tok {
            let text = spans[self.next_comment].slice(self.source).trim_end();
            writeln!(self.out, "{pad}{text}").unwrap();
            self.next_comment += 1;
        }
    }

    fn flush_trailing_comments(&mut self) {
        let spans = self.ast.comments.span();
        while self.next_comment < spans.len() {
            let text = spans[self.next_comment].slice(self.source).trim_end();
            writeln!(self.out, "{text}").unwrap();
            self.next_comment += 1;
        }
    }

    fn format_root(&mut self) {
        let decls: Vec<_> = self.ast.root_decls().collect();
        for (i, decl) in decls.into_iter().enumerate() {
            if i > 0 {
                self.out.push('\n');
            }
            let first_tok = self.decl_first_token(decl);
            self.emit_comments_before(first_tok, 0);
            self.format_decl(decl, 0);
            self.out.push('\n');
        }
    }

    fn decl_first_token(&self, node: NodeIndex) -> TokenIndex {
        let main = self.ast.node_main_token(node);
        match self.ast.node_tag(node) {
            NodeTag::ModuleDecl => {
                let d = self.ast.module_decl(node);
                if d.exported {
                    TokenIndex(main.0.saturating_sub(1))
                } else {
                    main
                }
            }
            NodeTag::TypeDecl => {
                let d = self.ast.type_decl(node);
                let mut offset = 0u32;
                if d.exported {
                    offset += 1;
                }
                if d.is_new {
                    offset += 1;
                }
                TokenIndex(main.0.saturating_sub(offset))
            }
            NodeTag::EnumDecl => {
                let d = self.ast.enum_decl(node);
                if d.exported {
                    TokenIndex(main.0.saturating_sub(1))
                } else {
                    main
                }
            }
            NodeTag::StructDecl => {
                let d = self.ast.struct_decl(node);
                if d.exported {
                    TokenIndex(main.0.saturating_sub(1))
                } else {
                    main
                }
            }
            NodeTag::WitnessDecl => {
                let d = self.ast.witness_decl(node);
                if d.exported {
                    TokenIndex(main.0.saturating_sub(1))
                } else {
                    main
                }
            }
            NodeTag::LedgerDecl => {
                let d = self.ast.ledger_decl(node);
                let mut offset = 0u32;
                if d.exported {
                    offset += 1;
                }
                if d.sealed {
                    offset += 1;
                }
                TokenIndex(main.0.saturating_sub(offset))
            }
            NodeTag::CircuitDecl => {
                let d = self.ast.circuit_decl(node);
                let mut offset = 0u32;
                if d.exported {
                    offset += 1;
                }
                if d.pure {
                    offset += 1;
                }
                TokenIndex(main.0.saturating_sub(offset))
            }
            _ => main,
        }
    }

    fn format_generic_params(&mut self, start: u32, end: u32) {
        if start == end {
            return;
        }
        self.out.push('<');
        let gps: Vec<_> = self.ast.extra_nodes(start, end).collect();
        for (i, gp_node) in gps.into_iter().enumerate() {
            if i > 0 {
                self.out.push_str(", ");
            }
            let gp = self.ast.generic_param(gp_node);
            if gp.is_nat {
                self.out.push('#');
            }
            self.out
                .push_str(self.ast.token_text(gp.name_token, self.source));
        }
        self.out.push('>');
    }

    fn format_version_expr(&mut self, node: NodeIndex) {
        let data = self.ast.node_data(node);
        match self.ast.node_tag(node) {
            NodeTag::VersionAtom => {
                self.out
                    .push_str(self.ast.node_span(node).slice(self.source));
            }
            NodeTag::VersionUnary => {
                let op = self
                    .ast
                    .token_text(self.ast.node_main_token(node), self.source);
                self.out.push_str(op);
                if op != "!" {
                    self.out.push(' ');
                }
                self.format_version_expr(NodeIndex(data.lhs));
            }
            NodeTag::VersionBinary => {
                self.format_version_expr(NodeIndex(data.lhs));
                write!(
                    self.out,
                    " {} ",
                    self.ast
                        .token_text(self.ast.node_main_token(node), self.source)
                )
                .unwrap();
                self.format_version_expr(NodeIndex(data.rhs));
            }
            _ => {}
        }
    }

    fn format_decl(&mut self, node: NodeIndex, indent: usize) {
        let pad = "  ".repeat(indent);
        match self.ast.node_tag(node) {
            NodeTag::PragmaDecl => {
                let decl = self.ast.pragma_decl(node);
                write!(
                    self.out,
                    "{pad}pragma {} ",
                    self.ast.token_text(decl.name_token, self.source)
                )
                .unwrap();
                self.format_version_expr(decl.expr);
                self.out.push(';');
            }
            NodeTag::IncludeDecl => {
                let decl = self.ast.include_decl(node);
                write!(
                    self.out,
                    "{pad}include {};",
                    self.ast.token_text(decl.path_token, self.source)
                )
                .unwrap();
            }
            NodeTag::ModuleDecl => {
                let decl = self.ast.module_decl(node);
                self.out.push_str(&pad);
                if decl.exported {
                    self.out.push_str("export ");
                }
                write!(
                    self.out,
                    "module {}",
                    self.ast.token_text(decl.name_token, self.source)
                )
                .unwrap();
                self.format_generic_params(decl.gparams_start, decl.gparams_end);
                let inner: Vec<_> = self
                    .ast
                    .extra_nodes(decl.decls_start, decl.decls_end)
                    .collect();
                if inner.is_empty() {
                    self.out.push_str(" {}");
                } else {
                    self.out.push_str(" {\n");
                    for (i, d) in inner.into_iter().enumerate() {
                        if i > 0 {
                            self.out.push('\n');
                        }
                        let first_tok = self.decl_first_token(d);
                        self.emit_comments_before(first_tok, indent + 1);
                        self.format_decl(d, indent + 1);
                        self.out.push('\n');
                    }
                    write!(self.out, "{pad}}}").unwrap();
                }
            }
            NodeTag::ImportDecl => {
                let decl = self.ast.import_decl(node);
                write!(self.out, "{pad}import ").unwrap();
                let items: Vec<_> = self
                    .ast
                    .extra_nodes(decl.items_start, decl.items_end)
                    .collect();
                if !items.is_empty() {
                    self.out.push_str("{ ");
                    for (i, item_node) in items.into_iter().enumerate() {
                        if i > 0 {
                            self.out.push_str(", ");
                        }
                        let item = self.ast.import_item(item_node);
                        self.out
                            .push_str(self.ast.token_text(item.name_token, self.source));
                        if let Some(alias) = item.alias_token {
                            write!(self.out, " as {}", self.ast.token_text(alias, self.source))
                                .unwrap();
                        }
                    }
                    self.out.push_str(" } from ");
                }
                self.out
                    .push_str(self.ast.token_text(decl.name_token, self.source));
                let gargs: Vec<_> = self
                    .ast
                    .extra_nodes(decl.gargs_start, decl.gargs_end)
                    .collect();
                if !gargs.is_empty() {
                    self.out.push('<');
                    for (i, garg) in gargs.into_iter().enumerate() {
                        if i > 0 {
                            self.out.push_str(", ");
                        }
                        self.format_type(garg);
                    }
                    self.out.push('>');
                }
                if let Some(prefix) = decl.prefix_token {
                    write!(
                        self.out,
                        " prefix {}",
                        self.ast.token_text(prefix, self.source)
                    )
                    .unwrap();
                }
                self.out.push(';');
            }
            NodeTag::ExportListDecl => {
                let decl = self.ast.export_list_decl(node);
                let names: Vec<_> = self
                    .ast
                    .extra_tokens(decl.names_start, decl.names_end)
                    .map(|t| self.ast.token_text(t, self.source))
                    .collect();
                write!(self.out, "{pad}export {{ {} }};", names.join(", ")).unwrap();
            }
            NodeTag::TypeDecl => {
                let decl = self.ast.type_decl(node);
                self.out.push_str(&pad);
                if decl.exported {
                    self.out.push_str("export ");
                }
                if decl.is_new {
                    self.out.push_str("new ");
                }
                write!(
                    self.out,
                    "type {}",
                    self.ast.token_text(decl.name_token, self.source)
                )
                .unwrap();
                self.format_generic_params(decl.gparams_start, decl.gparams_end);
                self.out.push_str(" = ");
                self.format_type(decl.target_type);
                self.out.push(';');
            }
            NodeTag::EnumDecl => {
                let decl = self.ast.enum_decl(node);
                self.out.push_str(&pad);
                if decl.exported {
                    self.out.push_str("export ");
                }
                let variants: Vec<_> = self
                    .ast
                    .extra_tokens(decl.variants_start, decl.variants_end)
                    .map(|t| self.ast.token_text(t, self.source))
                    .collect();
                write!(
                    self.out,
                    "enum {} {{ {} }}",
                    self.ast.token_text(decl.name_token, self.source),
                    variants.join(", ")
                )
                .unwrap();
            }
            NodeTag::StructDecl => {
                let decl = self.ast.struct_decl(node);
                self.out.push_str(&pad);
                if decl.exported {
                    self.out.push_str("export ");
                }
                write!(
                    self.out,
                    "struct {}",
                    self.ast.token_text(decl.name_token, self.source)
                )
                .unwrap();
                self.format_generic_params(decl.gparams_start, decl.gparams_end);
                self.out.push_str(" {\n");
                let fields: Vec<_> = self
                    .ast
                    .extra_nodes(decl.fields_start, decl.fields_end)
                    .collect();
                for f in fields {
                    let sf = self.ast.struct_field(f);
                    write!(
                        self.out,
                        "{pad}  {}: ",
                        self.ast.token_text(sf.name_token, self.source)
                    )
                    .unwrap();
                    self.format_type(sf.type_node);
                    self.out.push_str(";\n");
                }
                write!(self.out, "{pad}}}").unwrap();
            }
            NodeTag::LedgerDecl => {
                let decl = self.ast.ledger_decl(node);
                self.out.push_str(&pad);
                if decl.exported {
                    self.out.push_str("export ");
                }
                if decl.sealed {
                    self.out.push_str("sealed ");
                }
                write!(
                    self.out,
                    "ledger {}: ",
                    self.ast.token_text(decl.name_token, self.source)
                )
                .unwrap();
                self.format_type(decl.type_node);
                self.out.push(';');
            }
            NodeTag::WitnessDecl => {
                let decl = self.ast.witness_decl(node);
                self.out.push_str(&pad);
                if decl.exported {
                    self.out.push_str("export ");
                }
                write!(
                    self.out,
                    "witness {}",
                    self.ast.token_text(decl.name_token, self.source)
                )
                .unwrap();
                self.format_generic_params(decl.gparams_start, decl.gparams_end);
                self.out.push('(');
                self.format_params(decl.params_start, decl.params_end);
                self.out.push_str("): ");
                self.format_type(decl.ret_type);
                self.out.push(';');
            }
            NodeTag::ConstructorDecl => {
                let decl = self.ast.constructor_decl(node);
                write!(self.out, "{pad}constructor(").unwrap();
                self.format_params(decl.params_start, decl.params_end);
                self.out.push_str(") ");
                self.format_block(decl.body, indent);
            }
            NodeTag::CircuitDecl => {
                let decl = self.ast.circuit_decl(node);
                self.out.push_str(&pad);
                if decl.exported {
                    self.out.push_str("export ");
                }
                if decl.pure {
                    self.out.push_str("pure ");
                }
                write!(
                    self.out,
                    "circuit {}",
                    self.ast.token_text(decl.name_token, self.source)
                )
                .unwrap();
                self.format_generic_params(decl.gparams_start, decl.gparams_end);
                self.out.push('(');
                self.format_params(decl.params_start, decl.params_end);
                self.out.push_str("): ");
                self.format_type(decl.ret_type);
                self.out.push(' ');
                self.format_block(decl.body, indent);
            }
            _ => {}
        }
    }

    fn format_params(&mut self, start: u32, end: u32) {
        let params: Vec<_> = self.ast.extra_nodes(start, end).collect();
        for (i, param) in params.into_iter().enumerate() {
            if i > 0 {
                self.out.push_str(", ");
            }
            let p = self.ast.param(param);
            write!(
                self.out,
                "{}: ",
                self.ast.token_text(p.name_token, self.source)
            )
            .unwrap();
            self.format_type(p.type_node);
        }
    }

    fn format_type(&mut self, node: NodeIndex) {
        let data = self.ast.node_data(node);
        match self.ast.node_tag(node) {
            NodeTag::TypeNamed | NodeTag::TypeNat | NodeTag::TypeString => {
                self.out.push_str(
                    self.ast
                        .token_text(self.ast.node_main_token(node), self.source),
                );
            }
            NodeTag::TypeGeneric => {
                self.out.push_str(
                    self.ast
                        .token_text(self.ast.node_main_token(node), self.source),
                );
                self.out.push('<');
                let args: Vec<_> = self.ast.extra_nodes(data.lhs, data.rhs).collect();
                for (i, arg) in args.into_iter().enumerate() {
                    if i > 0 {
                        self.out.push_str(", ");
                    }
                    self.format_type(arg);
                }
                self.out.push('>');
            }
            NodeTag::TypeTuple => {
                self.out.push('[');
                let elems: Vec<_> = self.ast.extra_nodes(data.lhs, data.rhs).collect();
                for (i, elem) in elems.into_iter().enumerate() {
                    if i > 0 {
                        self.out.push_str(", ");
                    }
                    self.format_type(elem);
                }
                self.out.push(']');
            }
            _ => {}
        }
    }

    fn format_block(&mut self, node: NodeIndex, indent: usize) {
        let data = self.ast.node_data(node);
        let stmts: Vec<_> = self.ast.extra_nodes(data.lhs, data.rhs).collect();
        if stmts.is_empty() {
            self.out.push_str("{}");
            return;
        }
        self.out.push_str("{\n");
        let inner_pad = "  ".repeat(indent + 1);
        for stmt in stmts {
            let tok = self.ast.node_main_token(stmt);
            self.emit_comments_before(tok, indent + 1);
            self.out.push_str(&inner_pad);
            self.format_stmt(stmt, indent + 1);
            self.out.push('\n');
        }
        self.out.push_str(&"  ".repeat(indent));
        self.out.push('}');
    }

    fn format_stmt(&mut self, node: NodeIndex, indent: usize) {
        let data = self.ast.node_data(node);
        match self.ast.node_tag(node) {
            NodeTag::IfStmt => {
                let stmt = self.ast.if_stmt(node);
                self.out.push_str("if (");
                self.format_expr(stmt.cond);
                self.out.push_str(") ");
                if self.ast.node_tag(stmt.then_branch) == NodeTag::Block {
                    self.format_block(stmt.then_branch, indent);
                } else {
                    self.format_stmt(stmt.then_branch, indent);
                }
                if let Some(else_branch) = stmt.else_branch {
                    self.out.push_str(" else ");
                    match self.ast.node_tag(else_branch) {
                        NodeTag::IfStmt => self.format_stmt(else_branch, indent),
                        NodeTag::Block => self.format_block(else_branch, indent),
                        _ => self.format_stmt(else_branch, indent),
                    }
                }
            }
            NodeTag::ForRangeStmt => {
                let stmt = self.ast.for_range_stmt(node);
                write!(
                    self.out,
                    "for (const {} of ",
                    self.ast.token_text(stmt.name_token, self.source)
                )
                .unwrap();
                self.format_expr(stmt.start);
                self.out.push_str("..");
                self.format_expr(stmt.end);
                self.out.push_str(") ");
                if self.ast.node_tag(stmt.body) == NodeTag::Block {
                    self.format_block(stmt.body, indent);
                } else {
                    self.format_stmt(stmt.body, indent);
                }
            }
            NodeTag::ForEachStmt => {
                let stmt = self.ast.for_each_stmt(node);
                write!(
                    self.out,
                    "for (const {} of ",
                    self.ast.token_text(stmt.name_token, self.source)
                )
                .unwrap();
                self.format_expr(stmt.iter);
                self.out.push_str(") ");
                if self.ast.node_tag(stmt.body) == NodeTag::Block {
                    self.format_block(stmt.body, indent);
                } else {
                    self.format_stmt(stmt.body, indent);
                }
            }
            NodeTag::ConstStmt => {
                let stmt = self.ast.const_stmt(node);
                write!(
                    self.out,
                    "const {}",
                    self.ast.token_text(stmt.name_token, self.source)
                )
                .unwrap();
                if let Some(ty) = stmt.ty {
                    self.out.push_str(": ");
                    self.format_type(ty);
                }
                self.out.push_str(" = ");
                self.format_expr(stmt.init);
                self.out.push(';');
            }
            NodeTag::AssignStmt => {
                let stmt = self.ast.assign_stmt(node);
                self.format_expr(stmt.lhs);
                self.out.push_str(" = ");
                self.format_expr(stmt.rhs);
                self.out.push(';');
            }
            NodeTag::ExprStmt => {
                self.format_expr(NodeIndex(data.lhs));
                self.out.push(';');
            }
            NodeTag::ReturnStmt => {
                self.out.push_str("return");
                if let Some(expr) = NodeIndex(data.lhs).into_option() {
                    self.out.push(' ');
                    self.format_expr(expr);
                }
                self.out.push(';');
            }
            _ => {}
        }
    }

    fn format_expr(&mut self, node: NodeIndex) {
        let data = self.ast.node_data(node);
        match self.ast.node_tag(node) {
            NodeTag::IdentExpr
            | NodeTag::IntLitExpr
            | NodeTag::BoolLitExpr
            | NodeTag::StringLitExpr => {
                self.out.push_str(
                    self.ast
                        .token_text(self.ast.node_main_token(node), self.source),
                );
            }
            NodeTag::TupleExpr => {
                self.out.push('[');
                let elems: Vec<_> = self.ast.extra_nodes(data.lhs, data.rhs).collect();
                for (i, elem) in elems.into_iter().enumerate() {
                    if i > 0 {
                        self.out.push_str(", ");
                    }
                    self.format_expr(elem);
                }
                self.out.push(']');
            }
            NodeTag::MemberExpr => {
                self.format_expr(NodeIndex(data.lhs));
                self.out.push('.');
                self.out
                    .push_str(self.ast.token_text(TokenIndex(data.rhs), self.source));
            }
            NodeTag::IndexExpr => {
                let idx = self.ast.index_expr(node);
                self.format_expr(idx.base);
                self.out.push('[');
                self.format_expr(idx.index);
                self.out.push(']');
            }
            NodeTag::CallExpr => {
                let call = self.ast.call_expr(node);
                self.format_expr(call.callee);
                self.out.push('(');
                let args: Vec<_> = self
                    .ast
                    .extra_nodes(call.args_start, call.args_end)
                    .collect();
                for (i, arg) in args.into_iter().enumerate() {
                    if i > 0 {
                        self.out.push_str(", ");
                    }
                    self.format_expr(arg);
                }
                self.out.push(')');
            }
            NodeTag::GenericCallExpr => {
                let call = self.ast.generic_call_expr(node);
                self.format_expr(call.callee);
                self.out.push('<');
                let targs: Vec<_> = self
                    .ast
                    .extra_nodes(call.targs_start, call.targs_end)
                    .collect();
                for (i, targ) in targs.into_iter().enumerate() {
                    if i > 0 {
                        self.out.push_str(", ");
                    }
                    self.format_type(targ);
                }
                self.out.push_str(">(");
                let args: Vec<_> = self
                    .ast
                    .extra_nodes(call.args_start, call.args_end)
                    .collect();
                for (i, arg) in args.into_iter().enumerate() {
                    if i > 0 {
                        self.out.push_str(", ");
                    }
                    self.format_expr(arg);
                }
                self.out.push(')');
            }
            NodeTag::UnaryExpr => {
                self.out.push_str(
                    self.ast
                        .token_text(self.ast.node_main_token(node), self.source),
                );
                self.format_expr(NodeIndex(data.lhs));
            }
            NodeTag::BinaryExpr => {
                self.format_expr(NodeIndex(data.lhs));
                write!(
                    self.out,
                    " {} ",
                    self.ast
                        .token_text(self.ast.node_main_token(node), self.source)
                )
                .unwrap();
                self.format_expr(NodeIndex(data.rhs));
            }
            NodeTag::TernaryExpr => {
                let t = self.ast.ternary_expr(node);
                self.format_expr(t.cond);
                self.out.push_str(" ? ");
                self.format_expr(t.then_branch);
                self.out.push_str(" : ");
                self.format_expr(t.else_branch);
            }
            NodeTag::CastExpr => {
                self.format_expr(NodeIndex(data.lhs));
                self.out.push_str(" as ");
                self.format_type(NodeIndex(data.rhs));
            }
            NodeTag::DefaultExpr => {
                self.out.push_str("default<");
                self.format_type(NodeIndex(data.lhs));
                self.out.push('>');
            }
            NodeTag::AssertExpr => {
                let a = self.ast.assert_expr(node);
                self.out.push_str("assert(");
                self.format_expr(a.cond);
                self.out.push_str(", ");
                self.format_expr(a.msg);
                self.out.push(')');
            }
            NodeTag::DiscloseExpr => {
                self.out.push_str("disclose(");
                self.format_expr(NodeIndex(data.lhs));
                self.out.push(')');
            }
            NodeTag::StructLitExpr => {
                let lit = self.ast.struct_lit_expr(node);
                self.format_type(lit.type_node);
                self.out.push_str("{ ");
                let fields: Vec<_> = self
                    .ast
                    .extra_nodes(lit.fields_start, lit.fields_end)
                    .collect();
                for (i, f) in fields.into_iter().enumerate() {
                    if i > 0 {
                        self.out.push_str(", ");
                    }
                    let sf = self.ast.struct_lit_field(f);
                    write!(
                        self.out,
                        "{}: ",
                        self.ast.token_text(sf.name_token, self.source)
                    )
                    .unwrap();
                    self.format_expr(sf.value);
                }
                self.out.push_str(" }");
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use compact_parser::parse;
    use compact_span::SourceMap;
    use compact_test_utils::assert_compact_snapshot;

    use super::{FormatOptions, format_ast};

    fn fmt(src: &str) -> String {
        let mut sm = SourceMap::new();
        let id = sm.add_file("test.compact", src);
        let parsed = parse(sm.get(id));
        assert!(
            !parsed.diagnostics.has_errors(),
            "unexpected parse errors: {:?}",
            parsed.diagnostics
        );
        format_ast(&parsed.ast, src, &FormatOptions::default())
    }

    #[test]
    fn format_messy_counter() {
        assert_compact_snapshot!(
            r#"
            // Counter contract
            import   CompactStandardLibrary ;
            export  ledger   round : Counter ;
            export circuit increment( ):[]{round.increment( 1 );}
            "#,
            fmt
        );
    }

    #[test]
    fn format_cell_and_enum() {
        assert_compact_snapshot!(
            r#"
            enum   STATE{unset,set}
            export ledger value:Field;
            ledger state:STATE;
            circuit in_state(s:STATE):Boolean{return state==s;}
            export circuit set(v:Field):[]{assert(in_state(STATE.unset),"overwrite");const dv=disclose(v);value=dv;state=STATE.set;}
            "#,
            fmt
        );
    }

    #[test]
    fn format_tiny_contract() {
        assert_compact_snapshot!(
            r#"
            export{Maybe}
            export{set,get,clear,public_key}
            import CompactStandardLibrary;
            enum STATE{unset,set}
            ledger authority:Bytes<32>;
            export ledger value:Field;
            ledger state:STATE;
            constructor(v:Field){const sk=private$secret_key();authority=public_key(sk);value=disclose(v);state=STATE.set;}
            witness private$secret_key():Bytes<32>;
            circuit get():Maybe<Field>{return state==STATE.set?some<Field>(value):none<Field>();}
            circuit clear():[]{authority=default<Bytes<32>>;value=default<Field>;state=STATE.unset;}
            circuit public_key(sk:Bytes<32>):Bytes<32>{return disclose(persistentHash<Vector<2,Bytes<32>>>([pad(32,"lares:tiny:pk:"),sk]));}
            "#,
            fmt
        );
    }

    #[test]
    fn format_struct_if_and_opaque() {
        assert_compact_snapshot!(
            r#"
            struct Pair{a:Field;b:Opaque<"string">;}
            enum State{a,b,c,}
            ledger s:State;
            ledger t:Maybe<Opaque<"string">>;
            circuit next(x:State):State{if(x==State.a&&true){return State.b;}else if(x==State.b||false){return State.c;}else{return State.a;}}
            circuit set_t(v:Opaque<"string">):[]{t.write(Maybe<Opaque<"string">>{is_some:true,value:disclose(v)});}
            "#,
            fmt
        );
    }

    #[test]
    fn format_for_loops_and_adts() {
        assert_compact_snapshot!(
            r#"
            import CompactStandardLibrary;
            export ledger nested:Map<Boolean,Map<Field,Counter>>;
            export ledger queue:List<Field>;
            export circuit run(xs:Vector<3,Field>,a:Uint<32>,b:Uint<32>):Boolean{for(const i of 0..3){nested.lookup(true).insert(i as Field,default<Counter>);}for(const x of xs){queue.pushFront(disclose(x));}return a*b<=100&&a<b&&b>=a&&b>0;}
            "#,
            fmt
        );
    }

    #[test]
    fn format_modules_pragma_generics_and_types() {
        assert_compact_snapshot!(
            r#"
            pragma language_version >= 0.16.0 && <= 1.0.0;
            import CompactStandardLibrary;
            include "types";
            export new type Tag<#N> = Bytes<N>;
            struct Pair<A,B>{first:A;second:B;}
            module Vault<K>{export ledger m:Map<K,Counter>;export circuit bump(k:K):[]{m.lookup(k).increment(1);}}
            import {bump as bump_field} from Vault<Field> prefix V_;
            export circuit pick<T>(v:Vector<3,T>,i:Uint<8>):T{const x:T=v[i];return x;}
            "#,
            fmt
        );
    }
}
