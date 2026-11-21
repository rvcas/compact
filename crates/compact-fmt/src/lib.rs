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
            self.format_decl(decl);
            self.out.push('\n');
        }
    }

    fn decl_first_token(&self, node: NodeIndex) -> TokenIndex {
        let main = self.ast.node_main_token(node);
        match self.ast.node_tag(node) {
            NodeTag::EnumDecl => {
                let d = self.ast.enum_decl(node);
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

    fn format_decl(&mut self, node: NodeIndex) {
        match self.ast.node_tag(node) {
            NodeTag::ImportDecl => {
                let decl = self.ast.import_decl(node);
                write!(
                    self.out,
                    "import {};",
                    self.ast.token_text(decl.name_token, self.source)
                )
                .unwrap();
            }
            NodeTag::EnumDecl => {
                let decl = self.ast.enum_decl(node);
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
            NodeTag::LedgerDecl => {
                let decl = self.ast.ledger_decl(node);
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
            NodeTag::CircuitDecl => {
                let decl = self.ast.circuit_decl(node);
                if decl.exported {
                    self.out.push_str("export ");
                }
                if decl.pure {
                    self.out.push_str("pure ");
                }
                write!(
                    self.out,
                    "circuit {}(",
                    self.ast.token_text(decl.name_token, self.source)
                )
                .unwrap();
                let params: Vec<_> = self
                    .ast
                    .extra_nodes(decl.params_start, decl.params_end)
                    .collect();
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
                self.out.push_str("): ");
                self.format_type(decl.ret_type);
                self.out.push(' ');
                self.format_block(decl.body, 0);
            }
            _ => {}
        }
    }

    fn format_type(&mut self, node: NodeIndex) {
        let data = self.ast.node_data(node);
        match self.ast.node_tag(node) {
            NodeTag::TypeNamed => {
                self.out
                    .push_str(self.ast.token_text(self.ast.node_main_token(node), self.source));
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
            self.format_stmt(stmt);
            self.out.push('\n');
        }
        self.out.push_str(&"  ".repeat(indent));
        self.out.push('}');
    }

    fn format_stmt(&mut self, node: NodeIndex) {
        let data = self.ast.node_data(node);
        match self.ast.node_tag(node) {
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
                self.out
                    .push_str(self.ast.token_text(self.ast.node_main_token(node), self.source));
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
            NodeTag::UnaryExpr => {
                self.out
                    .push_str(self.ast.token_text(self.ast.node_main_token(node), self.source));
                self.format_expr(NodeIndex(data.lhs));
            }
            NodeTag::BinaryExpr => {
                self.format_expr(NodeIndex(data.lhs));
                write!(
                    self.out,
                    " {} ",
                    self.ast.token_text(self.ast.node_main_token(node), self.source)
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
        assert!(!parsed.diagnostics.has_errors());
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
}
