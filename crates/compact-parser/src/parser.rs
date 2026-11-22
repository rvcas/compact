use compact_ast::{Ast, NodeData, NodeIndex, NodeTag, TokenIndex, TokenTag, decl_flags};
use compact_diagnostics::{CompactDiagnostic, DiagnosticBag};
use compact_span::SourceFile;

use crate::lexer::lex;

pub struct ParseResult {
    pub ast: Ast,
    pub diagnostics: DiagnosticBag,
}

pub fn parse(file: &SourceFile) -> ParseResult {
    let mut diagnostics = DiagnosticBag::new();
    let lex_out = lex(file, &mut diagnostics);
    let mut parser = Parser {
        file,
        ast: Ast::new(lex_out.tokens, lex_out.comments),
        cursor: 0,
        diagnostics,
    };
    parser.parse_program();
    ParseResult {
        ast: parser.ast,
        diagnostics: parser.diagnostics,
    }
}

struct Parser<'a> {
    file: &'a SourceFile,
    ast: Ast,
    cursor: u32,
    diagnostics: DiagnosticBag,
}

impl<'a> Parser<'a> {
    #[inline]
    fn current_tok(&self) -> TokenIndex {
        TokenIndex(self.cursor)
    }

    #[inline]
    fn peek(&self) -> TokenTag {
        self.ast.token_tag(self.current_tok())
    }

    #[inline]
    fn peek_at(&self, offset: u32) -> TokenTag {
        let idx = (self.cursor + offset) as usize;
        let tags = self.ast.tokens.tag();
        if idx < tags.len() {
            tags[idx]
        } else {
            TokenTag::Eof
        }
    }

    #[inline]
    fn advance(&mut self) -> TokenIndex {
        let tok = self.current_tok();
        if self.peek() != TokenTag::Eof {
            self.cursor += 1;
        }
        tok
    }

    fn expect(&mut self, expected: TokenTag) -> Option<TokenIndex> {
        if self.peek() == expected {
            Some(self.advance())
        } else {
            let tok = self.current_tok();
            let found = self.ast.token_tag(tok);
            self.diagnostics.push(CompactDiagnostic::error(
                self.file,
                self.ast.token_span(tok),
                format!("expected `{}`, found `{}`", expected.as_str(), found.as_str()),
            ));
            None
        }
    }

    fn parse_program(&mut self) {
        let root = self
            .ast
            .push_node(NodeTag::Root, TokenIndex(0), NodeData::default());
        debug_assert_eq!(root, NodeIndex::ROOT);

        let mut decls = Vec::new();
        while self.peek() != TokenTag::Eof {
            if let Some(decl) = self.parse_program_element() {
                decls.push(decl.0);
            } else {
                self.advance();
            }
        }

        let (start, end) = self.ast.push_extra_slice(&decls);
        self.ast.nodes.data_mut()[NodeIndex::ROOT.as_usize()] = NodeData::new(start, end);
    }

    fn parse_program_element(&mut self) -> Option<NodeIndex> {
        match self.peek() {
            TokenTag::Import => self.parse_import_decl(),
            TokenTag::Export if self.peek_at(1) == TokenTag::LBrace => self.parse_export_list(),
            TokenTag::Constructor => self.parse_constructor_decl(),
            TokenTag::Export
            | TokenTag::Sealed
            | TokenTag::Ledger
            | TokenTag::Pure
            | TokenTag::Circuit
            | TokenTag::Witness
            | TokenTag::Enum
            | TokenTag::Struct => self.parse_decl(),
            other => {
                let tok = self.current_tok();
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    self.ast.token_span(tok),
                    format!("unexpected token `{}` at top level", other.as_str()),
                ));
                None
            }
        }
    }

    fn parse_import_decl(&mut self) -> Option<NodeIndex> {
        let import_tok = self.expect(TokenTag::Import)?;
        let name_tok = self.expect(TokenTag::Ident)?;
        self.expect(TokenTag::Semi)?;
        Some(self.ast.push_node(
            NodeTag::ImportDecl,
            import_tok,
            NodeData::new(name_tok.0, 0),
        ))
    }

    fn parse_export_list(&mut self) -> Option<NodeIndex> {
        let export_tok = self.expect(TokenTag::Export)?;
        self.expect(TokenTag::LBrace)?;
        let mut names = Vec::new();
        while self.peek() != TokenTag::RBrace && self.peek() != TokenTag::Eof {
            let name_tok = self.expect(TokenTag::Ident)?;
            names.push(name_tok.0);
            if self.peek() == TokenTag::Comma {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(TokenTag::RBrace)?;
        if self.peek() == TokenTag::Semi {
            self.advance();
        }
        let (start, end) = self.ast.push_extra_slice(&names);
        Some(self.ast.push_node(
            NodeTag::ExportListDecl,
            export_tok,
            NodeData::new(start, end),
        ))
    }

    fn parse_decl(&mut self) -> Option<NodeIndex> {
        let mut flags = decl_flags::NONE;
        if self.peek() == TokenTag::Export {
            self.advance();
            flags |= decl_flags::EXPORT;
        }
        if self.peek() == TokenTag::Sealed {
            self.advance();
            flags |= decl_flags::SEALED;
        }
        if self.peek() == TokenTag::Pure {
            self.advance();
            flags |= decl_flags::PURE;
        }

        match self.peek() {
            TokenTag::Enum => self.parse_enum_decl(flags),
            TokenTag::Struct => self.parse_struct_decl(flags),
            TokenTag::Ledger => self.parse_ledger_decl(flags),
            TokenTag::Witness => self.parse_witness_decl(flags),
            TokenTag::Circuit => self.parse_circuit_decl(flags),
            other => {
                let tok = self.current_tok();
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    self.ast.token_span(tok),
                    format!(
                        "expected `enum`, `struct`, `ledger`, `witness`, or `circuit` after modifiers, found `{}`",
                        other.as_str()
                    ),
                ));
                None
            }
        }
    }

    fn parse_struct_decl(&mut self, flags: u32) -> Option<NodeIndex> {
        let struct_tok = self.expect(TokenTag::Struct)?;
        let name_tok = self.expect(TokenTag::Ident)?;
        self.expect(TokenTag::LBrace)?;
        let mut fields = Vec::new();
        while self.peek() != TokenTag::RBrace && self.peek() != TokenTag::Eof {
            let fname = self.expect(TokenTag::Ident)?;
            self.expect(TokenTag::Colon)?;
            let fty = self.parse_type()?;
            let field = self
                .ast
                .push_node(NodeTag::StructField, fname, NodeData::new(fty.0, 0));
            fields.push(field.0);
            if matches!(self.peek(), TokenTag::Semi | TokenTag::Comma) {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(TokenTag::RBrace)?;
        if self.peek() == TokenTag::Semi {
            self.advance();
        }
        let (fstart, fend) = self.ast.push_extra_slice(&fields);
        let (extra_start, _) = self.ast.push_extra_slice(&[name_tok.0, fstart, fend]);
        Some(self.ast.push_node(
            NodeTag::StructDecl,
            struct_tok,
            NodeData::new(extra_start, flags),
        ))
    }

    fn parse_enum_decl(&mut self, flags: u32) -> Option<NodeIndex> {
        let enum_tok = self.expect(TokenTag::Enum)?;
        let name_tok = self.expect(TokenTag::Ident)?;
        self.expect(TokenTag::LBrace)?;
        let mut variants = Vec::new();
        while self.peek() != TokenTag::RBrace && self.peek() != TokenTag::Eof {
            let vtok = self.expect(TokenTag::Ident)?;
            variants.push(vtok.0);
            if self.peek() == TokenTag::Comma {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(TokenTag::RBrace)?;
        if self.peek() == TokenTag::Semi {
            self.advance();
        }
        let (vstart, vend) = self.ast.push_extra_slice(&variants);
        let (extra_start, _) = self.ast.push_extra_slice(&[name_tok.0, vstart, vend]);
        Some(self.ast.push_node(
            NodeTag::EnumDecl,
            enum_tok,
            NodeData::new(extra_start, flags),
        ))
    }

    fn parse_ledger_decl(&mut self, flags: u32) -> Option<NodeIndex> {
        let ledger_tok = self.expect(TokenTag::Ledger)?;
        let name_tok = self.expect(TokenTag::Ident)?;
        self.expect(TokenTag::Colon)?;
        let type_node = self.parse_type()?;
        self.expect(TokenTag::Semi)?;
        let (extra_start, _) = self.ast.push_extra_slice(&[name_tok.0, type_node.0]);
        Some(self.ast.push_node(
            NodeTag::LedgerDecl,
            ledger_tok,
            NodeData::new(extra_start, flags),
        ))
    }

    fn parse_witness_decl(&mut self, flags: u32) -> Option<NodeIndex> {
        let witness_tok = self.expect(TokenTag::Witness)?;
        let name_tok = self.expect(TokenTag::Ident)?;
        let params = self.parse_param_list()?;
        self.expect(TokenTag::Colon)?;
        let ret_type = self.parse_type()?;
        self.expect(TokenTag::Semi)?;
        let (params_start, params_end) = self.ast.push_extra_slice(&params);
        let (extra_start, _) =
            self.ast
                .push_extra_slice(&[name_tok.0, params_start, params_end, ret_type.0]);
        Some(self.ast.push_node(
            NodeTag::WitnessDecl,
            witness_tok,
            NodeData::new(extra_start, flags),
        ))
    }

    fn parse_constructor_decl(&mut self) -> Option<NodeIndex> {
        let ctor_tok = self.expect(TokenTag::Constructor)?;
        let params = self.parse_param_list()?;
        let body = self.parse_block()?;
        let (params_start, params_end) = self.ast.push_extra_slice(&params);
        let (extra_start, _) = self.ast.push_extra_slice(&[params_start, params_end, body.0]);
        Some(self.ast.push_node(
            NodeTag::ConstructorDecl,
            ctor_tok,
            NodeData::new(extra_start, 0),
        ))
    }

    fn parse_circuit_decl(&mut self, flags: u32) -> Option<NodeIndex> {
        let circuit_tok = self.expect(TokenTag::Circuit)?;
        let name_tok = self.expect(TokenTag::Ident)?;
        let params = self.parse_param_list()?;
        self.expect(TokenTag::Colon)?;
        let ret_type = self.parse_type()?;
        let body = self.parse_block()?;

        let (params_start, params_end) = self.ast.push_extra_slice(&params);
        let (extra_start, _) = self.ast.push_extra_slice(&[
            name_tok.0,
            params_start,
            params_end,
            ret_type.0,
            body.0,
        ]);
        Some(self.ast.push_node(
            NodeTag::CircuitDecl,
            circuit_tok,
            NodeData::new(extra_start, flags),
        ))
    }

    fn parse_param_list(&mut self) -> Option<Vec<u32>> {
        self.expect(TokenTag::LParen)?;
        let mut params = Vec::new();
        while self.peek() != TokenTag::RParen && self.peek() != TokenTag::Eof {
            let param = self.parse_param()?;
            params.push(param.0);
            if self.peek() == TokenTag::Comma {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(TokenTag::RParen)?;
        Some(params)
    }

    fn parse_param(&mut self) -> Option<NodeIndex> {
        let name_tok = self.expect(TokenTag::Ident)?;
        self.expect(TokenTag::Colon)?;
        let type_node = self.parse_type()?;
        Some(self.ast.push_node(
            NodeTag::Param,
            name_tok,
            NodeData::new(type_node.0, 0),
        ))
    }

    fn parse_type(&mut self) -> Option<NodeIndex> {
        match self.peek() {
            TokenTag::Ident => {
                let name_tok = self.advance();
                if self.peek() == TokenTag::LAngle {
                    let args = self.parse_type_args()?;
                    let (start, end) = self.ast.push_extra_slice(&args);
                    Some(self.ast.push_node(
                        NodeTag::TypeGeneric,
                        name_tok,
                        NodeData::new(start, end),
                    ))
                } else {
                    Some(
                        self.ast
                            .push_node(NodeTag::TypeNamed, name_tok, NodeData::default()),
                    )
                }
            }
            TokenTag::LBracket => {
                let lbracket = self.advance();
                let mut elems = Vec::new();
                while self.peek() != TokenTag::RBracket && self.peek() != TokenTag::Eof {
                    let elem = self.parse_type()?;
                    elems.push(elem.0);
                    if self.peek() == TokenTag::Comma {
                        self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(TokenTag::RBracket)?;
                let (start, end) = self.ast.push_extra_slice(&elems);
                Some(
                    self.ast
                        .push_node(NodeTag::TypeTuple, lbracket, NodeData::new(start, end)),
                )
            }
            other => {
                let tok = self.current_tok();
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    self.ast.token_span(tok),
                    format!("expected type, found `{}`", other.as_str()),
                ));
                None
            }
        }
    }

    fn parse_type_args(&mut self) -> Option<Vec<u32>> {
        self.expect(TokenTag::LAngle)?;
        let mut args = Vec::new();
        while self.peek() != TokenTag::RAngle && self.peek() != TokenTag::Eof {
            let arg = if self.peek() == TokenTag::Nat {
                let nat_tok = self.advance();
                self.ast
                    .push_node(NodeTag::TypeNat, nat_tok, NodeData::default())
            } else if self.peek() == TokenTag::String {
                let str_tok = self.advance();
                self.ast
                    .push_node(NodeTag::TypeString, str_tok, NodeData::default())
            } else {
                self.parse_type()?
            };
            args.push(arg.0);
            if self.peek() == TokenTag::Comma {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(TokenTag::RAngle)?;
        Some(args)
    }

    fn parse_block(&mut self) -> Option<NodeIndex> {
        let lbrace = self.expect(TokenTag::LBrace)?;
        let mut stmts = Vec::new();
        while self.peek() != TokenTag::RBrace && self.peek() != TokenTag::Eof {
            if let Some(stmt) = self.parse_stmt() {
                stmts.push(stmt.0);
            } else {
                while !matches!(self.peek(), TokenTag::Semi | TokenTag::RBrace | TokenTag::Eof) {
                    self.advance();
                }
                if self.peek() == TokenTag::Semi {
                    self.advance();
                }
            }
        }
        self.expect(TokenTag::RBrace)?;
        let (start, end) = self.ast.push_extra_slice(&stmts);
        Some(
            self.ast
                .push_node(NodeTag::Block, lbrace, NodeData::new(start, end)),
        )
    }

    fn parse_stmt(&mut self) -> Option<NodeIndex> {
        match self.peek() {
            TokenTag::If => self.parse_if_stmt(),
            TokenTag::Return => {
                let ret_tok = self.advance();
                let expr = if self.peek() == TokenTag::Semi {
                    NodeIndex::NONE
                } else {
                    self.parse_expr()?
                };
                let semi = self.expect(TokenTag::Semi)?;
                Some(self.ast.push_node(
                    NodeTag::ReturnStmt,
                    ret_tok,
                    NodeData::new(expr.0, semi.0),
                ))
            }
            TokenTag::Const => {
                let const_tok = self.advance();
                let name_tok = self.expect(TokenTag::Ident)?;
                let ty = if self.peek() == TokenTag::Colon {
                    self.advance();
                    self.parse_type()?
                } else {
                    NodeIndex::NONE
                };
                self.expect(TokenTag::Eq)?;
                let init = self.parse_expr()?;
                let semi = self.expect(TokenTag::Semi)?;
                let (extra_start, _) = self.ast.push_extra_slice(&[name_tok.0, ty.0, init.0]);
                Some(self.ast.push_node(
                    NodeTag::ConstStmt,
                    const_tok,
                    NodeData::new(extra_start, semi.0),
                ))
            }
            _ => {
                let expr = self.parse_expr()?;
                if self.peek() == TokenTag::Eq {
                    let eq_tok = self.advance();
                    let rhs = self.parse_expr()?;
                    let semi = self.expect(TokenTag::Semi)?;
                    let (extra_start, _) = self.ast.push_extra_slice(&[expr.0, rhs.0]);
                    Some(self.ast.push_node(
                        NodeTag::AssignStmt,
                        eq_tok,
                        NodeData::new(extra_start, semi.0),
                    ))
                } else {
                    let semi = self.expect(TokenTag::Semi)?;
                    Some(self.ast.push_node(
                        NodeTag::ExprStmt,
                        self.ast.node_main_token(expr),
                        NodeData::new(expr.0, semi.0),
                    ))
                }
            }
        }
    }

    fn parse_if_stmt(&mut self) -> Option<NodeIndex> {
        let if_tok = self.expect(TokenTag::If)?;
        self.expect(TokenTag::LParen)?;
        let cond = self.parse_expr()?;
        self.expect(TokenTag::RParen)?;
        let then_branch = if self.peek() == TokenTag::LBrace {
            self.parse_block()?
        } else {
            self.parse_stmt()?
        };
        let else_branch = if self.peek() == TokenTag::Else {
            self.advance();
            if self.peek() == TokenTag::If {
                self.parse_if_stmt()?
            } else if self.peek() == TokenTag::LBrace {
                self.parse_block()?
            } else {
                self.parse_stmt()?
            }
        } else {
            NodeIndex::NONE
        };
        let (extra_start, _) =
            self.ast
                .push_extra_slice(&[cond.0, then_branch.0, else_branch.0]);
        Some(self.ast.push_node(
            NodeTag::IfStmt,
            if_tok,
            NodeData::new(extra_start, 0),
        ))
    }

    fn parse_expr(&mut self) -> Option<NodeIndex> {
        self.parse_ternary_expr()
    }

    fn parse_ternary_expr(&mut self) -> Option<NodeIndex> {
        let cond = self.parse_or_expr()?;
        if self.peek() == TokenTag::Question {
            let q_tok = self.advance();
            let then_branch = self.parse_expr()?;
            self.expect(TokenTag::Colon)?;
            let else_branch = self.parse_expr()?;
            let (extra_start, _) =
                self.ast
                    .push_extra_slice(&[cond.0, then_branch.0, else_branch.0]);
            Some(self.ast.push_node(
                NodeTag::TernaryExpr,
                q_tok,
                NodeData::new(extra_start, 0),
            ))
        } else {
            Some(cond)
        }
    }

    fn parse_or_expr(&mut self) -> Option<NodeIndex> {
        let mut lhs = self.parse_and_expr()?;
        while self.peek() == TokenTag::PipePipe {
            let op_tok = self.advance();
            let rhs = self.parse_and_expr()?;
            lhs = self.ast.push_node(
                NodeTag::BinaryExpr,
                op_tok,
                NodeData::new(lhs.0, rhs.0),
            );
        }
        Some(lhs)
    }

    fn parse_and_expr(&mut self) -> Option<NodeIndex> {
        let mut lhs = self.parse_equality_expr()?;
        while self.peek() == TokenTag::AmpAmp {
            let op_tok = self.advance();
            let rhs = self.parse_equality_expr()?;
            lhs = self.ast.push_node(
                NodeTag::BinaryExpr,
                op_tok,
                NodeData::new(lhs.0, rhs.0),
            );
        }
        Some(lhs)
    }

    fn parse_equality_expr(&mut self) -> Option<NodeIndex> {
        let mut lhs = self.parse_additive_expr()?;
        while matches!(self.peek(), TokenTag::EqEq | TokenTag::BangEq) {
            let op_tok = self.advance();
            let rhs = self.parse_additive_expr()?;
            lhs = self.ast.push_node(
                NodeTag::BinaryExpr,
                op_tok,
                NodeData::new(lhs.0, rhs.0),
            );
        }
        Some(lhs)
    }

    fn parse_additive_expr(&mut self) -> Option<NodeIndex> {
        let mut lhs = self.parse_cast_expr()?;
        while matches!(self.peek(), TokenTag::Plus | TokenTag::Minus) {
            let op_tok = self.advance();
            let rhs = self.parse_cast_expr()?;
            lhs = self.ast.push_node(
                NodeTag::BinaryExpr,
                op_tok,
                NodeData::new(lhs.0, rhs.0),
            );
        }
        Some(lhs)
    }

    fn parse_cast_expr(&mut self) -> Option<NodeIndex> {
        let mut expr = self.parse_unary_expr()?;
        while self.peek() == TokenTag::As {
            let as_tok = self.advance();
            let ty = self.parse_type()?;
            expr = self
                .ast
                .push_node(NodeTag::CastExpr, as_tok, NodeData::new(expr.0, ty.0));
        }
        Some(expr)
    }

    fn parse_unary_expr(&mut self) -> Option<NodeIndex> {
        if matches!(self.peek(), TokenTag::Bang | TokenTag::Minus) {
            let op_tok = self.advance();
            let operand = self.parse_unary_expr()?;
            return Some(self.ast.push_node(
                NodeTag::UnaryExpr,
                op_tok,
                NodeData::new(operand.0, 0),
            ));
        }
        self.parse_postfix_expr()
    }

    fn parse_postfix_expr(&mut self) -> Option<NodeIndex> {
        let mut expr = self.parse_primary_expr()?;
        loop {
            match self.peek() {
                TokenTag::Dot => {
                    let dot_tok = self.advance();
                    let field_tok = self.expect(TokenTag::Ident)?;
                    expr = self.ast.push_node(
                        NodeTag::MemberExpr,
                        dot_tok,
                        NodeData::new(expr.0, field_tok.0),
                    );
                }
                TokenTag::LAngle => {
                    // Speculatively parse generic call `<type_args>(args)` or generic struct literal `<type_args>{ fields }`.
                    let saved_cursor = self.cursor;
                    let saved_diags = self.diagnostics.diagnostics.len();
                    let saved_extra = self.ast.extra_data.len();
                    if let Some(targs) = self.parse_type_args()
                        && self.peek() == TokenTag::LParen
                    {
                        let lparen = self.advance();
                        let mut args = Vec::new();
                        while self.peek() != TokenTag::RParen && self.peek() != TokenTag::Eof {
                            let arg = self.parse_expr()?;
                            args.push(arg.0);
                            if self.peek() == TokenTag::Comma {
                                self.advance();
                            } else {
                                break;
                            }
                        }
                        let rparen = self.expect(TokenTag::RParen)?;
                        let (targs_start, targs_end) = self.ast.push_extra_slice(&targs);
                        let (args_start, args_end) = self.ast.push_extra_slice(&args);
                        let (extra_start, _) = self.ast.push_extra_slice(&[
                            expr.0,
                            targs_start,
                            targs_end,
                            args_start,
                            args_end,
                        ]);
                        expr = self.ast.push_node(
                            NodeTag::GenericCallExpr,
                            lparen,
                            NodeData::new(extra_start, rparen.0),
                        );
                    } else if self.diagnostics.diagnostics.len() == saved_diags
                        && self.peek() == TokenTag::LBrace
                        && self.ast.node_tag(expr) == NodeTag::IdentExpr
                    {
                        // Re-parse type_args? Wait: we already parsed targs if we refactor cleanly below!
                        self.cursor = saved_cursor;
                        self.diagnostics.diagnostics.truncate(saved_diags);
                        self.ast.extra_data.truncate(saved_extra);
                        let targs = self.parse_type_args()?;
                        let (targs_start, targs_end) = self.ast.push_extra_slice(&targs);
                        let type_node = self.ast.push_node(
                            NodeTag::TypeGeneric,
                            self.ast.node_main_token(expr),
                            NodeData::new(targs_start, targs_end),
                        );
                        expr = self.parse_struct_lit_body(type_node)?;
                    } else {
                        self.cursor = saved_cursor;
                        self.diagnostics.diagnostics.truncate(saved_diags);
                        self.ast.extra_data.truncate(saved_extra);
                        break;
                    }
                }
                TokenTag::LBrace if self.ast.node_tag(expr) == NodeTag::IdentExpr => {
                    let type_node = self.ast.push_node(
                        NodeTag::TypeNamed,
                        self.ast.node_main_token(expr),
                        NodeData::default(),
                    );
                    expr = self.parse_struct_lit_body(type_node)?;
                }
                TokenTag::LParen => {
                    let lparen = self.advance();
                    let mut args = Vec::new();
                    while self.peek() != TokenTag::RParen && self.peek() != TokenTag::Eof {
                        let arg = self.parse_expr()?;
                        args.push(arg.0);
                        if self.peek() == TokenTag::Comma {
                            self.advance();
                        } else {
                            break;
                        }
                    }
                    let rparen = self.expect(TokenTag::RParen)?;
                    let (args_start, args_end) = self.ast.push_extra_slice(&args);
                    let (extra_start, _) =
                        self.ast.push_extra_slice(&[expr.0, args_start, args_end]);
                    expr = self.ast.push_node(
                        NodeTag::CallExpr,
                        lparen,
                        NodeData::new(extra_start, rparen.0),
                    );
                }
                _ => break,
            }
        }
        Some(expr)
    }

    fn parse_struct_lit_body(&mut self, type_node: NodeIndex) -> Option<NodeIndex> {
        let lbrace = self.expect(TokenTag::LBrace)?;
        let mut fields = Vec::new();
        while self.peek() != TokenTag::RBrace && self.peek() != TokenTag::Eof {
            let fname = self.expect(TokenTag::Ident)?;
            self.expect(TokenTag::Colon)?;
            let val = self.parse_expr()?;
            let fnode = self
                .ast
                .push_node(NodeTag::StructLitField, fname, NodeData::new(val.0, 0));
            fields.push(fnode.0);
            if self.peek() == TokenTag::Comma {
                self.advance();
            } else {
                break;
            }
        }
        let rbrace = self.expect(TokenTag::RBrace)?;
        let (fstart, fend) = self.ast.push_extra_slice(&fields);
        let (extra_start, _) = self.ast.push_extra_slice(&[type_node.0, fstart, fend]);
        Some(self.ast.push_node(
            NodeTag::StructLitExpr,
            lbrace,
            NodeData::new(extra_start, rbrace.0),
        ))
    }

    fn parse_primary_expr(&mut self) -> Option<NodeIndex> {
        match self.peek() {
            TokenTag::Ident => {
                let tok = self.advance();
                Some(
                    self.ast
                        .push_node(NodeTag::IdentExpr, tok, NodeData::default()),
                )
            }
            TokenTag::Nat => {
                let tok = self.advance();
                Some(
                    self.ast
                        .push_node(NodeTag::IntLitExpr, tok, NodeData::default()),
                )
            }
            TokenTag::True | TokenTag::False => {
                let tok = self.advance();
                Some(
                    self.ast
                        .push_node(NodeTag::BoolLitExpr, tok, NodeData::default()),
                )
            }
            TokenTag::String => {
                let tok = self.advance();
                Some(
                    self.ast
                        .push_node(NodeTag::StringLitExpr, tok, NodeData::default()),
                )
            }
            TokenTag::Default => {
                let def_tok = self.advance();
                self.expect(TokenTag::LAngle)?;
                let ty = self.parse_type()?;
                let rangle = self.expect(TokenTag::RAngle)?;
                Some(self.ast.push_node(
                    NodeTag::DefaultExpr,
                    def_tok,
                    NodeData::new(ty.0, rangle.0),
                ))
            }
            TokenTag::Assert => {
                let assert_tok = self.advance();
                self.expect(TokenTag::LParen)?;
                let cond = self.parse_expr()?;
                self.expect(TokenTag::Comma)?;
                let msg = self.parse_expr()?;
                let rparen = self.expect(TokenTag::RParen)?;
                let (extra_start, _) = self.ast.push_extra_slice(&[cond.0, msg.0]);
                Some(self.ast.push_node(
                    NodeTag::AssertExpr,
                    assert_tok,
                    NodeData::new(extra_start, rparen.0),
                ))
            }
            TokenTag::Disclose => {
                let disclose_tok = self.advance();
                self.expect(TokenTag::LParen)?;
                let inner = self.parse_expr()?;
                let rparen = self.expect(TokenTag::RParen)?;
                Some(self.ast.push_node(
                    NodeTag::DiscloseExpr,
                    disclose_tok,
                    NodeData::new(inner.0, rparen.0),
                ))
            }
            TokenTag::LBracket => {
                let lbracket = self.advance();
                let mut elems = Vec::new();
                while self.peek() != TokenTag::RBracket && self.peek() != TokenTag::Eof {
                    let elem = self.parse_expr()?;
                    elems.push(elem.0);
                    if self.peek() == TokenTag::Comma {
                        self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(TokenTag::RBracket)?;
                let (start, end) = self.ast.push_extra_slice(&elems);
                Some(
                    self.ast
                        .push_node(NodeTag::TupleExpr, lbracket, NodeData::new(start, end)),
                )
            }
            TokenTag::LParen => {
                self.advance();
                let inner = self.parse_expr()?;
                self.expect(TokenTag::RParen)?;
                Some(inner)
            }
            other => {
                let tok = self.current_tok();
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    self.ast.token_span(tok),
                    format!("expected expression, found `{}`", other.as_str()),
                ));
                None
            }
        }
    }
}
