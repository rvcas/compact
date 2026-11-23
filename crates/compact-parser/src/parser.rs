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
                format!(
                    "expected `{}`, found `{}`",
                    expected.as_str(),
                    found.as_str()
                ),
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
            TokenTag::Pragma => self.parse_pragma_decl(),
            TokenTag::Include => self.parse_include_decl(),
            TokenTag::Import => self.parse_import_decl(),
            TokenTag::Export if self.peek_at(1) == TokenTag::LBrace => self.parse_export_list(),
            TokenTag::Constructor => self.parse_constructor_decl(),
            TokenTag::Export
            | TokenTag::Module
            | TokenTag::New
            | TokenTag::Type
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

    fn parse_pragma_decl(&mut self) -> Option<NodeIndex> {
        let pragma_tok = self.expect(TokenTag::Pragma)?;
        let name_tok = self.expect(TokenTag::Ident)?;
        let expr = self.parse_version_or()?;
        let semi_tok = self.expect(TokenTag::Semi)?;
        let (extra_start, _) = self.ast.push_extra_slice(&[name_tok.0, expr.0]);
        Some(self.ast.push_node(
            NodeTag::PragmaDecl,
            pragma_tok,
            NodeData::new(extra_start, semi_tok.0),
        ))
    }

    fn parse_version_or(&mut self) -> Option<NodeIndex> {
        let mut lhs = self.parse_version_and()?;
        while self.peek() == TokenTag::PipePipe {
            let op_tok = self.advance();
            let rhs = self.parse_version_and()?;
            lhs = self
                .ast
                .push_node(NodeTag::VersionBinary, op_tok, NodeData::new(lhs.0, rhs.0));
        }
        Some(lhs)
    }

    fn parse_version_and(&mut self) -> Option<NodeIndex> {
        let mut lhs = self.parse_version_term()?;
        while self.peek() == TokenTag::AmpAmp {
            let op_tok = self.advance();
            let rhs = self.parse_version_term()?;
            lhs = self
                .ast
                .push_node(NodeTag::VersionBinary, op_tok, NodeData::new(lhs.0, rhs.0));
        }
        Some(lhs)
    }

    fn parse_version_term(&mut self) -> Option<NodeIndex> {
        match self.peek() {
            TokenTag::LParen => {
                self.advance();
                let inner = self.parse_version_or()?;
                self.expect(TokenTag::RParen)?;
                Some(inner)
            }
            TokenTag::Bang
            | TokenTag::LAngle
            | TokenTag::LtEq
            | TokenTag::RAngle
            | TokenTag::GtEq => {
                let op_tok = self.advance();
                let atom = self.parse_version_atom()?;
                Some(
                    self.ast
                        .push_node(NodeTag::VersionUnary, op_tok, NodeData::new(atom.0, 0)),
                )
            }
            _ => self.parse_version_atom(),
        }
    }

    fn parse_version_atom(&mut self) -> Option<NodeIndex> {
        let first_nat = self.expect(TokenTag::Nat)?;
        let mut last_nat = first_nat;
        while self.peek() == TokenTag::Dot && self.peek_at(1) == TokenTag::Nat {
            self.advance(); // '.'
            last_nat = self.advance(); // nat
        }
        Some(self.ast.push_node(
            NodeTag::VersionAtom,
            first_nat,
            NodeData::new(last_nat.0, 0),
        ))
    }

    fn parse_include_decl(&mut self) -> Option<NodeIndex> {
        let include_tok = self.expect(TokenTag::Include)?;
        let path_tok = self.expect(TokenTag::String)?;
        let semi_tok = self.expect(TokenTag::Semi)?;
        Some(self.ast.push_node(
            NodeTag::IncludeDecl,
            include_tok,
            NodeData::new(path_tok.0, semi_tok.0),
        ))
    }

    fn parse_opt_generic_params(&mut self) -> Option<(u32, u32)> {
        if self.peek() != TokenTag::LAngle {
            return Some((0, 0));
        }
        self.advance(); // '<'
        let mut params = Vec::new();
        while self.peek() != TokenTag::RAngle && self.peek() != TokenTag::Eof {
            let (is_nat, hash_tok) = if self.peek() == TokenTag::Hash {
                (1u32, self.advance())
            } else {
                (0u32, TokenIndex::NONE)
            };
            let name_tok = self.expect(TokenTag::Ident)?;
            let node = self.ast.push_node(
                NodeTag::GenericParam,
                name_tok,
                NodeData::new(is_nat, hash_tok.0),
            );
            params.push(node.0);
            if self.peek() == TokenTag::Comma {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(TokenTag::RAngle)?;
        Some(self.ast.push_extra_slice(&params))
    }

    fn parse_import_decl(&mut self) -> Option<NodeIndex> {
        let import_tok = self.expect(TokenTag::Import)?;
        let mut items = Vec::new();
        if self.peek() == TokenTag::LBrace {
            self.advance(); // '{'
            while self.peek() != TokenTag::RBrace && self.peek() != TokenTag::Eof {
                let name_tok = self.expect(TokenTag::Ident)?;
                let alias_tok = if self.peek() == TokenTag::As {
                    self.advance();
                    self.expect(TokenTag::Ident)?
                } else {
                    TokenIndex::NONE
                };
                let item = self.ast.push_node(
                    NodeTag::ImportItem,
                    name_tok,
                    NodeData::new(alias_tok.0, 0),
                );
                items.push(item.0);
                if self.peek() == TokenTag::Comma {
                    self.advance();
                } else {
                    break;
                }
            }
            self.expect(TokenTag::RBrace)?;
            self.expect(TokenTag::From)?;
        }
        let name_tok = if matches!(self.peek(), TokenTag::Ident | TokenTag::String) {
            self.advance()
        } else {
            let tok = self.current_tok();
            self.diagnostics.push(CompactDiagnostic::error(
                self.file,
                self.ast.token_span(tok),
                format!(
                    "expected module name or file path in `import`, found `{}`",
                    self.ast.token_tag(tok).as_str()
                ),
            ));
            return None;
        };
        let (gargs_start, gargs_end) = if self.peek() == TokenTag::LAngle {
            let gargs = self.parse_type_args()?;
            self.ast.push_extra_slice(&gargs)
        } else {
            (0, 0)
        };
        let prefix_tok = if self.peek() == TokenTag::Prefix {
            self.advance();
            self.expect(TokenTag::Ident)?
        } else {
            TokenIndex::NONE
        };
        let semi_tok = self.expect(TokenTag::Semi)?;
        let (items_start, items_end) = self.ast.push_extra_slice(&items);
        let (extra_start, _) = self.ast.push_extra_slice(&[
            name_tok.0,
            gargs_start,
            gargs_end,
            prefix_tok.0,
            items_start,
            items_end,
        ]);
        Some(self.ast.push_node(
            NodeTag::ImportDecl,
            import_tok,
            NodeData::new(extra_start, semi_tok.0),
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
        if self.peek() == TokenTag::New {
            self.advance();
            flags |= decl_flags::NEW_TYPE;
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
            TokenTag::Module => self.parse_module_decl(flags),
            TokenTag::Type => self.parse_type_decl(flags),
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
                        "expected declaration after modifiers, found `{}`",
                        other.as_str()
                    ),
                ));
                None
            }
        }
    }

    fn parse_module_decl(&mut self, flags: u32) -> Option<NodeIndex> {
        let module_tok = self.expect(TokenTag::Module)?;
        let name_tok = self.expect(TokenTag::Ident)?;
        let (gp_start, gp_end) = self.parse_opt_generic_params()?;
        self.expect(TokenTag::LBrace)?;
        let mut decls = Vec::new();
        while self.peek() != TokenTag::RBrace && self.peek() != TokenTag::Eof {
            if let Some(decl) = self.parse_program_element() {
                decls.push(decl.0);
            } else {
                self.advance();
            }
        }
        let rbrace_tok = self.expect(TokenTag::RBrace)?;
        let (decls_start, decls_end) = self.ast.push_extra_slice(&decls);
        let (extra_start, _) = self.ast.push_extra_slice(&[
            name_tok.0,
            gp_start,
            gp_end,
            decls_start,
            decls_end,
            rbrace_tok.0,
        ]);
        Some(self.ast.push_node(
            NodeTag::ModuleDecl,
            module_tok,
            NodeData::new(extra_start, flags),
        ))
    }

    fn parse_type_decl(&mut self, flags: u32) -> Option<NodeIndex> {
        let type_tok = self.expect(TokenTag::Type)?;
        let name_tok = self.expect(TokenTag::Ident)?;
        let (gp_start, gp_end) = self.parse_opt_generic_params()?;
        self.expect(TokenTag::Eq)?;
        let target_type = self.parse_type()?;
        let semi_tok = self.expect(TokenTag::Semi)?;
        let (extra_start, _) =
            self.ast
                .push_extra_slice(&[name_tok.0, gp_start, gp_end, target_type.0, semi_tok.0]);
        Some(self.ast.push_node(
            NodeTag::TypeDecl,
            type_tok,
            NodeData::new(extra_start, flags),
        ))
    }

    fn parse_struct_decl(&mut self, flags: u32) -> Option<NodeIndex> {
        let struct_tok = self.expect(TokenTag::Struct)?;
        let name_tok = self.expect(TokenTag::Ident)?;
        let (gp_start, gp_end) = self.parse_opt_generic_params()?;
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
        let (extra_start, _) = self
            .ast
            .push_extra_slice(&[name_tok.0, gp_start, gp_end, fstart, fend]);
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
        let (gp_start, gp_end) = self.parse_opt_generic_params()?;
        let params = self.parse_param_list()?;
        self.expect(TokenTag::Colon)?;
        let ret_type = self.parse_type()?;
        self.expect(TokenTag::Semi)?;
        let (params_start, params_end) = self.ast.push_extra_slice(&params);
        let (extra_start, _) = self.ast.push_extra_slice(&[
            name_tok.0,
            gp_start,
            gp_end,
            params_start,
            params_end,
            ret_type.0,
        ]);
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
        let (extra_start, _) = self
            .ast
            .push_extra_slice(&[params_start, params_end, body.0]);
        Some(self.ast.push_node(
            NodeTag::ConstructorDecl,
            ctor_tok,
            NodeData::new(extra_start, 0),
        ))
    }

    fn parse_circuit_decl(&mut self, flags: u32) -> Option<NodeIndex> {
        let circuit_tok = self.expect(TokenTag::Circuit)?;
        let name_tok = self.expect(TokenTag::Ident)?;
        let (gp_start, gp_end) = self.parse_opt_generic_params()?;
        let params = self.parse_param_list()?;
        self.expect(TokenTag::Colon)?;
        let ret_type = self.parse_type()?;
        let body = self.parse_block()?;

        let (params_start, params_end) = self.ast.push_extra_slice(&params);
        let (extra_start, _) = self.ast.push_extra_slice(&[
            name_tok.0,
            gp_start,
            gp_end,
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
        Some(
            self.ast
                .push_node(NodeTag::Param, name_tok, NodeData::new(type_node.0, 0)),
        )
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
                while !matches!(
                    self.peek(),
                    TokenTag::Semi | TokenTag::RBrace | TokenTag::Eof
                ) {
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
            TokenTag::For => self.parse_for_stmt(),
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
        let (extra_start, _) = self
            .ast
            .push_extra_slice(&[cond.0, then_branch.0, else_branch.0]);
        Some(
            self.ast
                .push_node(NodeTag::IfStmt, if_tok, NodeData::new(extra_start, 0)),
        )
    }

    fn parse_for_stmt(&mut self) -> Option<NodeIndex> {
        let for_tok = self.expect(TokenTag::For)?;
        self.expect(TokenTag::LParen)?;
        self.expect(TokenTag::Const)?;
        let name_tok = self.expect(TokenTag::Ident)?;
        // Contextual `of` keyword
        if self.peek() == TokenTag::Ident
            && self.ast.token_text(self.current_tok(), self.file.text()) == "of"
        {
            self.advance();
        } else {
            let tok = self.current_tok();
            self.diagnostics.push(CompactDiagnostic::error(
                self.file,
                self.ast.token_span(tok),
                format!(
                    "expected `of` in `for` loop, found `{}`",
                    self.ast.token_tag(tok).as_str()
                ),
            ));
            return None;
        }
        let first_expr = self.parse_expr()?;
        if self.peek() == TokenTag::DotDot {
            self.advance();
            let end_expr = self.parse_expr()?;
            self.expect(TokenTag::RParen)?;
            let body = if self.peek() == TokenTag::LBrace {
                self.parse_block()?
            } else {
                self.parse_stmt()?
            };
            let (extra_start, _) =
                self.ast
                    .push_extra_slice(&[name_tok.0, first_expr.0, end_expr.0, body.0]);
            Some(self.ast.push_node(
                NodeTag::ForRangeStmt,
                for_tok,
                NodeData::new(extra_start, 0),
            ))
        } else {
            self.expect(TokenTag::RParen)?;
            let body = if self.peek() == TokenTag::LBrace {
                self.parse_block()?
            } else {
                self.parse_stmt()?
            };
            let (extra_start, _) = self
                .ast
                .push_extra_slice(&[name_tok.0, first_expr.0, body.0]);
            Some(
                self.ast
                    .push_node(NodeTag::ForEachStmt, for_tok, NodeData::new(extra_start, 0)),
            )
        }
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
            Some(
                self.ast
                    .push_node(NodeTag::TernaryExpr, q_tok, NodeData::new(extra_start, 0)),
            )
        } else {
            Some(cond)
        }
    }

    fn parse_or_expr(&mut self) -> Option<NodeIndex> {
        let mut lhs = self.parse_and_expr()?;
        while self.peek() == TokenTag::PipePipe {
            let op_tok = self.advance();
            let rhs = self.parse_and_expr()?;
            lhs = self
                .ast
                .push_node(NodeTag::BinaryExpr, op_tok, NodeData::new(lhs.0, rhs.0));
        }
        Some(lhs)
    }

    fn parse_and_expr(&mut self) -> Option<NodeIndex> {
        let mut lhs = self.parse_equality_expr()?;
        while self.peek() == TokenTag::AmpAmp {
            let op_tok = self.advance();
            let rhs = self.parse_equality_expr()?;
            lhs = self
                .ast
                .push_node(NodeTag::BinaryExpr, op_tok, NodeData::new(lhs.0, rhs.0));
        }
        Some(lhs)
    }

    fn parse_equality_expr(&mut self) -> Option<NodeIndex> {
        let mut lhs = self.parse_relational_expr()?;
        while matches!(self.peek(), TokenTag::EqEq | TokenTag::BangEq) {
            let op_tok = self.advance();
            let rhs = self.parse_relational_expr()?;
            lhs = self
                .ast
                .push_node(NodeTag::BinaryExpr, op_tok, NodeData::new(lhs.0, rhs.0));
        }
        Some(lhs)
    }

    fn parse_relational_expr(&mut self) -> Option<NodeIndex> {
        let mut lhs = self.parse_additive_expr()?;
        while matches!(
            self.peek(),
            TokenTag::LAngle | TokenTag::RAngle | TokenTag::LtEq | TokenTag::GtEq
        ) {
            let op_tok = self.advance();
            let rhs = self.parse_additive_expr()?;
            lhs = self
                .ast
                .push_node(NodeTag::BinaryExpr, op_tok, NodeData::new(lhs.0, rhs.0));
        }
        Some(lhs)
    }

    fn parse_additive_expr(&mut self) -> Option<NodeIndex> {
        let mut lhs = self.parse_multiplicative_expr()?;
        while matches!(self.peek(), TokenTag::Plus | TokenTag::Minus) {
            let op_tok = self.advance();
            let rhs = self.parse_multiplicative_expr()?;
            lhs = self
                .ast
                .push_node(NodeTag::BinaryExpr, op_tok, NodeData::new(lhs.0, rhs.0));
        }
        Some(lhs)
    }

    fn parse_multiplicative_expr(&mut self) -> Option<NodeIndex> {
        let mut lhs = self.parse_cast_expr()?;
        while self.peek() == TokenTag::Star {
            let op_tok = self.advance();
            let rhs = self.parse_cast_expr()?;
            lhs = self
                .ast
                .push_node(NodeTag::BinaryExpr, op_tok, NodeData::new(lhs.0, rhs.0));
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
                TokenTag::LBracket => {
                    let lbracket = self.advance();
                    let index = self.parse_expr()?;
                    let rbracket = self.expect(TokenTag::RBracket)?;
                    let (extra_start, _) = self.ast.push_extra_slice(&[expr.0, index.0]);
                    expr = self.ast.push_node(
                        NodeTag::IndexExpr,
                        lbracket,
                        NodeData::new(extra_start, rbracket.0),
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
