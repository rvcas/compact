mod doc;

use compact_ast::{Ast, CommentKind, NodeIndex, NodeTag, TokenIndex, TokenTag};
use doc::{Doc, render};

pub struct FormatOptions {
    pub line_length: usize,
}

impl Default for FormatOptions {
    fn default() -> Self {
        Self { line_length: 100 }
    }
}

/// Format a parsed Compact AST back into canonical source code, preserving comments and
/// respecting `options.line_length`.
pub fn format_ast(ast: &Ast, source: &str, options: &FormatOptions) -> String {
    let mut fmt = Formatter {
        ast,
        source,
        next_comment: 0,
    };
    let root_doc = fmt.build_root();
    render(&root_doc, options.line_length)
}

struct Formatter<'a> {
    ast: &'a Ast,
    source: &'a str,
    next_comment: usize,
}

impl<'a> Formatter<'a> {
    /// Returns true if `source[from..to]` contains at least two newlines (i.e. a blank line).
    fn has_blank_line(&self, from: u32, to: u32) -> bool {
        let start = from as usize;
        let end = (to as usize).min(self.source.len());
        if start >= end {
            return false;
        }
        self.source[start..end]
            .bytes()
            .filter(|&b| b == b'\n')
            .count()
            >= 2
    }

    fn has_newline(&self, from: u32, to: u32) -> bool {
        let start = from as usize;
        let end = (to as usize).min(self.source.len());
        if start >= end {
            return false;
        }
        self.source[start..end].contains('\n')
    }

    /// Find the matching closing delimiter token (`}`, `)`, `]`) starting at `open_tok`.
    fn matching_close_token(
        &self,
        open_tok: TokenIndex,
        open_tag: TokenTag,
        close_tag: TokenTag,
    ) -> TokenIndex {
        let tags = self.ast.tokens.tag();
        let mut depth = 0u32;
        let mut idx = open_tok.0 as usize;
        while idx < tags.len() {
            let t = tags[idx];
            if t == open_tag {
                depth += 1;
            } else if t == close_tag {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return TokenIndex(idx as u32);
                }
            }
            idx += 1;
        }
        TokenIndex(tags.len().saturating_sub(1) as u32)
    }

    /// Find the first token with tag `target` at or after `start_tok`.
    fn find_token_after(&self, start_tok: TokenIndex, target: TokenTag) -> Option<TokenIndex> {
        let tags = self.ast.tokens.tag();
        let mut idx = start_tok.0 as usize;
        while idx < tags.len() {
            if tags[idx] == target {
                return Some(TokenIndex(idx as u32));
            }
            idx += 1;
        }
        None
    }

    /// End byte offset of a declaration or statement (including trailing `;` or closing `}`).
    fn node_full_end(&self, node: NodeIndex) -> u32 {
        match self.ast.node_tag(node) {
            NodeTag::Block => {
                let open = self.ast.node_main_token(node);
                let close = self.matching_close_token(open, TokenTag::LBrace, TokenTag::RBrace);
                self.ast.token_span(close).end
            }
            NodeTag::CircuitDecl => {
                let d = self.ast.circuit_decl(node);
                self.node_full_end(d.body)
            }
            NodeTag::ConstructorDecl => {
                let d = self.ast.constructor_decl(node);
                self.node_full_end(d.body)
            }
            NodeTag::IfStmt => {
                let s = self.ast.if_stmt(node);
                self.node_full_end(s.else_branch.unwrap_or(s.then_branch))
            }
            NodeTag::ForRangeStmt => {
                let s = self.ast.for_range_stmt(node);
                self.node_full_end(s.body)
            }
            NodeTag::ForEachStmt => {
                let s = self.ast.for_each_stmt(node);
                self.node_full_end(s.body)
            }
            NodeTag::StructDecl | NodeTag::EnumDecl | NodeTag::ContractDecl => {
                let main = self.ast.node_main_token(node);
                if let Some(open) = self.find_token_after(main, TokenTag::LBrace) {
                    let close = self.matching_close_token(open, TokenTag::LBrace, TokenTag::RBrace);
                    self.ast.token_span(close).end
                } else {
                    self.ast.node_span(node).end
                }
            }
            NodeTag::ExportListDecl
            | NodeTag::WitnessDecl
            | NodeTag::LedgerDecl
            | NodeTag::ContractImplementsDecl
            | NodeTag::ReturnStmt
            | NodeTag::ExprStmt => {
                let span_end = self.ast.node_span(node).end;
                let spans = self.ast.tokens.span();
                let tags = self.ast.tokens.tag();
                // Check if the immediately following token is `;`.
                for i in 0..spans.len() {
                    if spans[i].start >= span_end {
                        if tags[i] == TokenTag::Semi {
                            return spans[i].end;
                        }
                        break;
                    }
                }
                span_end
            }
            _ => self.ast.node_span(node).end,
        }
    }

    /// Emit all leading comments occurring before `tok`, preserving blank lines between comments
    /// and between the last comment and `tok`.
    fn take_leading_comments(&mut self, tok: TokenIndex) -> Vec<Doc> {
        let before_tokens = self.ast.comments.before_token();
        let spans = self.ast.comments.span();
        let kinds = self.ast.comments.kind();
        let mut docs = Vec::new();
        let mut prev_end: Option<u32> = None;

        while self.next_comment < before_tokens.len() && before_tokens[self.next_comment] <= tok {
            let span = spans[self.next_comment];
            let kind = kinds[self.next_comment];
            let text = span.slice(self.source).trim_end().to_owned();
            if let Some(pe) = prev_end {
                if self.has_blank_line(pe, span.start) {
                    docs.push(Doc::BlankLine);
                } else {
                    docs.push(Doc::HardLine);
                }
            }
            match kind {
                CommentKind::Line => docs.push(Doc::LineComment(text)),
                CommentKind::Block => docs.push(Doc::Text(text)),
            }
            prev_end = Some(span.end);
            self.next_comment += 1;
        }

        if let Some(pe) = prev_end {
            let tok_start = self.ast.token_span(tok).start;
            if self.has_blank_line(pe, tok_start) {
                docs.push(Doc::BlankLine);
            } else {
                docs.push(Doc::HardLine);
            }
        }
        docs
    }

    /// Emit any comments before `byte_limit` (used for comments inside braces before `}` or
    /// before an item inside a wrapped list).
    fn take_comments_before_byte(&mut self, byte_limit: u32, trailing_break: bool) -> Vec<Doc> {
        let spans = self.ast.comments.span();
        let kinds = self.ast.comments.kind();
        let mut docs = Vec::new();
        let mut prev_end: Option<u32> = None;

        while self.next_comment < spans.len() && spans[self.next_comment].start < byte_limit {
            let span = spans[self.next_comment];
            let kind = kinds[self.next_comment];
            let text = span.slice(self.source).trim_end().to_owned();
            if let Some(pe) = prev_end {
                if self.has_blank_line(pe, span.start) {
                    docs.push(Doc::BlankLine);
                } else {
                    docs.push(Doc::HardLine);
                }
            }
            match kind {
                CommentKind::Line => docs.push(Doc::LineComment(text)),
                CommentKind::Block => docs.push(Doc::Text(text)),
            }
            prev_end = Some(span.end);
            self.next_comment += 1;
        }

        if let Some(pe) = prev_end
            && trailing_break
        {
            if self.has_blank_line(pe, byte_limit) {
                docs.push(Doc::BlankLine);
            } else {
                docs.push(Doc::HardLine);
            }
        }
        docs
    }

    /// Consume trailing same-line comments attached immediately after `end_byte` (no newline
    /// between `end_byte` and the comment, and if it is a block comment, followed by a newline).
    fn take_trailing_comment(&mut self, end_byte: u32) -> Doc {
        let spans = self.ast.comments.span();
        let kinds = self.ast.comments.kind();
        let before_tokens = self.ast.comments.before_token();
        if self.next_comment >= spans.len() {
            return Doc::Nil;
        }
        let span = spans[self.next_comment];
        if span.start < end_byte || self.has_newline(end_byte, span.start) {
            return Doc::Nil;
        }
        let kind = kinds[self.next_comment];
        let next_tok = before_tokens[self.next_comment];
        let is_trailing = match kind {
            CommentKind::Line => true,
            CommentKind::Block => {
                let next_start = if (next_tok.0 as usize) < self.ast.tokens.len() {
                    self.ast.token_span(next_tok).start
                } else {
                    self.source.len() as u32
                };
                next_start >= self.source.len() as u32 || self.has_newline(span.end, next_start)
            }
        };
        if !is_trailing {
            return Doc::Nil;
        }
        self.next_comment += 1;
        let text = span.slice(self.source).trim_end().to_owned();
        match kind {
            CommentKind::Line => Doc::concat(vec![Doc::text(" "), Doc::LineComment(text)]),
            CommentKind::Block => Doc::concat(vec![Doc::text(" "), Doc::Text(text)]),
        }
    }

    fn take_eof_comments(&mut self, last_end: Option<u32>) -> Vec<Doc> {
        let spans = self.ast.comments.span();
        let kinds = self.ast.comments.kind();
        let mut docs = Vec::new();
        let mut prev_end = last_end;

        while self.next_comment < spans.len() {
            let span = spans[self.next_comment];
            let kind = kinds[self.next_comment];
            let text = span.slice(self.source).trim_end().to_owned();
            if let Some(pe) = prev_end {
                if self.has_blank_line(pe, span.start) {
                    docs.push(Doc::BlankLine);
                } else {
                    docs.push(Doc::HardLine);
                }
            }
            match kind {
                CommentKind::Line => docs.push(Doc::LineComment(text)),
                CommentKind::Block => docs.push(Doc::Text(text)),
            }
            prev_end = Some(span.end);
            self.next_comment += 1;
        }
        docs
    }

    fn build_root(&mut self) -> Doc {
        let decls: Vec<_> = self.ast.root_decls().collect();
        let mut parts = Vec::new();
        let mut last_end: Option<u32> = None;

        for (i, decl) in decls.into_iter().enumerate() {
            if i > 0 {
                parts.push(Doc::BlankLine);
            }
            let first_tok = self.decl_first_token(decl);
            parts.extend(self.take_leading_comments(first_tok));
            parts.push(self.build_decl(decl));
            let end_byte = self.node_full_end(decl);
            parts.push(self.take_trailing_comment(end_byte));
            last_end = Some(end_byte);
        }

        let eof = self.take_eof_comments(last_end);
        parts.extend(eof);
        Doc::concat(parts)
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
            NodeTag::ContractDecl => {
                let d = self.ast.contract_decl(node);
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

    fn build_generic_params(&self, start: u32, end: u32) -> Doc {
        if start == end {
            return Doc::Nil;
        }
        let items: Vec<Doc> = self
            .ast
            .extra_nodes(start, end)
            .map(|gp_node| {
                let gp = self.ast.generic_param(gp_node);
                let name = self.ast.token_text(gp.name_token, self.source);
                if gp.is_nat {
                    Doc::text(format!("#{name}"))
                } else {
                    Doc::text(name)
                }
            })
            .collect();
        Doc::delimited_list("<", items, ">", "")
    }

    fn build_version_expr(&self, node: NodeIndex) -> Doc {
        let data = self.ast.node_data(node);
        match self.ast.node_tag(node) {
            NodeTag::VersionAtom => Doc::text(self.ast.node_span(node).slice(self.source)),
            NodeTag::VersionUnary => {
                let op = self
                    .ast
                    .token_text(self.ast.node_main_token(node), self.source);
                let sep = if op == "!" { "" } else { " " };
                Doc::concat(vec![
                    Doc::text(format!("{op}{sep}")),
                    self.build_version_expr(NodeIndex(data.lhs)),
                ])
            }
            NodeTag::VersionBinary => {
                let op = self
                    .ast
                    .token_text(self.ast.node_main_token(node), self.source);
                Doc::group(Doc::concat(vec![
                    self.build_version_expr(NodeIndex(data.lhs)),
                    Doc::text(format!(" {op}")),
                    Doc::indent(
                        2,
                        Doc::concat(vec![
                            Doc::space_or_line(),
                            self.build_version_expr(NodeIndex(data.rhs)),
                        ]),
                    ),
                ]))
            }
            _ => Doc::Nil,
        }
    }

    fn build_decl(&mut self, node: NodeIndex) -> Doc {
        match self.ast.node_tag(node) {
            NodeTag::PragmaDecl => {
                let decl = self.ast.pragma_decl(node);
                Doc::concat(vec![
                    Doc::text(format!(
                        "pragma {} ",
                        self.ast.token_text(decl.name_token, self.source)
                    )),
                    self.build_version_expr(decl.expr),
                    Doc::text(";"),
                ])
            }
            NodeTag::IncludeDecl => {
                let decl = self.ast.include_decl(node);
                Doc::text(format!(
                    "include {};",
                    self.ast.token_text(decl.path_token, self.source)
                ))
            }
            NodeTag::ModuleDecl => {
                let decl = self.ast.module_decl(node);
                let mut header = Vec::new();
                if decl.exported {
                    header.push(Doc::text("export "));
                }
                header.push(Doc::text(format!(
                    "module {}",
                    self.ast.token_text(decl.name_token, self.source)
                )));
                header.push(self.build_generic_params(decl.gparams_start, decl.gparams_end));

                let inner: Vec<_> = self
                    .ast
                    .extra_nodes(decl.decls_start, decl.decls_end)
                    .collect();
                let rbrace_start = self.ast.token_span(decl.rbrace_token).start;
                if inner.is_empty() {
                    let inside_cmts = self.take_comments_before_byte(rbrace_start, false);
                    if inside_cmts.is_empty() {
                        header.push(Doc::text(" {}"));
                    } else {
                        header.push(Doc::text(" {"));
                        let mut body = vec![Doc::HardLine];
                        body.extend(inside_cmts);
                        header.push(Doc::indent(2, Doc::concat(body)));
                        header.push(Doc::HardLine);
                        header.push(Doc::text("}"));
                    }
                    return Doc::concat(header);
                }

                let mut body = Vec::new();
                for (i, d) in inner.into_iter().enumerate() {
                    if i == 0 {
                        body.push(Doc::HardLine);
                    } else {
                        body.push(Doc::BlankLine);
                    }
                    let first_tok = self.decl_first_token(d);
                    body.extend(self.take_leading_comments(first_tok));
                    body.push(self.build_decl(d));
                    let end_byte = self.node_full_end(d);
                    body.push(self.take_trailing_comment(end_byte));
                }
                let tail_cmts = self.take_comments_before_byte(rbrace_start, false);
                if !tail_cmts.is_empty() {
                    body.push(Doc::HardLine);
                    body.extend(tail_cmts);
                }
                header.push(Doc::text(" {"));
                header.push(Doc::indent(2, Doc::concat(body)));
                header.push(Doc::HardLine);
                header.push(Doc::text("}"));
                Doc::concat(header)
            }
            NodeTag::ImportDecl => {
                let decl = self.ast.import_decl(node);
                let mut parts = vec![Doc::text("import ")];
                let items: Vec<_> = self
                    .ast
                    .extra_nodes(decl.items_start, decl.items_end)
                    .collect();
                if !items.is_empty() {
                    let item_docs: Vec<Doc> = items
                        .into_iter()
                        .map(|item_node| {
                            let item = self.ast.import_item(item_node);
                            let name = self.ast.token_text(item.name_token, self.source);
                            if let Some(alias) = item.alias_token {
                                Doc::text(format!(
                                    "{name} as {}",
                                    self.ast.token_text(alias, self.source)
                                ))
                            } else {
                                Doc::text(name)
                            }
                        })
                        .collect();
                    parts.push(Doc::delimited_list("{", item_docs, "}", " "));
                    parts.push(Doc::text(" from "));
                }
                parts.push(Doc::text(self.ast.token_text(decl.name_token, self.source)));
                let gargs: Vec<_> = self
                    .ast
                    .extra_nodes(decl.gargs_start, decl.gargs_end)
                    .collect();
                if !gargs.is_empty() {
                    let garg_docs = gargs.into_iter().map(|g| self.build_type(g)).collect();
                    parts.push(Doc::delimited_list("<", garg_docs, ">", ""));
                }
                if let Some(prefix) = decl.prefix_token {
                    parts.push(Doc::text(format!(
                        " prefix {}",
                        self.ast.token_text(prefix, self.source)
                    )));
                }
                parts.push(Doc::text(";"));
                Doc::group(Doc::concat(parts))
            }
            NodeTag::ExportListDecl => {
                let decl = self.ast.export_list_decl(node);
                let names: Vec<Doc> = self
                    .ast
                    .extra_tokens(decl.names_start, decl.names_end)
                    .map(|t| Doc::text(self.ast.token_text(t, self.source)))
                    .collect();
                Doc::concat(vec![
                    Doc::text("export "),
                    Doc::delimited_list("{", names, "}", " "),
                    Doc::text(";"),
                ])
            }
            NodeTag::TypeDecl => {
                let decl = self.ast.type_decl(node);
                let mut parts = Vec::new();
                if decl.exported {
                    parts.push(Doc::text("export "));
                }
                if decl.is_new {
                    parts.push(Doc::text("new "));
                }
                parts.push(Doc::text(format!(
                    "type {}",
                    self.ast.token_text(decl.name_token, self.source)
                )));
                parts.push(self.build_generic_params(decl.gparams_start, decl.gparams_end));
                parts.push(Doc::text(" = "));
                parts.push(self.build_type(decl.target_type));
                parts.push(Doc::text(";"));
                Doc::group(Doc::concat(parts))
            }
            NodeTag::EnumDecl => {
                let decl = self.ast.enum_decl(node);
                let mut parts = Vec::new();
                if decl.exported {
                    parts.push(Doc::text("export "));
                }
                parts.push(Doc::text(format!(
                    "enum {} ",
                    self.ast.token_text(decl.name_token, self.source)
                )));
                let variants: Vec<TokenIndex> = self
                    .ast
                    .extra_tokens(decl.variants_start, decl.variants_end)
                    .collect();
                let mut variant_docs = Vec::with_capacity(variants.len());
                for tok in variants {
                    let mut vparts = self.take_leading_comments(tok);
                    vparts.push(Doc::text(self.ast.token_text(tok, self.source)));
                    variant_docs.push(Doc::concat(vparts));
                }
                parts.push(Doc::delimited_list("{", variant_docs, "}", " "));
                Doc::concat(parts)
            }
            NodeTag::StructDecl => {
                let decl = self.ast.struct_decl(node);
                let mut parts = Vec::new();
                if decl.exported {
                    parts.push(Doc::text("export "));
                }
                parts.push(Doc::text(format!(
                    "struct {}",
                    self.ast.token_text(decl.name_token, self.source)
                )));
                parts.push(self.build_generic_params(decl.gparams_start, decl.gparams_end));

                let fields: Vec<_> = self
                    .ast
                    .extra_nodes(decl.fields_start, decl.fields_end)
                    .collect();
                let rbrace_start = self
                    .find_token_after(self.ast.node_main_token(node), TokenTag::LBrace)
                    .map(|open| {
                        let close =
                            self.matching_close_token(open, TokenTag::LBrace, TokenTag::RBrace);
                        self.ast.token_span(close).start
                    })
                    .unwrap_or(self.ast.node_span(node).end);

                if fields.is_empty() {
                    let inside = self.take_comments_before_byte(rbrace_start, false);
                    if inside.is_empty() {
                        parts.push(Doc::text(" {}"));
                    } else {
                        parts.push(Doc::text(" {"));
                        let mut body = vec![Doc::HardLine];
                        body.extend(inside);
                        parts.push(Doc::indent(2, Doc::concat(body)));
                        parts.push(Doc::HardLine);
                        parts.push(Doc::text("}"));
                    }
                    return Doc::concat(parts);
                }

                let mut body = Vec::new();
                for f in fields {
                    body.push(Doc::HardLine);
                    let sf = self.ast.struct_field(f);
                    body.extend(self.take_leading_comments(sf.name_token));
                    body.push(Doc::group(Doc::concat(vec![
                        Doc::text(format!(
                            "{}: ",
                            self.ast.token_text(sf.name_token, self.source)
                        )),
                        self.build_type(sf.type_node),
                        Doc::text(";"),
                    ])));
                    let fend = self.node_full_end(f);
                    body.push(self.take_trailing_comment(fend));
                }
                let tail_cmts = self.take_comments_before_byte(rbrace_start, false);
                if !tail_cmts.is_empty() {
                    body.push(Doc::HardLine);
                    body.extend(tail_cmts);
                }
                parts.push(Doc::text(" {"));
                parts.push(Doc::indent(2, Doc::concat(body)));
                parts.push(Doc::HardLine);
                parts.push(Doc::text("}"));
                Doc::concat(parts)
            }
            NodeTag::ContractDecl => {
                let decl = self.ast.contract_decl(node);
                let mut parts = Vec::new();
                if decl.exported {
                    parts.push(Doc::text("export "));
                }
                parts.push(Doc::text(format!(
                    "contract {}",
                    self.ast.token_text(decl.name_token, self.source)
                )));

                let circuits: Vec<_> = self
                    .ast
                    .extra_nodes(decl.circuits_start, decl.circuits_end)
                    .collect();
                let rbrace_start = self
                    .find_token_after(self.ast.node_main_token(node), TokenTag::LBrace)
                    .map(|open| {
                        let close =
                            self.matching_close_token(open, TokenTag::LBrace, TokenTag::RBrace);
                        self.ast.token_span(close).start
                    })
                    .unwrap_or(self.ast.node_span(node).end);

                if circuits.is_empty() {
                    let inside = self.take_comments_before_byte(rbrace_start, false);
                    if inside.is_empty() {
                        parts.push(Doc::text(" { }"));
                    } else {
                        parts.push(Doc::text(" {"));
                        let mut body = vec![Doc::HardLine];
                        body.extend(inside);
                        parts.push(Doc::indent(2, Doc::concat(body)));
                        parts.push(Doc::HardLine);
                        parts.push(Doc::text("}"));
                    }
                    return Doc::concat(parts);
                }

                let mut body = Vec::new();
                for cc_node in circuits {
                    body.push(Doc::HardLine);
                    let cc = self.ast.contract_circuit(cc_node);
                    let first_tok = if cc.pure {
                        TokenIndex(self.ast.node_main_token(cc_node).0.saturating_sub(1))
                    } else {
                        self.ast.node_main_token(cc_node)
                    };
                    body.extend(self.take_leading_comments(first_tok));
                    let mut sig = Vec::new();
                    if cc.pure {
                        sig.push(Doc::text("pure "));
                    }
                    sig.push(Doc::text(format!(
                        "circuit {}",
                        self.ast.token_text(cc.name_token, self.source)
                    )));
                    sig.push(self.build_params(cc.params_start, cc.params_end));
                    sig.push(Doc::text(": "));
                    sig.push(self.build_type(cc.ret_type));
                    sig.push(Doc::text(";"));
                    body.push(Doc::group(Doc::concat(sig)));
                    let cend = self.node_full_end(cc_node);
                    body.push(self.take_trailing_comment(cend));
                }
                let tail_cmts = self.take_comments_before_byte(rbrace_start, false);
                if !tail_cmts.is_empty() {
                    body.push(Doc::HardLine);
                    body.extend(tail_cmts);
                }
                parts.push(Doc::text(" {"));
                parts.push(Doc::indent(2, Doc::concat(body)));
                parts.push(Doc::HardLine);
                parts.push(Doc::text("}"));
                Doc::concat(parts)
            }
            NodeTag::ContractImplementsDecl => {
                let decl = self.ast.contract_implements_decl(node);
                Doc::concat(vec![
                    Doc::text("contract implements "),
                    self.build_type(decl.type_node),
                    Doc::text(";"),
                ])
            }
            NodeTag::LedgerDecl => {
                let decl = self.ast.ledger_decl(node);
                let mut parts = Vec::new();
                if decl.exported {
                    parts.push(Doc::text("export "));
                }
                if decl.sealed {
                    parts.push(Doc::text("sealed "));
                }
                parts.push(Doc::text(format!(
                    "ledger {}: ",
                    self.ast.token_text(decl.name_token, self.source)
                )));
                parts.push(self.build_type(decl.type_node));
                parts.push(Doc::text(";"));
                Doc::group(Doc::concat(parts))
            }
            NodeTag::WitnessDecl => {
                let decl = self.ast.witness_decl(node);
                let mut parts = Vec::new();
                if decl.exported {
                    parts.push(Doc::text("export "));
                }
                parts.push(Doc::text(format!(
                    "witness {}",
                    self.ast.token_text(decl.name_token, self.source)
                )));
                parts.push(self.build_generic_params(decl.gparams_start, decl.gparams_end));
                parts.push(self.build_params(decl.params_start, decl.params_end));
                parts.push(Doc::text(": "));
                parts.push(self.build_type(decl.ret_type));
                parts.push(Doc::text(";"));
                Doc::group(Doc::concat(parts))
            }
            NodeTag::ConstructorDecl => {
                let decl = self.ast.constructor_decl(node);
                Doc::concat(vec![
                    Doc::group(Doc::concat(vec![
                        Doc::text("constructor"),
                        self.build_params(decl.params_start, decl.params_end),
                    ])),
                    Doc::text(" "),
                    self.build_block(decl.body),
                ])
            }
            NodeTag::CircuitDecl => {
                let decl = self.ast.circuit_decl(node);
                let mut sig = Vec::new();
                if decl.exported {
                    sig.push(Doc::text("export "));
                }
                if decl.pure {
                    sig.push(Doc::text("pure "));
                }
                sig.push(Doc::text(format!(
                    "circuit {}",
                    self.ast.token_text(decl.name_token, self.source)
                )));
                sig.push(self.build_generic_params(decl.gparams_start, decl.gparams_end));
                sig.push(self.build_params(decl.params_start, decl.params_end));
                sig.push(Doc::text(": "));
                sig.push(self.build_type(decl.ret_type));
                Doc::concat(vec![
                    Doc::group(Doc::concat(sig)),
                    Doc::text(" "),
                    self.build_block(decl.body),
                ])
            }
            _ => Doc::Nil,
        }
    }

    fn build_params(&self, start: u32, end: u32) -> Doc {
        let params: Vec<Doc> = self
            .ast
            .extra_nodes(start, end)
            .map(|param| {
                let p = self.ast.param(param);
                let name = self.ast.token_text(p.name_token, self.source);
                if p.type_node.is_some() {
                    Doc::concat(vec![
                        Doc::text(format!("{name}: ")),
                        self.build_type(p.type_node),
                    ])
                } else {
                    Doc::text(name)
                }
            })
            .collect();
        Doc::delimited_list("(", params, ")", "")
    }

    fn build_type(&self, node: NodeIndex) -> Doc {
        let data = self.ast.node_data(node);
        match self.ast.node_tag(node) {
            NodeTag::TypeNamed | NodeTag::TypeNat | NodeTag::TypeString => Doc::text(
                self.ast
                    .token_text(self.ast.node_main_token(node), self.source),
            ),
            NodeTag::TypeRange => Doc::concat(vec![
                self.build_type(NodeIndex(data.lhs)),
                Doc::text(".."),
                self.build_type(NodeIndex(data.rhs)),
            ]),
            NodeTag::TypeGeneric => {
                let name = self
                    .ast
                    .token_text(self.ast.node_main_token(node), self.source);
                let args: Vec<Doc> = self
                    .ast
                    .extra_nodes(data.lhs, data.rhs)
                    .map(|a| self.build_type(a))
                    .collect();
                Doc::concat(vec![
                    Doc::text(name),
                    Doc::delimited_list("<", args, ">", ""),
                ])
            }
            NodeTag::TypeTuple => {
                let elems: Vec<Doc> = self
                    .ast
                    .extra_nodes(data.lhs, data.rhs)
                    .map(|e| self.build_type(e))
                    .collect();
                Doc::delimited_list("[", elems, "]", "")
            }
            _ => Doc::Nil,
        }
    }

    fn build_block(&mut self, node: NodeIndex) -> Doc {
        let data = self.ast.node_data(node);
        let stmts: Vec<_> = self.ast.extra_nodes(data.lhs, data.rhs).collect();
        let open_tok = self.ast.node_main_token(node);
        let close_tok = self.matching_close_token(open_tok, TokenTag::LBrace, TokenTag::RBrace);
        let rbrace_start = self.ast.token_span(close_tok).start;

        if stmts.is_empty() {
            let inside = self.take_comments_before_byte(rbrace_start, false);
            if inside.is_empty() {
                return Doc::text("{}");
            }
            let mut body = vec![Doc::HardLine];
            body.extend(inside);
            return Doc::concat(vec![
                Doc::text("{"),
                Doc::indent(2, Doc::concat(body)),
                Doc::HardLine,
                Doc::text("}"),
            ]);
        }

        let mut body = Vec::new();
        let mut prev_end: Option<u32> = None;
        for stmt in stmts {
            let first_tok = self.stmt_first_token(stmt);
            let next_start = self.next_item_start(first_tok);
            if let Some(pe) = prev_end {
                if self.has_blank_line(pe, next_start) {
                    body.push(Doc::BlankLine);
                } else {
                    body.push(Doc::HardLine);
                }
            } else {
                body.push(Doc::HardLine);
            }
            body.extend(self.take_leading_comments(first_tok));
            body.push(self.build_stmt(stmt));
            let end_byte = self.node_full_end(stmt);
            body.push(self.take_trailing_comment(end_byte));
            prev_end = Some(end_byte);
        }

        let tail_cmts = self.take_comments_before_byte(rbrace_start, false);
        if !tail_cmts.is_empty() {
            if let Some(pe) = prev_end
                && let Some(first_cmt_start) = self
                    .ast
                    .comments
                    .span()
                    .get(self.next_comment.saturating_sub(1))
                    .map(|s| s.start)
                && self.has_blank_line(pe, first_cmt_start)
            {
                body.push(Doc::BlankLine);
            } else {
                body.push(Doc::HardLine);
            }
            body.extend(tail_cmts);
        }

        Doc::concat(vec![
            Doc::text("{"),
            Doc::indent(2, Doc::concat(body)),
            Doc::HardLine,
            Doc::text("}"),
        ])
    }

    /// Byte offset of either the next leading comment before `tok` or `tok` itself.
    fn next_item_start(&self, tok: TokenIndex) -> u32 {
        let before_tokens = self.ast.comments.before_token();
        if self.next_comment < before_tokens.len() && before_tokens[self.next_comment] <= tok {
            self.ast.comments.span()[self.next_comment].start
        } else {
            self.ast.token_span(tok).start
        }
    }

    fn stmt_first_token(&self, node: NodeIndex) -> TokenIndex {
        let span_start = self.ast.node_span(node).start;
        let spans = self.ast.tokens.span();
        // Fast path: check main token first.
        let main = self.ast.node_main_token(node);
        if self.ast.token_span(main).start == span_start {
            return main;
        }
        // Binary search for the first token starting at `span_start`.
        match spans.binary_search_by_key(&span_start, |s| s.start) {
            Ok(idx) => TokenIndex(idx as u32),
            Err(idx) => TokenIndex(idx.min(spans.len().saturating_sub(1)) as u32),
        }
    }

    fn build_stmt(&mut self, node: NodeIndex) -> Doc {
        let data = self.ast.node_data(node);
        match self.ast.node_tag(node) {
            NodeTag::Block => self.build_block(node),
            NodeTag::IfStmt => {
                let stmt = self.ast.if_stmt(node);
                let mut parts = vec![
                    Doc::group(Doc::concat(vec![
                        Doc::text("if ("),
                        Doc::indent(
                            2,
                            Doc::concat(vec![Doc::soft_line(), self.build_expr(stmt.cond)]),
                        ),
                        Doc::soft_line(),
                        Doc::text(")"),
                    ])),
                    Doc::text(" "),
                ];
                if self.ast.node_tag(stmt.then_branch) == NodeTag::Block {
                    parts.push(self.build_block(stmt.then_branch));
                } else {
                    parts.push(self.build_stmt(stmt.then_branch));
                }
                if let Some(else_branch) = stmt.else_branch {
                    parts.push(Doc::text(" else "));
                    match self.ast.node_tag(else_branch) {
                        NodeTag::Block => parts.push(self.build_block(else_branch)),
                        _ => parts.push(self.build_stmt(else_branch)),
                    }
                }
                Doc::concat(parts)
            }
            NodeTag::ForRangeStmt => {
                let stmt = self.ast.for_range_stmt(node);
                let header = Doc::group(Doc::concat(vec![
                    Doc::text(format!(
                        "for (const {} of ",
                        self.ast.token_text(stmt.name_token, self.source)
                    )),
                    self.build_expr(stmt.start),
                    Doc::text(".."),
                    self.build_expr(stmt.end),
                    Doc::text(")"),
                ]));
                let body = if self.ast.node_tag(stmt.body) == NodeTag::Block {
                    self.build_block(stmt.body)
                } else {
                    self.build_stmt(stmt.body)
                };
                Doc::concat(vec![header, Doc::text(" "), body])
            }
            NodeTag::ForEachStmt => {
                let stmt = self.ast.for_each_stmt(node);
                let header = Doc::group(Doc::concat(vec![
                    Doc::text(format!(
                        "for (const {} of ",
                        self.ast.token_text(stmt.name_token, self.source)
                    )),
                    self.build_expr(stmt.iter),
                    Doc::text(")"),
                ]));
                let body = if self.ast.node_tag(stmt.body) == NodeTag::Block {
                    self.build_block(stmt.body)
                } else {
                    self.build_stmt(stmt.body)
                };
                Doc::concat(vec![header, Doc::text(" "), body])
            }
            NodeTag::ConstStmt => {
                let stmt = self.ast.const_stmt(node);
                let mut lhs = vec![Doc::text("const "), self.build_pattern(stmt.pat)];
                if let Some(ty) = stmt.ty {
                    lhs.push(Doc::text(": "));
                    lhs.push(self.build_type(ty));
                }
                lhs.push(Doc::text(" ="));
                let rhs = self.build_expr(stmt.init);
                if self.prefer_inline_rhs(stmt.init) {
                    Doc::group(Doc::concat(vec![
                        Doc::concat(lhs),
                        Doc::text(" "),
                        rhs,
                        Doc::text(";"),
                    ]))
                } else {
                    Doc::group(Doc::concat(vec![
                        Doc::concat(lhs),
                        Doc::indent(2, Doc::concat(vec![Doc::space_or_line(), rhs])),
                        Doc::text(";"),
                    ]))
                }
            }
            NodeTag::AssignStmt => {
                let stmt = self.ast.assign_stmt(node);
                let op = self.ast.token_text(stmt.eq_token, self.source);
                let lhs = Doc::concat(vec![self.build_expr(stmt.lhs), Doc::text(format!(" {op}"))]);
                let rhs = self.build_expr(stmt.rhs);
                if self.prefer_inline_rhs(stmt.rhs) {
                    Doc::group(Doc::concat(vec![lhs, Doc::text(" "), rhs, Doc::text(";")]))
                } else {
                    Doc::group(Doc::concat(vec![
                        lhs,
                        Doc::indent(2, Doc::concat(vec![Doc::space_or_line(), rhs])),
                        Doc::text(";"),
                    ]))
                }
            }
            NodeTag::ExprStmt => {
                Doc::concat(vec![self.build_expr(NodeIndex(data.lhs)), Doc::text(";")])
            }
            NodeTag::ReturnStmt => {
                if let Some(expr) = NodeIndex(data.lhs).into_option() {
                    if self.prefer_inline_rhs(expr) {
                        Doc::group(Doc::concat(vec![
                            Doc::text("return "),
                            self.build_expr(expr),
                            Doc::text(";"),
                        ]))
                    } else {
                        Doc::group(Doc::concat(vec![
                            Doc::text("return"),
                            Doc::indent(
                                2,
                                Doc::concat(vec![Doc::space_or_line(), self.build_expr(expr)]),
                            ),
                            Doc::text(";"),
                        ]))
                    }
                } else {
                    Doc::text("return;")
                }
            }
            _ => Doc::Nil,
        }
    }

    /// Expressions with their own structured internal line-breaking (`CallExpr`, `StructLitExpr`,
    /// `TupleExpr`, `ArrowExpr`, etc.) look cleaner breaking internally rather than pushing their
    /// head onto a new line right after `=` or `return`.
    fn prefer_inline_rhs(&self, expr: NodeIndex) -> bool {
        matches!(
            self.ast.node_tag(expr),
            NodeTag::CallExpr
                | NodeTag::GenericCallExpr
                | NodeTag::StructLitExpr
                | NodeTag::TupleExpr
                | NodeTag::BytesLitExpr
                | NodeTag::ArrowExpr
                | NodeTag::BinaryExpr
                | NodeTag::TernaryExpr
                | NodeTag::DiscloseExpr
                | NodeTag::EmitExpr
                | NodeTag::AssertExpr
                | NodeTag::IdentExpr
                | NodeTag::IntLitExpr
                | NodeTag::BoolLitExpr
                | NodeTag::StringLitExpr
                | NodeTag::DefaultExpr
        )
    }

    fn binary_op_prec(op: &str) -> u8 {
        match op {
            "||" => 2,
            "&&" => 3,
            "==" | "!=" => 4,
            "<" | "<=" | ">" | ">=" => 5,
            "+" | "-" => 7,
            "*" => 8,
            _ => 7,
        }
    }

    fn expr_prec(&self, node: NodeIndex) -> u8 {
        match self.ast.node_tag(node) {
            NodeTag::ArrowExpr => 0,
            NodeTag::TernaryExpr => 1,
            NodeTag::BinaryExpr => {
                let op = self
                    .ast
                    .token_text(self.ast.node_main_token(node), self.source);
                Self::binary_op_prec(op)
            }
            NodeTag::CastExpr => 6,
            NodeTag::UnaryExpr => 9,
            _ => 10,
        }
    }

    fn build_expr_with_min_prec(&mut self, node: NodeIndex, min_prec: u8) -> Doc {
        if self.expr_prec(node) < min_prec {
            Doc::group(Doc::concat(vec![
                Doc::text("("),
                Doc::indent(
                    2,
                    Doc::concat(vec![Doc::soft_line(), self.build_expr(node)]),
                ),
                Doc::soft_line(),
                Doc::text(")"),
            ]))
        } else {
            self.build_expr(node)
        }
    }

    /// Flatten a left-associative chain of binary expressions with the same operator precedence
    /// (`&&`, `||`, `+`, `-`, `*`) so the entire chain wraps uniformly at its operators.
    fn collect_binary_chain<'b>(
        &self,
        node: NodeIndex,
        target_prec: u8,
        out_first: &mut Option<NodeIndex>,
        out_rest: &mut Vec<(&'b str, NodeIndex)>,
    ) where
        'a: 'b,
    {
        if self.ast.node_tag(node) == NodeTag::BinaryExpr {
            let op = self
                .ast
                .token_text(self.ast.node_main_token(node), self.source);
            if Self::binary_op_prec(op) == target_prec
                && matches!(op, "&&" | "||" | "+" | "-" | "*")
            {
                let data = self.ast.node_data(node);
                self.collect_binary_chain(NodeIndex(data.lhs), target_prec, out_first, out_rest);
                out_rest.push((op, NodeIndex(data.rhs)));
                return;
            }
        }
        *out_first = Some(node);
    }

    fn build_expr(&mut self, node: NodeIndex) -> Doc {
        let data = self.ast.node_data(node);
        match self.ast.node_tag(node) {
            NodeTag::IdentExpr
            | NodeTag::IntLitExpr
            | NodeTag::BoolLitExpr
            | NodeTag::StringLitExpr => Doc::text(
                self.ast
                    .token_text(self.ast.node_main_token(node), self.source),
            ),
            NodeTag::TupleExpr => {
                let elems: Vec<_> = self.ast.extra_nodes(data.lhs, data.rhs).collect();
                let mut items = Vec::with_capacity(elems.len());
                for elem in elems {
                    let start = self.ast.node_span(elem).start;
                    let mut iparts = self.take_comments_before_byte(start, true);
                    iparts.push(self.build_expr(elem));
                    items.push(Doc::concat(iparts));
                }
                Doc::delimited_list("[", items, "]", "")
            }
            NodeTag::MemberExpr => Doc::concat(vec![
                self.build_expr_with_min_prec(NodeIndex(data.lhs), 10),
                Doc::text("."),
                Doc::text(self.ast.token_text(TokenIndex(data.rhs), self.source)),
            ]),
            NodeTag::IndexExpr => {
                let idx = self.ast.index_expr(node);
                Doc::concat(vec![
                    self.build_expr_with_min_prec(idx.base, 10),
                    Doc::text("["),
                    self.build_expr(idx.index),
                    Doc::text("]"),
                ])
            }
            NodeTag::CallExpr => {
                let call = self.ast.call_expr(node);
                let callee = self.build_expr_with_min_prec(call.callee, 10);
                let args: Vec<_> = self
                    .ast
                    .extra_nodes(call.args_start, call.args_end)
                    .collect();
                let mut arg_docs = Vec::with_capacity(args.len());
                for arg in args {
                    let start = self.ast.node_span(arg).start;
                    let mut aparts = self.take_comments_before_byte(start, true);
                    aparts.push(self.build_expr(arg));
                    arg_docs.push(Doc::concat(aparts));
                }
                Doc::concat(vec![callee, Doc::delimited_list("(", arg_docs, ")", "")])
            }
            NodeTag::GenericCallExpr => {
                let call = self.ast.generic_call_expr(node);
                let callee = self.build_expr_with_min_prec(call.callee, 10);
                let targs: Vec<Doc> = self
                    .ast
                    .extra_nodes(call.targs_start, call.targs_end)
                    .map(|t| self.build_type(t))
                    .collect();
                let args: Vec<_> = self
                    .ast
                    .extra_nodes(call.args_start, call.args_end)
                    .collect();
                let mut arg_docs = Vec::with_capacity(args.len());
                for arg in args {
                    let start = self.ast.node_span(arg).start;
                    let mut aparts = self.take_comments_before_byte(start, true);
                    aparts.push(self.build_expr(arg));
                    arg_docs.push(Doc::concat(aparts));
                }
                Doc::concat(vec![
                    callee,
                    Doc::delimited_list("<", targs, ">", ""),
                    Doc::delimited_list("(", arg_docs, ")", ""),
                ])
            }
            NodeTag::UnaryExpr => Doc::concat(vec![
                Doc::text(
                    self.ast
                        .token_text(self.ast.node_main_token(node), self.source),
                ),
                self.build_expr_with_min_prec(NodeIndex(data.lhs), 9),
            ]),
            NodeTag::BinaryExpr => {
                let op = self
                    .ast
                    .token_text(self.ast.node_main_token(node), self.source);
                let prec = Self::binary_op_prec(op);
                if matches!(op, "&&" | "||" | "+" | "-" | "*") {
                    let mut first = None;
                    let mut rest = Vec::new();
                    self.collect_binary_chain(node, prec, &mut first, &mut rest);
                    let first_node = first.unwrap();
                    let mut parts = vec![self.build_expr_with_min_prec(first_node, prec)];
                    let mut tail = Vec::with_capacity(rest.len() * 3);
                    for (chain_op, rhs_node) in rest {
                        let rhs_min = match chain_op {
                            "+" | "*" | "&&" | "||" => prec,
                            _ => prec + 1,
                        };
                        tail.push(Doc::text(format!(" {chain_op}")));
                        tail.push(Doc::space_or_line());
                        tail.push(self.build_expr_with_min_prec(rhs_node, rhs_min));
                    }
                    parts.push(Doc::indent(2, Doc::concat(tail)));
                    Doc::group(Doc::concat(parts))
                } else {
                    let rhs_min = prec + 1;
                    Doc::group(Doc::concat(vec![
                        self.build_expr_with_min_prec(NodeIndex(data.lhs), prec),
                        Doc::text(format!(" {op}")),
                        Doc::indent(
                            2,
                            Doc::concat(vec![
                                Doc::space_or_line(),
                                self.build_expr_with_min_prec(NodeIndex(data.rhs), rhs_min),
                            ]),
                        ),
                    ]))
                }
            }
            NodeTag::TernaryExpr => {
                let t = self.ast.ternary_expr(node);
                Doc::group(Doc::concat(vec![
                    self.build_expr_with_min_prec(t.cond, 2),
                    Doc::indent(
                        2,
                        Doc::concat(vec![
                            Doc::space_or_line(),
                            Doc::text("? "),
                            self.build_expr(t.then_branch),
                            Doc::space_or_line(),
                            Doc::text(": "),
                            self.build_expr(t.else_branch),
                        ]),
                    ),
                ]))
            }
            NodeTag::CastExpr => Doc::group(Doc::concat(vec![
                self.build_expr_with_min_prec(NodeIndex(data.lhs), 6),
                Doc::text(" as "),
                self.build_type(NodeIndex(data.rhs)),
            ])),
            NodeTag::DefaultExpr => Doc::concat(vec![
                Doc::text("default<"),
                self.build_type(NodeIndex(data.lhs)),
                Doc::text(">"),
            ]),
            NodeTag::AssertExpr => {
                let a = self.ast.assert_expr(node);
                let items = vec![self.build_expr(a.cond), self.build_expr(a.msg)];
                Doc::concat(vec![
                    Doc::text("assert"),
                    Doc::delimited_list("(", items, ")", ""),
                ])
            }
            NodeTag::DiscloseExpr => Doc::group(Doc::concat(vec![
                Doc::text("disclose("),
                Doc::indent(
                    2,
                    Doc::concat(vec![Doc::soft_line(), self.build_expr(NodeIndex(data.lhs))]),
                ),
                Doc::soft_line(),
                Doc::text(")"),
            ])),
            NodeTag::EmitExpr => Doc::group(Doc::concat(vec![
                Doc::text("emit("),
                Doc::indent(
                    2,
                    Doc::concat(vec![Doc::soft_line(), self.build_expr(NodeIndex(data.lhs))]),
                ),
                Doc::soft_line(),
                Doc::text(")"),
            ])),
            NodeTag::StructLitExpr => {
                let lit = self.ast.struct_lit_expr(node);
                let ty = self.build_type(lit.type_node);
                let fields: Vec<_> = self
                    .ast
                    .extra_nodes(lit.fields_start, lit.fields_end)
                    .collect();
                if fields.is_empty() {
                    return Doc::concat(vec![ty, Doc::text("{}")]);
                }
                let mut field_docs = Vec::with_capacity(fields.len());
                for f in fields {
                    let start = self.ast.node_span(f).start;
                    let mut fparts = self.take_comments_before_byte(start, true);
                    if self.ast.node_tag(f) == NodeTag::StructLitField {
                        let sf = self.ast.struct_lit_field(f);
                        fparts.push(Doc::text(format!(
                            "{}: ",
                            self.ast.token_text(sf.name_token, self.source)
                        )));
                        fparts.push(self.build_expr(sf.value));
                    } else {
                        fparts.push(self.build_expr(f));
                    }
                    field_docs.push(Doc::concat(fparts));
                }
                Doc::concat(vec![ty, Doc::delimited_list("{", field_docs, "}", " ")])
            }
            NodeTag::SpreadExpr => {
                Doc::concat(vec![Doc::text("..."), self.build_expr(NodeIndex(data.lhs))])
            }
            NodeTag::BytesLitExpr => {
                let lit = self.ast.bytes_lit_expr(node);
                let elems: Vec<Doc> = self
                    .ast
                    .extra_nodes(lit.elems_start, lit.elems_end)
                    .map(|e| self.build_expr(e))
                    .collect();
                Doc::concat(vec![
                    Doc::text("Bytes"),
                    Doc::delimited_list("[", elems, "]", ""),
                ])
            }
            NodeTag::ArrowExpr => {
                let arrow = self.ast.arrow_expr(node);
                let mut header = vec![self.build_params(arrow.params_start, arrow.params_end)];
                if let Some(ret) = arrow.ret_type {
                    header.push(Doc::text(": "));
                    header.push(self.build_type(ret));
                }
                header.push(Doc::text(" => "));
                let body = if self.ast.node_tag(arrow.body) == NodeTag::Block {
                    self.build_block(arrow.body)
                } else {
                    self.build_expr(arrow.body)
                };
                Doc::concat(vec![Doc::group(Doc::concat(header)), body])
            }
            _ => Doc::Nil,
        }
    }

    fn build_pattern(&self, node: NodeIndex) -> Doc {
        let data = self.ast.node_data(node);
        match self.ast.node_tag(node) {
            NodeTag::PatIdent => Doc::text(
                self.ast
                    .token_text(self.ast.node_main_token(node), self.source),
            ),
            NodeTag::PatTuple => {
                let elems: Vec<Doc> = self
                    .ast
                    .extra_nodes(data.lhs, data.rhs)
                    .map(|elem| {
                        if elem.is_some() {
                            self.build_pattern(elem)
                        } else {
                            Doc::Nil
                        }
                    })
                    .collect();
                Doc::delimited_list("[", elems, "]", "")
            }
            NodeTag::PatStruct => {
                let fields: Vec<Doc> = self
                    .ast
                    .extra_nodes(data.lhs, data.rhs)
                    .map(|field| {
                        let sf = self.ast.pat_struct_field(field);
                        let name = self.ast.token_text(sf.name_token, self.source);
                        if let Some(sub) = sf.pat {
                            Doc::concat(vec![
                                Doc::text(format!("{name}: ")),
                                self.build_pattern(sub),
                            ])
                        } else {
                            Doc::text(name)
                        }
                    })
                    .collect();
                Doc::delimited_list("{", fields, "}", " ")
            }
            _ => Doc::Nil,
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
        fmt_width(src, FormatOptions::default().line_length)
    }

    fn fmt_width(src: &str, line_length: usize) -> String {
        let mut sm = SourceMap::new();
        let id = sm.add_file("test.compact", src);
        let parsed = parse(sm.get(id));
        assert!(
            !parsed.diagnostics.has_errors(),
            "unexpected parse errors: {:?}",
            parsed.diagnostics
        );
        format_ast(&parsed.ast, src, &FormatOptions { line_length })
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

    #[test]
    fn format_patterns_arrows_spreads_and_bytes() {
        assert_compact_snapshot!(
            r#"
            import CompactStandardLibrary;
            export ledger ops:Counter;
            struct Point{x:Field;y:Field;}
            export circuit demo(pt:Point,v:Vector<2,Field>,raw:Bytes<4>):[Field,Bytes<4>]{
              const {x:px,y}=pt;
              const [a,b]=v;
              const doubled=map((n)=>n+px,v);
              const sum=fold((acc:Field,n:Field):Field=>{const t=acc+n;return t;},0,doubled);
              const next=Point{...pt,x:sum};
              const ext:Vector<3,Field> = [...doubled,a+b];
              const bv=raw as Vector<4,Uint<8>>;
              const rev=Bytes[bv[3],bv[2],bv[1],bv[0]];
              ops+=2;
              ops-=1;
              return [next.x+ext[2],rev];
            }
            "#,
            fmt
        );
    }

    #[test]
    fn format_contracts_implements_and_emit() {
        assert_compact_snapshot!(
            r#"
            import CompactStandardLibrary;
            export contract Inner{circuit add(v:Field):Field;circuit ping():[];}
            contract Empty{}
            contract implements Empty;
            export ledger inner:Inner;
            export circuit go(n:Bytes<32>):Field{emit(ShieldedSpend{nullifier:disclose(n)});return inner.add(1);}
            "#,
            fmt
        );
    }

    #[test]
    fn format_line_wrapping_at_80_columns() {
        assert_compact_snapshot!(
            r#"
            import CompactStandardLibrary;
            export { Maybe, Either, ShieldedCoinInfo, QualifiedShieldedCoinInfo, ContractAddress, ZswapCoinPublicKey }
            export circuit compute_tiered_bonus_score(user_account_balance: Uint<64>, transaction_total_amount: Uint<64>, accumulated_loyalty_points: Uint<64>, account_age_in_months: Uint<64>): Uint<64> {
              const total = (user_account_balance + transaction_total_amount) + accumulated_loyalty_points + account_age_in_months;
              const ok = user_account_balance > 0 && transaction_total_amount > 0 && accumulated_loyalty_points >= 10 && account_age_in_months >= 1;
              assert(ok, "all bonus eligibility conditions must hold before payout");
              const res = ok ? total : transaction_total_amount;
              return res;
            }
            "#,
            |src| fmt_width(src, 80)
        );
    }

    #[test]
    fn format_preserves_trailing_inline_and_block_comments_and_blank_lines() {
        assert_compact_snapshot!(
            r#"
            // License header line 1
            // License header line 2

            import CompactStandardLibrary; // stdlib import

            struct Config {
              // Threshold comment
              threshold: Uint<64>; // inline field comment
              owner: Bytes<32>;
            }

            export circuit run(x: Field): Field {
              const a = x + 1; // keep trailing

              // Section 2
              const b = a * 2;
              if (x == 0) {
                /* keep inside empty block */
              }
              return b; // final return
              // trailing inside block
            }
            // EOF comment
            "#,
            fmt
        );
    }

    #[test]
    fn format_idempotent_across_widths_and_preserves_all_comments() {
        let src = r#"
// Header comment 1
// Header comment 2

import CompactStandardLibrary; // inline stdlib

struct Record {
  // field a
  alpha: Uint<64>; // trailing a
  beta: Bytes<32>;
}

export circuit process(first_arg: Uint<64>, second_arg: Uint<64>, third_arg: Bytes<32>): Record {
  const combined = first_arg + second_arg + (1 as Uint<64>) + (2 as Uint<64>); // sum
  const ok = first_arg > 0 && second_arg > 0 && combined >= first_arg;
  assert(ok, "combined must remain valid");
  if (ok) {
    /* inside block */
  }
  return Record{ alpha: combined, beta: third_arg }; // done
}
// trailing EOF
"#;
        for width in [40, 60, 80, 100, 120] {
            let once = fmt_width(src, width);
            let twice = fmt_width(&once, width);
            assert_eq!(once, twice, "not idempotent at width {width}");
            for comment in [
                "// Header comment 1",
                "// Header comment 2",
                "// inline stdlib",
                "// field a",
                "// trailing a",
                "// sum",
                "/* inside block */",
                "// done",
                "// trailing EOF",
            ] {
                assert!(
                    once.contains(comment),
                    "lost comment `{comment}` at width {width}:\n{once}"
                );
            }
        }
    }
}
