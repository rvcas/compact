use std::fmt::Write as _;

use compact_span::Span;
use soa_rs::{Soa, Soars};

/// Compact index into [`Ast::tokens`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct TokenIndex(pub u32);

impl TokenIndex {
    pub const NONE: Self = Self(u32::MAX);

    #[inline]
    pub const fn as_usize(self) -> usize {
        self.0 as usize
    }

    #[inline]
    pub const fn is_some(self) -> bool {
        self.0 != u32::MAX
    }
}

/// Compact index into [`Ast::nodes`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct NodeIndex(pub u32);

impl NodeIndex {
    pub const ROOT: Self = Self(0);
    pub const NONE: Self = Self(u32::MAX);

    #[inline]
    pub const fn as_usize(self) -> usize {
        self.0 as usize
    }

    #[inline]
    pub const fn is_some(self) -> bool {
        self.0 != u32::MAX
    }

    #[inline]
    pub const fn into_option(self) -> Option<Self> {
        if self.is_some() { Some(self) } else { None }
    }
}

/// Token tag produced by the Compact lexer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum TokenTag {
    // Keywords
    Import,
    Export,
    Ledger,
    Sealed,
    Circuit,
    Pure,
    Return,
    Witness,
    Pragma,
    Struct,
    Enum,
    Module,
    Const,
    If,
    Else,
    For,
    Assert,
    Disclose,
    True,
    False,
    Default,
    As,
    Contract,
    Constructor,

    // Identifiers and literals
    Ident,
    Nat,
    String,

    // Punctuation and operators
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    LAngle,
    RAngle,
    Colon,
    Semi,
    Comma,
    Dot,
    DotDot,
    Plus,
    Minus,
    Star,
    Eq,
    EqEq,
    BangEq,
    Bang,

    // Special
    Eof,
    Invalid,
}

impl TokenTag {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Import => "import",
            Self::Export => "export",
            Self::Ledger => "ledger",
            Self::Sealed => "sealed",
            Self::Circuit => "circuit",
            Self::Pure => "pure",
            Self::Return => "return",
            Self::Witness => "witness",
            Self::Pragma => "pragma",
            Self::Struct => "struct",
            Self::Enum => "enum",
            Self::Module => "module",
            Self::Const => "const",
            Self::If => "if",
            Self::Else => "else",
            Self::For => "for",
            Self::Assert => "assert",
            Self::Disclose => "disclose",
            Self::True => "true",
            Self::False => "false",
            Self::Default => "default",
            Self::As => "as",
            Self::Contract => "contract",
            Self::Constructor => "constructor",
            Self::Ident => "identifier",
            Self::Nat => "integer literal",
            Self::String => "string literal",
            Self::LParen => "(",
            Self::RParen => ")",
            Self::LBrace => "{",
            Self::RBrace => "}",
            Self::LBracket => "[",
            Self::RBracket => "]",
            Self::LAngle => "<",
            Self::RAngle => ">",
            Self::Colon => ":",
            Self::Semi => ";",
            Self::Comma => ",",
            Self::Dot => ".",
            Self::DotDot => "..",
            Self::Plus => "+",
            Self::Minus => "-",
            Self::Star => "*",
            Self::Eq => "=",
            Self::EqEq => "==",
            Self::BangEq => "!=",
            Self::Bang => "!",
            Self::Eof => "end of file",
            Self::Invalid => "invalid token",
        }
    }
}

/// SoA token row.
#[derive(Soars, Debug, Clone, Copy, PartialEq, Eq)]
#[soa_derive(Debug)]
pub struct Token {
    pub tag: TokenTag,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CommentKind {
    Line,
    Block,
}

/// Comment trivia stored out-of-band so the parser never skips comments in the hot token stream,
/// while the formatter can attach comments cleanly to the token they precede.
#[derive(Soars, Debug, Clone, Copy, PartialEq, Eq)]
#[soa_derive(Debug)]
pub struct Comment {
    pub kind: CommentKind,
    pub span: Span,
    pub before_token: TokenIndex,
}

/// Bitflags packed into `NodeData::rhs` for declaration modifiers.
pub mod decl_flags {
    pub const NONE: u32 = 0;
    pub const EXPORT: u32 = 1 << 0;
    pub const SEALED: u32 = 1 << 1;
    pub const PURE: u32 = 1 << 2;
}

/// Tag identifying the syntactic form of an AST node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum NodeTag {
    /// Program root: `data = (extra_start, extra_end)` listing top-level declarations.
    Root,
    /// `import <ident>;` — `main_token = import`, `data = (name_tok, 0)`.
    ImportDecl,
    /// `[export] [sealed] ledger <name>: <type>;`
    /// `main_token = ledger`, `data = (extra_start, flags)`,
    /// `extra_data[extra_start..+2] = [name_tok, type_node]`.
    LedgerDecl,
    /// `[export] [pure] circuit <name>(<params>): <ret_type> <block>`
    /// `main_token = circuit`, `data = (extra_start, flags)`,
    /// `extra_data[extra_start..+5] = [name_tok, params_start, params_end, ret_type_node, body_node]`.
    CircuitDecl,
    /// `<name>: <type>` — `main_token = name_tok`, `data = (type_node, 0)`.
    Param,
    /// Named type reference (e.g. `Counter`, `Field`) — `main_token = name_tok`.
    TypeNamed,
    /// Tuple type (e.g. `[]`, `[Field, Boolean]`) — `main_token = '['`, `data = (extra_start, extra_end)`.
    TypeTuple,
    /// Block `{ <stmt>* }` — `main_token = '{'`, `data = (extra_start, extra_end)`.
    Block,
    /// Expression statement `<expr>;` — `data = (expr_node, semi_tok)`.
    ExprStmt,
    /// `return [<expr>];` — `main_token = return`, `data = (opt_expr_node, semi_tok)`.
    ReturnStmt,
    /// Identifier expression — `main_token = ident_tok`.
    IdentExpr,
    /// Integer literal expression — `main_token = nat_tok`.
    IntLitExpr,
    /// Tuple literal expression `[<expr>, ...]` — `main_token = '['`, `data = (extra_start, extra_end)`.
    TupleExpr,
    /// Member access `<lhs>.<field>` — `main_token = '.'`, `data = (lhs_node, field_tok)`.
    MemberExpr,
    /// Call expression `<callee>(<args>)`
    /// `main_token = '('`, `data = (extra_start, rparen_tok)`,
    /// `extra_data[extra_start..+3] = [callee_node, args_start, args_end]`.
    CallExpr,
    /// Binary expression `<lhs> <op> <rhs>` — `main_token = op_tok`, `data = (lhs_node, rhs_node)`.
    BinaryExpr,
}

/// Fixed-width payload stored alongside every AST node (Zig-style two-word `Data`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct NodeData {
    pub lhs: u32,
    pub rhs: u32,
}

impl NodeData {
    #[inline]
    pub const fn new(lhs: u32, rhs: u32) -> Self {
        Self { lhs, rhs }
    }
}

/// SoA AST node row.
#[derive(Soars, Debug, Clone, Copy, PartialEq, Eq)]
#[soa_derive(Debug)]
pub struct Node {
    pub tag: NodeTag,
    pub main_token: TokenIndex,
    pub data: NodeData,
}

/// Typed views decoded from [`Ast`] for ergonomic downstream traversal.
#[derive(Debug, Clone, Copy)]
pub struct ImportDecl {
    pub import_token: TokenIndex,
    pub name_token: TokenIndex,
}

#[derive(Debug, Clone, Copy)]
pub struct LedgerDecl {
    pub ledger_token: TokenIndex,
    pub name_token: TokenIndex,
    pub type_node: NodeIndex,
    pub exported: bool,
    pub sealed: bool,
}

#[derive(Debug, Clone, Copy)]
pub struct CircuitDecl {
    pub circuit_token: TokenIndex,
    pub name_token: TokenIndex,
    pub params_start: u32,
    pub params_end: u32,
    pub ret_type: NodeIndex,
    pub body: NodeIndex,
    pub exported: bool,
    pub pure: bool,
}

#[derive(Debug, Clone, Copy)]
pub struct Param {
    pub name_token: TokenIndex,
    pub type_node: NodeIndex,
}

#[derive(Debug, Clone, Copy)]
pub struct CallExpr {
    pub lparen_token: TokenIndex,
    pub rparen_token: TokenIndex,
    pub callee: NodeIndex,
    pub args_start: u32,
    pub args_end: u32,
}

/// Flat Structure-of-Arrays AST inspired by Zig's `std.zig.Ast`.
#[derive(Debug)]
pub struct Ast {
    pub tokens: Soa<Token>,
    pub comments: Soa<Comment>,
    pub nodes: Soa<Node>,
    pub extra_data: Vec<u32>,
}

impl Ast {
    pub fn new(tokens: Soa<Token>, comments: Soa<Comment>) -> Self {
        Self {
            tokens,
            comments,
            nodes: Soa::new(),
            extra_data: Vec::new(),
        }
    }

    pub fn push_node(&mut self, tag: NodeTag, main_token: TokenIndex, data: NodeData) -> NodeIndex {
        let idx = NodeIndex(self.nodes.len() as u32);
        self.nodes.push(Node {
            tag,
            main_token,
            data,
        });
        idx
    }

    pub fn push_extra(&mut self, value: u32) -> u32 {
        let idx = self.extra_data.len() as u32;
        self.extra_data.push(value);
        idx
    }

    pub fn push_extra_slice(&mut self, values: &[u32]) -> (u32, u32) {
        let start = self.extra_data.len() as u32;
        self.extra_data.extend_from_slice(values);
        let end = self.extra_data.len() as u32;
        (start, end)
    }

    #[inline]
    pub fn token_tag(&self, idx: TokenIndex) -> TokenTag {
        self.tokens.tag()[idx.as_usize()]
    }

    #[inline]
    pub fn token_span(&self, idx: TokenIndex) -> Span {
        self.tokens.span()[idx.as_usize()]
    }

    #[inline]
    pub fn token_text<'a>(&self, idx: TokenIndex, source: &'a str) -> &'a str {
        self.token_span(idx).slice(source)
    }

    #[inline]
    pub fn node_tag(&self, idx: NodeIndex) -> NodeTag {
        self.nodes.tag()[idx.as_usize()]
    }

    #[inline]
    pub fn node_main_token(&self, idx: NodeIndex) -> TokenIndex {
        self.nodes.main_token()[idx.as_usize()]
    }

    #[inline]
    pub fn node_data(&self, idx: NodeIndex) -> NodeData {
        self.nodes.data()[idx.as_usize()]
    }

    pub fn extra_nodes(&self, start: u32, end: u32) -> impl Iterator<Item = NodeIndex> + '_ {
        self.extra_data[start as usize..end as usize]
            .iter()
            .copied()
            .map(NodeIndex)
    }

    pub fn root_decls(&self) -> impl Iterator<Item = NodeIndex> + '_ {
        debug_assert_eq!(self.node_tag(NodeIndex::ROOT), NodeTag::Root);
        let data = self.node_data(NodeIndex::ROOT);
        self.extra_nodes(data.lhs, data.rhs)
    }

    pub fn import_decl(&self, node: NodeIndex) -> ImportDecl {
        debug_assert_eq!(self.node_tag(node), NodeTag::ImportDecl);
        let data = self.node_data(node);
        ImportDecl {
            import_token: self.node_main_token(node),
            name_token: TokenIndex(data.lhs),
        }
    }

    pub fn ledger_decl(&self, node: NodeIndex) -> LedgerDecl {
        debug_assert_eq!(self.node_tag(node), NodeTag::LedgerDecl);
        let data = self.node_data(node);
        let base = data.lhs as usize;
        LedgerDecl {
            ledger_token: self.node_main_token(node),
            name_token: TokenIndex(self.extra_data[base]),
            type_node: NodeIndex(self.extra_data[base + 1]),
            exported: (data.rhs & decl_flags::EXPORT) != 0,
            sealed: (data.rhs & decl_flags::SEALED) != 0,
        }
    }

    pub fn circuit_decl(&self, node: NodeIndex) -> CircuitDecl {
        debug_assert_eq!(self.node_tag(node), NodeTag::CircuitDecl);
        let data = self.node_data(node);
        let base = data.lhs as usize;
        CircuitDecl {
            circuit_token: self.node_main_token(node),
            name_token: TokenIndex(self.extra_data[base]),
            params_start: self.extra_data[base + 1],
            params_end: self.extra_data[base + 2],
            ret_type: NodeIndex(self.extra_data[base + 3]),
            body: NodeIndex(self.extra_data[base + 4]),
            exported: (data.rhs & decl_flags::EXPORT) != 0,
            pure: (data.rhs & decl_flags::PURE) != 0,
        }
    }

    pub fn param(&self, node: NodeIndex) -> Param {
        debug_assert_eq!(self.node_tag(node), NodeTag::Param);
        let data = self.node_data(node);
        Param {
            name_token: self.node_main_token(node),
            type_node: NodeIndex(data.lhs),
        }
    }

    pub fn call_expr(&self, node: NodeIndex) -> CallExpr {
        debug_assert_eq!(self.node_tag(node), NodeTag::CallExpr);
        let data = self.node_data(node);
        let base = data.lhs as usize;
        CallExpr {
            lparen_token: self.node_main_token(node),
            rparen_token: TokenIndex(data.rhs),
            callee: NodeIndex(self.extra_data[base]),
            args_start: self.extra_data[base + 1],
            args_end: self.extra_data[base + 2],
        }
    }

    /// Compute a conservative source span covering an AST node.
    pub fn node_span(&self, node: NodeIndex) -> Span {
        let tag = self.node_tag(node);
        let main = self.token_span(self.node_main_token(node));
        let data = self.node_data(node);
        match tag {
            NodeTag::Root => {
                let mut iter = self.root_decls();
                let Some(first) = iter.next() else {
                    return Span::EMPTY;
                };
                let last = iter.last().unwrap_or(first);
                self.node_span(first).merge(self.node_span(last))
            }
            NodeTag::ImportDecl => main.merge(self.token_span(TokenIndex(data.lhs))),
            NodeTag::LedgerDecl => {
                let decl = self.ledger_decl(node);
                main.merge(self.node_span(decl.type_node))
            }
            NodeTag::CircuitDecl => {
                let decl = self.circuit_decl(node);
                main.merge(self.node_span(decl.body))
            }
            NodeTag::Param => main.merge(self.node_span(NodeIndex(data.lhs))),
            NodeTag::TypeNamed | NodeTag::IdentExpr | NodeTag::IntLitExpr => main,
            NodeTag::TypeTuple | NodeTag::TupleExpr | NodeTag::Block => {
                let mut span = main;
                if let Some(last) = self.extra_nodes(data.lhs, data.rhs).last() {
                    span = span.merge(self.node_span(last));
                }
                span
            }
            NodeTag::ExprStmt => self
                .node_span(NodeIndex(data.lhs))
                .merge(self.token_span(TokenIndex(data.rhs))),
            NodeTag::ReturnStmt => {
                let mut span = main;
                if let Some(expr) = NodeIndex(data.lhs).into_option() {
                    span = span.merge(self.node_span(expr));
                }
                span.merge(self.token_span(TokenIndex(data.rhs)))
            }
            NodeTag::MemberExpr => self
                .node_span(NodeIndex(data.lhs))
                .merge(self.token_span(TokenIndex(data.rhs))),
            NodeTag::CallExpr => {
                let call = self.call_expr(node);
                self.node_span(call.callee)
                    .merge(self.token_span(call.rparen_token))
            }
            NodeTag::BinaryExpr => self
                .node_span(NodeIndex(data.lhs))
                .merge(self.node_span(NodeIndex(data.rhs))),
        }
    }

    /// Render a deterministic, human-readable AST tree dump (useful for snapshot tests).
    pub fn dump(&self, source: &str) -> String {
        let mut out = String::new();
        self.dump_node(NodeIndex::ROOT, source, 0, &mut out);
        out
    }

    fn dump_node(&self, node: NodeIndex, source: &str, indent: usize, out: &mut String) {
        let pad = "  ".repeat(indent);
        let tag = self.node_tag(node);
        let data = self.node_data(node);
        match tag {
            NodeTag::Root => {
                writeln!(out, "{pad}Program").unwrap();
                for child in self.root_decls() {
                    self.dump_node(child, source, indent + 1, out);
                }
            }
            NodeTag::ImportDecl => {
                let decl = self.import_decl(node);
                writeln!(
                    out,
                    "{pad}ImportDecl {}",
                    self.token_text(decl.name_token, source)
                )
                .unwrap();
            }
            NodeTag::LedgerDecl => {
                let decl = self.ledger_decl(node);
                let mut mods = Vec::new();
                if decl.exported {
                    mods.push("export");
                }
                if decl.sealed {
                    mods.push("sealed");
                }
                let mods_str = if mods.is_empty() {
                    String::new()
                } else {
                    format!("[{}] ", mods.join(" "))
                };
                writeln!(
                    out,
                    "{pad}LedgerDecl {mods_str}{}",
                    self.token_text(decl.name_token, source)
                )
                .unwrap();
                self.dump_node(decl.type_node, source, indent + 1, out);
            }
            NodeTag::CircuitDecl => {
                let decl = self.circuit_decl(node);
                let mut mods = Vec::new();
                if decl.exported {
                    mods.push("export");
                }
                if decl.pure {
                    mods.push("pure");
                }
                let mods_str = if mods.is_empty() {
                    String::new()
                } else {
                    format!("[{}] ", mods.join(" "))
                };
                writeln!(
                    out,
                    "{pad}CircuitDecl {mods_str}{}",
                    self.token_text(decl.name_token, source)
                )
                .unwrap();
                let params: Vec<_> = self
                    .extra_nodes(decl.params_start, decl.params_end)
                    .collect();
                if !params.is_empty() {
                    writeln!(out, "{pad}  Params").unwrap();
                    for param in params {
                        self.dump_node(param, source, indent + 2, out);
                    }
                }
                writeln!(out, "{pad}  ReturnType").unwrap();
                self.dump_node(decl.ret_type, source, indent + 2, out);
                self.dump_node(decl.body, source, indent + 1, out);
            }
            NodeTag::Param => {
                let param = self.param(node);
                writeln!(
                    out,
                    "{pad}Param {}",
                    self.token_text(param.name_token, source)
                )
                .unwrap();
                self.dump_node(param.type_node, source, indent + 1, out);
            }
            NodeTag::TypeNamed => {
                writeln!(
                    out,
                    "{pad}TypeNamed {}",
                    self.token_text(self.node_main_token(node), source)
                )
                .unwrap();
            }
            NodeTag::TypeTuple => {
                writeln!(out, "{pad}TypeTuple").unwrap();
                for elem in self.extra_nodes(data.lhs, data.rhs) {
                    self.dump_node(elem, source, indent + 1, out);
                }
            }
            NodeTag::Block => {
                writeln!(out, "{pad}Block").unwrap();
                for stmt in self.extra_nodes(data.lhs, data.rhs) {
                    self.dump_node(stmt, source, indent + 1, out);
                }
            }
            NodeTag::ExprStmt => {
                writeln!(out, "{pad}ExprStmt").unwrap();
                self.dump_node(NodeIndex(data.lhs), source, indent + 1, out);
            }
            NodeTag::ReturnStmt => {
                writeln!(out, "{pad}ReturnStmt").unwrap();
                if let Some(expr) = NodeIndex(data.lhs).into_option() {
                    self.dump_node(expr, source, indent + 1, out);
                }
            }
            NodeTag::IdentExpr => {
                writeln!(
                    out,
                    "{pad}IdentExpr {}",
                    self.token_text(self.node_main_token(node), source)
                )
                .unwrap();
            }
            NodeTag::IntLitExpr => {
                writeln!(
                    out,
                    "{pad}IntLitExpr {}",
                    self.token_text(self.node_main_token(node), source)
                )
                .unwrap();
            }
            NodeTag::TupleExpr => {
                writeln!(out, "{pad}TupleExpr").unwrap();
                for elem in self.extra_nodes(data.lhs, data.rhs) {
                    self.dump_node(elem, source, indent + 1, out);
                }
            }
            NodeTag::MemberExpr => {
                writeln!(
                    out,
                    "{pad}MemberExpr .{}",
                    self.token_text(TokenIndex(data.rhs), source)
                )
                .unwrap();
                self.dump_node(NodeIndex(data.lhs), source, indent + 1, out);
            }
            NodeTag::CallExpr => {
                let call = self.call_expr(node);
                writeln!(out, "{pad}CallExpr").unwrap();
                self.dump_node(call.callee, source, indent + 1, out);
                for arg in self.extra_nodes(call.args_start, call.args_end) {
                    self.dump_node(arg, source, indent + 1, out);
                }
            }
            NodeTag::BinaryExpr => {
                writeln!(
                    out,
                    "{pad}BinaryExpr {}",
                    self.token_text(self.node_main_token(node), source)
                )
                .unwrap();
                self.dump_node(NodeIndex(data.lhs), source, indent + 1, out);
                self.dump_node(NodeIndex(data.rhs), source, indent + 1, out);
            }
        }
    }
}
