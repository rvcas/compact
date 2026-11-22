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
    Question,
    Plus,
    Minus,
    Star,
    Eq,
    EqEq,
    BangEq,
    Bang,
    AmpAmp,
    PipePipe,

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
            Self::Question => "?",
            Self::Plus => "+",
            Self::Minus => "-",
            Self::Star => "*",
            Self::Eq => "=",
            Self::EqEq => "==",
            Self::BangEq => "!=",
            Self::Bang => "!",
            Self::AmpAmp => "&&",
            Self::PipePipe => "||",
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
    /// `export { <name>, ... }[;]` — `main_token = export`, `data = (names_start, names_end)`.
    ExportListDecl,
    /// `[export] enum <name> { <variant>, ... }`
    /// `main_token = enum`, `data = (extra_start, flags)`,
    /// `extra_data[extra_start..+3] = [name_tok, variants_start, variants_end]`.
    EnumDecl,
    /// `[export] struct <name> { <field>: <type>; ... }`
    /// `main_token = struct`, `data = (extra_start, flags)`,
    /// `extra_data[extra_start..+3] = [name_tok, fields_start, fields_end]`.
    StructDecl,
    /// `<name>: <type>` inside a struct declaration — `main_token = name_tok`, `data = (type_node, 0)`.
    StructField,
    /// `[export] [sealed] ledger <name>: <type>;`
    /// `main_token = ledger`, `data = (extra_start, flags)`,
    /// `extra_data[extra_start..+2] = [name_tok, type_node]`.
    LedgerDecl,
    /// `[export] witness <name>(<params>): <ret_type>;`
    /// `main_token = witness`, `data = (extra_start, flags)`,
    /// `extra_data[extra_start..+4] = [name_tok, params_start, params_end, ret_type_node]`.
    WitnessDecl,
    /// `constructor(<params>) <block>`
    /// `main_token = constructor`, `data = (extra_start, 0)`,
    /// `extra_data[extra_start..+3] = [params_start, params_end, body_node]`.
    ConstructorDecl,
    /// `[export] [pure] circuit <name>(<params>): <ret_type> <block>`
    /// `main_token = circuit`, `data = (extra_start, flags)`,
    /// `extra_data[extra_start..+5] = [name_tok, params_start, params_end, ret_type_node, body_node]`.
    CircuitDecl,
    /// `<name>: <type>` — `main_token = name_tok`, `data = (type_node, 0)`.
    Param,
    /// Named type reference (e.g. `Counter`, `Field`) — `main_token = name_tok`.
    TypeNamed,
    /// Parameterized type (e.g. `Bytes<32>`, `Vector<2, Bytes<32>>`, `Maybe<Field>`)
    /// `main_token = name_tok`, `data = (args_start, args_end)`.
    TypeGeneric,
    /// Numeric type argument (e.g. `32` in `Bytes<32>`) — `main_token = nat_tok`.
    TypeNat,
    /// String type argument (e.g. `"string"` in `Opaque<"string">`) — `main_token = string_tok`.
    TypeString,
    /// Tuple type (e.g. `[]`, `[Field, Boolean]`) — `main_token = '['`, `data = (extra_start, extra_end)`.
    TypeTuple,
    /// Block `{ <stmt>* }` — `main_token = '{'`, `data = (extra_start, extra_end)`.
    Block,
    /// `if (<cond>) <then_block> [else <else_block_or_if>]`
    /// `main_token = if`, `data = (extra_start, 0)`,
    /// `extra_data[extra_start..+3] = [cond_expr, then_node, opt_else_node]`.
    IfStmt,
    /// `const <name>[: <type>] = <expr>;`
    /// `main_token = const`, `data = (extra_start, semi_tok)`,
    /// `extra_data[extra_start..+3] = [name_tok, opt_type_node, init_expr]`.
    ConstStmt,
    /// `<lhs> = <rhs>;` — `main_token = '='`, `data = (extra_start, semi_tok)`,
    /// `extra_data[extra_start..+2] = [lhs_node, rhs_node]`.
    AssignStmt,
    /// Expression statement `<expr>;` — `data = (expr_node, semi_tok)`.
    ExprStmt,
    /// `return [<expr>];` — `main_token = return`, `data = (opt_expr_node, semi_tok)`.
    ReturnStmt,
    /// Identifier expression — `main_token = ident_tok`.
    IdentExpr,
    /// Integer literal expression — `main_token = nat_tok`.
    IntLitExpr,
    /// Boolean literal expression (`true` / `false`) — `main_token = bool_tok`.
    BoolLitExpr,
    /// String literal expression — `main_token = string_tok`.
    StringLitExpr,
    /// Tuple / vector literal expression `[<expr>, ...]` — `main_token = '['`, `data = (extra_start, extra_end)`.
    TupleExpr,
    /// Member access `<lhs>.<field>` — `main_token = '.'`, `data = (lhs_node, field_tok)`.
    MemberExpr,
    /// Call expression `<callee>(<args>)`
    /// `main_token = '('`, `data = (extra_start, rparen_tok)`,
    /// `extra_data[extra_start..+3] = [callee_node, args_start, args_end]`.
    CallExpr,
    /// Generic call expression `<callee><targs>(<args>)`
    /// `main_token = '('`, `data = (extra_start, rparen_tok)`,
    /// `extra_data[extra_start..+5] = [callee_node, targs_start, targs_end, args_start, args_end]`.
    GenericCallExpr,
    /// Unary expression `<op><expr>` — `main_token = op_tok`, `data = (operand_node, 0)`.
    UnaryExpr,
    /// Binary expression `<lhs> <op> <rhs>` — `main_token = op_tok`, `data = (lhs_node, rhs_node)`.
    BinaryExpr,
    /// Ternary expression `<cond> ? <then> : <else>`
    /// `main_token = '?'`, `data = (extra_start, 0)`,
    /// `extra_data[extra_start..+3] = [cond_node, then_node, else_node]`.
    TernaryExpr,
    /// Cast expression `<expr> as <type>` — `main_token = as`, `data = (expr_node, type_node)`.
    CastExpr,
    /// `default<T>` — `main_token = default`, `data = (type_node, rangle_tok)`.
    DefaultExpr,
    /// `assert(<cond>, <msg>)` — `main_token = assert`, `data = (extra_start, rparen_tok)`,
    /// `extra_data[extra_start..+2] = [cond_node, msg_node]`.
    AssertExpr,
    /// `disclose(<expr>)` — `main_token = disclose`, `data = (expr_node, rparen_tok)`.
    DiscloseExpr,
    /// Struct literal `<Type> { <field>: <expr>, ... }`
    /// `main_token = '{'`, `data = (extra_start, rbrace_tok)`,
    /// `extra_data[extra_start..+3] = [type_node, fields_start, fields_end]`.
    StructLitExpr,
    /// Struct literal field `<name>: <expr>` — `main_token = name_tok`, `data = (value_expr, 0)`.
    StructLitField,
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
pub struct ExportListDecl {
    pub export_token: TokenIndex,
    pub names_start: u32,
    pub names_end: u32,
}

#[derive(Debug, Clone, Copy)]
pub struct EnumDecl {
    pub enum_token: TokenIndex,
    pub name_token: TokenIndex,
    pub variants_start: u32,
    pub variants_end: u32,
    pub exported: bool,
}

#[derive(Debug, Clone, Copy)]
pub struct StructDecl {
    pub struct_token: TokenIndex,
    pub name_token: TokenIndex,
    pub fields_start: u32,
    pub fields_end: u32,
    pub exported: bool,
}

#[derive(Debug, Clone, Copy)]
pub struct StructField {
    pub name_token: TokenIndex,
    pub type_node: NodeIndex,
}

#[derive(Debug, Clone, Copy)]
pub struct IfStmt {
    pub if_token: TokenIndex,
    pub cond: NodeIndex,
    pub then_branch: NodeIndex,
    pub else_branch: Option<NodeIndex>,
}

#[derive(Debug, Clone, Copy)]
pub struct StructLitExpr {
    pub lbrace_token: TokenIndex,
    pub rbrace_token: TokenIndex,
    pub type_node: NodeIndex,
    pub fields_start: u32,
    pub fields_end: u32,
}

#[derive(Debug, Clone, Copy)]
pub struct StructLitField {
    pub name_token: TokenIndex,
    pub value: NodeIndex,
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
pub struct WitnessDecl {
    pub witness_token: TokenIndex,
    pub name_token: TokenIndex,
    pub params_start: u32,
    pub params_end: u32,
    pub ret_type: NodeIndex,
    pub exported: bool,
}

#[derive(Debug, Clone, Copy)]
pub struct ConstructorDecl {
    pub constructor_token: TokenIndex,
    pub params_start: u32,
    pub params_end: u32,
    pub body: NodeIndex,
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
pub struct ConstStmt {
    pub const_token: TokenIndex,
    pub name_token: TokenIndex,
    pub ty: Option<NodeIndex>,
    pub init: NodeIndex,
    pub semi_token: TokenIndex,
}

#[derive(Debug, Clone, Copy)]
pub struct AssignStmt {
    pub eq_token: TokenIndex,
    pub lhs: NodeIndex,
    pub rhs: NodeIndex,
    pub semi_token: TokenIndex,
}

#[derive(Debug, Clone, Copy)]
pub struct CallExpr {
    pub lparen_token: TokenIndex,
    pub rparen_token: TokenIndex,
    pub callee: NodeIndex,
    pub args_start: u32,
    pub args_end: u32,
}

#[derive(Debug, Clone, Copy)]
pub struct GenericCallExpr {
    pub lparen_token: TokenIndex,
    pub rparen_token: TokenIndex,
    pub callee: NodeIndex,
    pub targs_start: u32,
    pub targs_end: u32,
    pub args_start: u32,
    pub args_end: u32,
}

#[derive(Debug, Clone, Copy)]
pub struct TernaryExpr {
    pub question_token: TokenIndex,
    pub cond: NodeIndex,
    pub then_branch: NodeIndex,
    pub else_branch: NodeIndex,
}

#[derive(Debug, Clone, Copy)]
pub struct AssertExpr {
    pub assert_token: TokenIndex,
    pub cond: NodeIndex,
    pub msg: NodeIndex,
    pub rparen_token: TokenIndex,
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

    pub fn extra_tokens(&self, start: u32, end: u32) -> impl Iterator<Item = TokenIndex> + '_ {
        self.extra_data[start as usize..end as usize]
            .iter()
            .copied()
            .map(TokenIndex)
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

    pub fn export_list_decl(&self, node: NodeIndex) -> ExportListDecl {
        debug_assert_eq!(self.node_tag(node), NodeTag::ExportListDecl);
        let data = self.node_data(node);
        ExportListDecl {
            export_token: self.node_main_token(node),
            names_start: data.lhs,
            names_end: data.rhs,
        }
    }

    pub fn enum_decl(&self, node: NodeIndex) -> EnumDecl {
        debug_assert_eq!(self.node_tag(node), NodeTag::EnumDecl);
        let data = self.node_data(node);
        let base = data.lhs as usize;
        EnumDecl {
            enum_token: self.node_main_token(node),
            name_token: TokenIndex(self.extra_data[base]),
            variants_start: self.extra_data[base + 1],
            variants_end: self.extra_data[base + 2],
            exported: (data.rhs & decl_flags::EXPORT) != 0,
        }
    }

    pub fn struct_decl(&self, node: NodeIndex) -> StructDecl {
        debug_assert_eq!(self.node_tag(node), NodeTag::StructDecl);
        let data = self.node_data(node);
        let base = data.lhs as usize;
        StructDecl {
            struct_token: self.node_main_token(node),
            name_token: TokenIndex(self.extra_data[base]),
            fields_start: self.extra_data[base + 1],
            fields_end: self.extra_data[base + 2],
            exported: (data.rhs & decl_flags::EXPORT) != 0,
        }
    }

    pub fn struct_field(&self, node: NodeIndex) -> StructField {
        debug_assert_eq!(self.node_tag(node), NodeTag::StructField);
        let data = self.node_data(node);
        StructField {
            name_token: self.node_main_token(node),
            type_node: NodeIndex(data.lhs),
        }
    }

    pub fn if_stmt(&self, node: NodeIndex) -> IfStmt {
        debug_assert_eq!(self.node_tag(node), NodeTag::IfStmt);
        let data = self.node_data(node);
        let base = data.lhs as usize;
        IfStmt {
            if_token: self.node_main_token(node),
            cond: NodeIndex(self.extra_data[base]),
            then_branch: NodeIndex(self.extra_data[base + 1]),
            else_branch: NodeIndex(self.extra_data[base + 2]).into_option(),
        }
    }

    pub fn struct_lit_expr(&self, node: NodeIndex) -> StructLitExpr {
        debug_assert_eq!(self.node_tag(node), NodeTag::StructLitExpr);
        let data = self.node_data(node);
        let base = data.lhs as usize;
        StructLitExpr {
            lbrace_token: self.node_main_token(node),
            rbrace_token: TokenIndex(data.rhs),
            type_node: NodeIndex(self.extra_data[base]),
            fields_start: self.extra_data[base + 1],
            fields_end: self.extra_data[base + 2],
        }
    }

    pub fn struct_lit_field(&self, node: NodeIndex) -> StructLitField {
        debug_assert_eq!(self.node_tag(node), NodeTag::StructLitField);
        let data = self.node_data(node);
        StructLitField {
            name_token: self.node_main_token(node),
            value: NodeIndex(data.lhs),
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

    pub fn witness_decl(&self, node: NodeIndex) -> WitnessDecl {
        debug_assert_eq!(self.node_tag(node), NodeTag::WitnessDecl);
        let data = self.node_data(node);
        let base = data.lhs as usize;
        WitnessDecl {
            witness_token: self.node_main_token(node),
            name_token: TokenIndex(self.extra_data[base]),
            params_start: self.extra_data[base + 1],
            params_end: self.extra_data[base + 2],
            ret_type: NodeIndex(self.extra_data[base + 3]),
            exported: (data.rhs & decl_flags::EXPORT) != 0,
        }
    }

    pub fn constructor_decl(&self, node: NodeIndex) -> ConstructorDecl {
        debug_assert_eq!(self.node_tag(node), NodeTag::ConstructorDecl);
        let data = self.node_data(node);
        let base = data.lhs as usize;
        ConstructorDecl {
            constructor_token: self.node_main_token(node),
            params_start: self.extra_data[base],
            params_end: self.extra_data[base + 1],
            body: NodeIndex(self.extra_data[base + 2]),
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

    pub fn const_stmt(&self, node: NodeIndex) -> ConstStmt {
        debug_assert_eq!(self.node_tag(node), NodeTag::ConstStmt);
        let data = self.node_data(node);
        let base = data.lhs as usize;
        ConstStmt {
            const_token: self.node_main_token(node),
            name_token: TokenIndex(self.extra_data[base]),
            ty: NodeIndex(self.extra_data[base + 1]).into_option(),
            init: NodeIndex(self.extra_data[base + 2]),
            semi_token: TokenIndex(data.rhs),
        }
    }

    pub fn assign_stmt(&self, node: NodeIndex) -> AssignStmt {
        debug_assert_eq!(self.node_tag(node), NodeTag::AssignStmt);
        let data = self.node_data(node);
        let base = data.lhs as usize;
        AssignStmt {
            eq_token: self.node_main_token(node),
            lhs: NodeIndex(self.extra_data[base]),
            rhs: NodeIndex(self.extra_data[base + 1]),
            semi_token: TokenIndex(data.rhs),
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

    pub fn generic_call_expr(&self, node: NodeIndex) -> GenericCallExpr {
        debug_assert_eq!(self.node_tag(node), NodeTag::GenericCallExpr);
        let data = self.node_data(node);
        let base = data.lhs as usize;
        GenericCallExpr {
            lparen_token: self.node_main_token(node),
            rparen_token: TokenIndex(data.rhs),
            callee: NodeIndex(self.extra_data[base]),
            targs_start: self.extra_data[base + 1],
            targs_end: self.extra_data[base + 2],
            args_start: self.extra_data[base + 3],
            args_end: self.extra_data[base + 4],
        }
    }

    pub fn ternary_expr(&self, node: NodeIndex) -> TernaryExpr {
        debug_assert_eq!(self.node_tag(node), NodeTag::TernaryExpr);
        let data = self.node_data(node);
        let base = data.lhs as usize;
        TernaryExpr {
            question_token: self.node_main_token(node),
            cond: NodeIndex(self.extra_data[base]),
            then_branch: NodeIndex(self.extra_data[base + 1]),
            else_branch: NodeIndex(self.extra_data[base + 2]),
        }
    }

    pub fn assert_expr(&self, node: NodeIndex) -> AssertExpr {
        debug_assert_eq!(self.node_tag(node), NodeTag::AssertExpr);
        let data = self.node_data(node);
        let base = data.lhs as usize;
        AssertExpr {
            assert_token: self.node_main_token(node),
            cond: NodeIndex(self.extra_data[base]),
            msg: NodeIndex(self.extra_data[base + 1]),
            rparen_token: TokenIndex(data.rhs),
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
            NodeTag::ExportListDecl => {
                let mut span = main;
                if let Some(last) = self.extra_tokens(data.lhs, data.rhs).last() {
                    span = span.merge(self.token_span(last));
                }
                span
            }
            NodeTag::EnumDecl => {
                let decl = self.enum_decl(node);
                let mut span = main.merge(self.token_span(decl.name_token));
                if let Some(last) = self
                    .extra_tokens(decl.variants_start, decl.variants_end)
                    .last()
                {
                    span = span.merge(self.token_span(last));
                }
                span
            }
            NodeTag::StructDecl => {
                let decl = self.struct_decl(node);
                let mut span = main.merge(self.token_span(decl.name_token));
                if let Some(last) = self.extra_nodes(decl.fields_start, decl.fields_end).last() {
                    span = span.merge(self.node_span(last));
                }
                span
            }
            NodeTag::StructField | NodeTag::Param | NodeTag::StructLitField => {
                main.merge(self.node_span(NodeIndex(data.lhs)))
            }
            NodeTag::LedgerDecl => {
                let decl = self.ledger_decl(node);
                main.merge(self.node_span(decl.type_node))
            }
            NodeTag::WitnessDecl => {
                let decl = self.witness_decl(node);
                main.merge(self.node_span(decl.ret_type))
            }
            NodeTag::ConstructorDecl => {
                let decl = self.constructor_decl(node);
                main.merge(self.node_span(decl.body))
            }
            NodeTag::CircuitDecl => {
                let decl = self.circuit_decl(node);
                main.merge(self.node_span(decl.body))
            }
            NodeTag::TypeNamed
            | NodeTag::TypeNat
            | NodeTag::TypeString
            | NodeTag::IdentExpr
            | NodeTag::IntLitExpr
            | NodeTag::BoolLitExpr
            | NodeTag::StringLitExpr => main,
            NodeTag::TypeGeneric | NodeTag::TypeTuple | NodeTag::TupleExpr | NodeTag::Block => {
                let mut span = main;
                if let Some(last) = self.extra_nodes(data.lhs, data.rhs).last() {
                    span = span.merge(self.node_span(last));
                }
                span
            }
            NodeTag::IfStmt => {
                let stmt = self.if_stmt(node);
                let end = stmt.else_branch.unwrap_or(stmt.then_branch);
                main.merge(self.node_span(end))
            }
            NodeTag::ConstStmt => {
                let stmt = self.const_stmt(node);
                main.merge(self.token_span(stmt.semi_token))
            }
            NodeTag::AssignStmt => {
                let stmt = self.assign_stmt(node);
                self.node_span(stmt.lhs)
                    .merge(self.token_span(stmt.semi_token))
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
            NodeTag::GenericCallExpr => {
                let call = self.generic_call_expr(node);
                self.node_span(call.callee)
                    .merge(self.token_span(call.rparen_token))
            }
            NodeTag::UnaryExpr => main.merge(self.node_span(NodeIndex(data.lhs))),
            NodeTag::BinaryExpr => self
                .node_span(NodeIndex(data.lhs))
                .merge(self.node_span(NodeIndex(data.rhs))),
            NodeTag::TernaryExpr => {
                let t = self.ternary_expr(node);
                self.node_span(t.cond).merge(self.node_span(t.else_branch))
            }
            NodeTag::CastExpr => self
                .node_span(NodeIndex(data.lhs))
                .merge(self.node_span(NodeIndex(data.rhs))),
            NodeTag::DefaultExpr => main.merge(self.token_span(TokenIndex(data.rhs))),
            NodeTag::AssertExpr => {
                let a = self.assert_expr(node);
                main.merge(self.token_span(a.rparen_token))
            }
            NodeTag::DiscloseExpr => main.merge(self.token_span(TokenIndex(data.rhs))),
            NodeTag::StructLitExpr => {
                let lit = self.struct_lit_expr(node);
                self.node_span(lit.type_node)
                    .merge(self.token_span(lit.rbrace_token))
            }
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
            NodeTag::ExportListDecl => {
                let decl = self.export_list_decl(node);
                let names: Vec<_> = self
                    .extra_tokens(decl.names_start, decl.names_end)
                    .map(|t| self.token_text(t, source))
                    .collect();
                writeln!(out, "{pad}ExportList {{ {} }}", names.join(", ")).unwrap();
            }
            NodeTag::EnumDecl => {
                let decl = self.enum_decl(node);
                let mods_str = if decl.exported { "[export] " } else { "" };
                let variants: Vec<_> = self
                    .extra_tokens(decl.variants_start, decl.variants_end)
                    .map(|t| self.token_text(t, source))
                    .collect();
                writeln!(
                    out,
                    "{pad}EnumDecl {mods_str}{} {{ {} }}",
                    self.token_text(decl.name_token, source),
                    variants.join(", ")
                )
                .unwrap();
            }
            NodeTag::StructDecl => {
                let decl = self.struct_decl(node);
                let mods_str = if decl.exported { "[export] " } else { "" };
                writeln!(
                    out,
                    "{pad}StructDecl {mods_str}{}",
                    self.token_text(decl.name_token, source)
                )
                .unwrap();
                for field in self.extra_nodes(decl.fields_start, decl.fields_end) {
                    self.dump_node(field, source, indent + 1, out);
                }
            }
            NodeTag::StructField => {
                let field = self.struct_field(node);
                writeln!(
                    out,
                    "{pad}StructField {}",
                    self.token_text(field.name_token, source)
                )
                .unwrap();
                self.dump_node(field.type_node, source, indent + 1, out);
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
            NodeTag::WitnessDecl => {
                let decl = self.witness_decl(node);
                let mods_str = if decl.exported { "[export] " } else { "" };
                writeln!(
                    out,
                    "{pad}WitnessDecl {mods_str}{}",
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
            }
            NodeTag::ConstructorDecl => {
                let decl = self.constructor_decl(node);
                writeln!(out, "{pad}ConstructorDecl").unwrap();
                let params: Vec<_> = self
                    .extra_nodes(decl.params_start, decl.params_end)
                    .collect();
                if !params.is_empty() {
                    writeln!(out, "{pad}  Params").unwrap();
                    for param in params {
                        self.dump_node(param, source, indent + 2, out);
                    }
                }
                self.dump_node(decl.body, source, indent + 1, out);
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
            NodeTag::TypeGeneric => {
                writeln!(
                    out,
                    "{pad}TypeGeneric {}",
                    self.token_text(self.node_main_token(node), source)
                )
                .unwrap();
                for arg in self.extra_nodes(data.lhs, data.rhs) {
                    self.dump_node(arg, source, indent + 1, out);
                }
            }
            NodeTag::TypeNat => {
                writeln!(
                    out,
                    "{pad}TypeNat {}",
                    self.token_text(self.node_main_token(node), source)
                )
                .unwrap();
            }
            NodeTag::TypeString => {
                writeln!(
                    out,
                    "{pad}TypeString {}",
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
            NodeTag::IfStmt => {
                let stmt = self.if_stmt(node);
                writeln!(out, "{pad}IfStmt").unwrap();
                self.dump_node(stmt.cond, source, indent + 1, out);
                self.dump_node(stmt.then_branch, source, indent + 1, out);
                if let Some(else_branch) = stmt.else_branch {
                    self.dump_node(else_branch, source, indent + 1, out);
                }
            }
            NodeTag::ConstStmt => {
                let stmt = self.const_stmt(node);
                writeln!(
                    out,
                    "{pad}ConstStmt {}",
                    self.token_text(stmt.name_token, source)
                )
                .unwrap();
                if let Some(ty) = stmt.ty {
                    self.dump_node(ty, source, indent + 1, out);
                }
                self.dump_node(stmt.init, source, indent + 1, out);
            }
            NodeTag::AssignStmt => {
                let stmt = self.assign_stmt(node);
                writeln!(out, "{pad}AssignStmt").unwrap();
                self.dump_node(stmt.lhs, source, indent + 1, out);
                self.dump_node(stmt.rhs, source, indent + 1, out);
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
            NodeTag::BoolLitExpr => {
                writeln!(
                    out,
                    "{pad}BoolLitExpr {}",
                    self.token_text(self.node_main_token(node), source)
                )
                .unwrap();
            }
            NodeTag::StringLitExpr => {
                writeln!(
                    out,
                    "{pad}StringLitExpr {}",
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
            NodeTag::GenericCallExpr => {
                let call = self.generic_call_expr(node);
                writeln!(out, "{pad}GenericCallExpr").unwrap();
                self.dump_node(call.callee, source, indent + 1, out);
                writeln!(out, "{pad}  TypeArgs").unwrap();
                for targ in self.extra_nodes(call.targs_start, call.targs_end) {
                    self.dump_node(targ, source, indent + 2, out);
                }
                for arg in self.extra_nodes(call.args_start, call.args_end) {
                    self.dump_node(arg, source, indent + 1, out);
                }
            }
            NodeTag::UnaryExpr => {
                writeln!(
                    out,
                    "{pad}UnaryExpr {}",
                    self.token_text(self.node_main_token(node), source)
                )
                .unwrap();
                self.dump_node(NodeIndex(data.lhs), source, indent + 1, out);
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
            NodeTag::TernaryExpr => {
                let t = self.ternary_expr(node);
                writeln!(out, "{pad}TernaryExpr").unwrap();
                self.dump_node(t.cond, source, indent + 1, out);
                self.dump_node(t.then_branch, source, indent + 1, out);
                self.dump_node(t.else_branch, source, indent + 1, out);
            }
            NodeTag::CastExpr => {
                writeln!(out, "{pad}CastExpr").unwrap();
                self.dump_node(NodeIndex(data.lhs), source, indent + 1, out);
                self.dump_node(NodeIndex(data.rhs), source, indent + 1, out);
            }
            NodeTag::DefaultExpr => {
                writeln!(out, "{pad}DefaultExpr").unwrap();
                self.dump_node(NodeIndex(data.lhs), source, indent + 1, out);
            }
            NodeTag::AssertExpr => {
                let a = self.assert_expr(node);
                writeln!(out, "{pad}AssertExpr").unwrap();
                self.dump_node(a.cond, source, indent + 1, out);
                self.dump_node(a.msg, source, indent + 1, out);
            }
            NodeTag::DiscloseExpr => {
                writeln!(out, "{pad}DiscloseExpr").unwrap();
                self.dump_node(NodeIndex(data.lhs), source, indent + 1, out);
            }
            NodeTag::StructLitExpr => {
                let lit = self.struct_lit_expr(node);
                writeln!(out, "{pad}StructLitExpr").unwrap();
                self.dump_node(lit.type_node, source, indent + 1, out);
                for field in self.extra_nodes(lit.fields_start, lit.fields_end) {
                    self.dump_node(field, source, indent + 1, out);
                }
            }
            NodeTag::StructLitField => {
                let field = self.struct_lit_field(node);
                writeln!(
                    out,
                    "{pad}StructLitField {}",
                    self.token_text(field.name_token, source)
                )
                .unwrap();
                self.dump_node(field.value, source, indent + 1, out);
            }
        }
    }
}
