use compact_ast::{Comment, CommentKind, Token, TokenIndex, TokenTag};
use compact_diagnostics::{CompactDiagnostic, DiagnosticBag};
use compact_span::{SourceFile, Span};
use soa_rs::Soa;

pub struct LexOutput {
    pub tokens: Soa<Token>,
    pub comments: Soa<Comment>,
}

pub fn lex(file: &SourceFile, diagnostics: &mut DiagnosticBag) -> LexOutput {
    let src = file.text();
    let bytes = src.as_bytes();
    let len = bytes.len();
    let mut pos = 0usize;

    let mut tokens: Soa<Token> = Soa::new();
    let mut comments: Soa<Comment> = Soa::new();

    while pos < len {
        let b = bytes[pos];

        // Whitespace
        if b.is_ascii_whitespace() {
            pos += 1;
            continue;
        }

        // Line comment: // ...
        if b == b'/' && pos + 1 < len && bytes[pos + 1] == b'/' {
            let start = pos;
            pos += 2;
            while pos < len && bytes[pos] != b'\n' {
                pos += 1;
            }
            comments.push(Comment {
                kind: CommentKind::Line,
                span: Span::new(start as u32, pos as u32),
                before_token: TokenIndex(tokens.len() as u32),
            });
            continue;
        }

        // Block comment: /* ... */ (Compact forbids nested block comments)
        if b == b'/' && pos + 1 < len && bytes[pos + 1] == b'*' {
            let start = pos;
            pos += 2;
            let mut closed = false;
            while pos + 1 < len {
                if bytes[pos] == b'/' && bytes[pos + 1] == b'*' {
                    diagnostics.push(CompactDiagnostic::error(
                        file,
                        Span::new(pos as u32, (pos + 2) as u32),
                        "attempt to nest block comment",
                    ));
                    pos += 2;
                    continue;
                }
                if bytes[pos] == b'*' && bytes[pos + 1] == b'/' {
                    pos += 2;
                    closed = true;
                    break;
                }
                pos += 1;
            }
            if !closed {
                pos = len;
                diagnostics.push(CompactDiagnostic::error(
                    file,
                    Span::new(start as u32, pos as u32),
                    "unterminated block comment",
                ));
            }
            comments.push(Comment {
                kind: CommentKind::Block,
                span: Span::new(start as u32, pos as u32),
                before_token: TokenIndex(tokens.len() as u32),
            });
            continue;
        }

        let start = pos;

        // Identifier or keyword
        if is_ident_start(b) {
            pos += 1;
            while pos < len && is_ident_continue(bytes[pos]) {
                pos += 1;
            }
            let text = &src[start..pos];
            let tag = keyword_or_ident(text);
            tokens.push(Token {
                tag,
                span: Span::new(start as u32, pos as u32),
            });
            continue;
        }

        // Natural number literal
        if b.is_ascii_digit() {
            pos += 1;
            while pos < len && bytes[pos].is_ascii_digit() {
                pos += 1;
            }
            tokens.push(Token {
                tag: TokenTag::Nat,
                span: Span::new(start as u32, pos as u32),
            });
            continue;
        }

        // String literal ('...' or "...")
        if b == b'"' || b == b'\'' {
            let quote = b;
            pos += 1;
            let mut closed = false;
            while pos < len {
                let c = bytes[pos];
                if c == b'\\' && pos + 1 < len {
                    pos += 2;
                    continue;
                }
                if c == quote {
                    pos += 1;
                    closed = true;
                    break;
                }
                if c == b'\n' {
                    break;
                }
                pos += 1;
            }
            if !closed {
                diagnostics.push(CompactDiagnostic::error(
                    file,
                    Span::new(start as u32, pos as u32),
                    "unterminated string literal",
                ));
            }
            tokens.push(Token {
                tag: TokenTag::String,
                span: Span::new(start as u32, pos as u32),
            });
            continue;
        }

        // Two-character and single-character tokens
        let tag = match b {
            b'(' => {
                pos += 1;
                TokenTag::LParen
            }
            b')' => {
                pos += 1;
                TokenTag::RParen
            }
            b'{' => {
                pos += 1;
                TokenTag::LBrace
            }
            b'}' => {
                pos += 1;
                TokenTag::RBrace
            }
            b'[' => {
                pos += 1;
                TokenTag::LBracket
            }
            b']' => {
                pos += 1;
                TokenTag::RBracket
            }
            b'<' => {
                if pos + 1 < len && bytes[pos + 1] == b'=' {
                    pos += 2;
                    TokenTag::LtEq
                } else {
                    pos += 1;
                    TokenTag::LAngle
                }
            }
            b'>' => {
                if pos + 1 < len && bytes[pos + 1] == b'=' {
                    pos += 2;
                    TokenTag::GtEq
                } else {
                    pos += 1;
                    TokenTag::RAngle
                }
            }
            b':' => {
                pos += 1;
                TokenTag::Colon
            }
            b';' => {
                pos += 1;
                TokenTag::Semi
            }
            b',' => {
                pos += 1;
                TokenTag::Comma
            }
            b'.' => {
                if pos + 2 < len && bytes[pos + 1] == b'.' && bytes[pos + 2] == b'.' {
                    pos += 3;
                    TokenTag::DotDotDot
                } else if pos + 1 < len && bytes[pos + 1] == b'.' {
                    pos += 2;
                    TokenTag::DotDot
                } else {
                    pos += 1;
                    TokenTag::Dot
                }
            }
            b'#' => {
                pos += 1;
                TokenTag::Hash
            }
            b'?' => {
                pos += 1;
                TokenTag::Question
            }
            b'+' => {
                if pos + 1 < len && bytes[pos + 1] == b'=' {
                    pos += 2;
                    TokenTag::PlusEq
                } else {
                    pos += 1;
                    TokenTag::Plus
                }
            }
            b'-' => {
                if pos + 1 < len && bytes[pos + 1] == b'=' {
                    pos += 2;
                    TokenTag::MinusEq
                } else {
                    pos += 1;
                    TokenTag::Minus
                }
            }
            b'*' => {
                pos += 1;
                TokenTag::Star
            }
            b'=' => {
                if pos + 1 < len && bytes[pos + 1] == b'=' {
                    pos += 2;
                    TokenTag::EqEq
                } else if pos + 1 < len && bytes[pos + 1] == b'>' {
                    pos += 2;
                    TokenTag::FatArrow
                } else {
                    pos += 1;
                    TokenTag::Eq
                }
            }
            b'!' => {
                if pos + 1 < len && bytes[pos + 1] == b'=' {
                    pos += 2;
                    TokenTag::BangEq
                } else {
                    pos += 1;
                    TokenTag::Bang
                }
            }
            b'&' if pos + 1 < len && bytes[pos + 1] == b'&' => {
                pos += 2;
                TokenTag::AmpAmp
            }
            b'|' if pos + 1 < len && bytes[pos + 1] == b'|' => {
                pos += 2;
                TokenTag::PipePipe
            }
            _ => {
                let ch = src[pos..].chars().next().unwrap();
                pos += ch.len_utf8();
                diagnostics.push(CompactDiagnostic::error(
                    file,
                    Span::new(start as u32, pos as u32),
                    format!("unexpected character '{ch}'"),
                ));
                TokenTag::Invalid
            }
        };

        tokens.push(Token {
            tag,
            span: Span::new(start as u32, pos as u32),
        });
    }

    tokens.push(Token {
        tag: TokenTag::Eof,
        span: Span::new(len as u32, len as u32),
    });

    LexOutput { tokens, comments }
}

#[inline]
fn is_ident_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_' || b == b'$'
}

#[inline]
fn is_ident_continue(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'$'
}

fn keyword_or_ident(text: &str) -> TokenTag {
    match text {
        "import" => TokenTag::Import,
        "export" => TokenTag::Export,
        "include" => TokenTag::Include,
        "from" => TokenTag::From,
        "prefix" => TokenTag::Prefix,
        "type" => TokenTag::Type,
        "new" => TokenTag::New,
        "ledger" => TokenTag::Ledger,
        "sealed" => TokenTag::Sealed,
        "circuit" => TokenTag::Circuit,
        "pure" => TokenTag::Pure,
        "return" => TokenTag::Return,
        "witness" => TokenTag::Witness,
        "pragma" => TokenTag::Pragma,
        "struct" => TokenTag::Struct,
        "enum" => TokenTag::Enum,
        "module" => TokenTag::Module,
        "const" => TokenTag::Const,
        "if" => TokenTag::If,
        "else" => TokenTag::Else,
        "for" => TokenTag::For,
        "assert" => TokenTag::Assert,
        "disclose" => TokenTag::Disclose,
        "true" => TokenTag::True,
        "false" => TokenTag::False,
        "default" => TokenTag::Default,
        "as" => TokenTag::As,
        "contract" => TokenTag::Contract,
        "implements" => TokenTag::Implements,
        "constructor" => TokenTag::Constructor,
        "emit" => TokenTag::Emit,
        _ => TokenTag::Ident,
    }
}
