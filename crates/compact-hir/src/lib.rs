use std::fmt::Write as _;

use compact_span::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EnumId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LedgerFieldId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CircuitId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ParamId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LocalId(pub u32);

/// Built-in ledger Abstract Data Types from Midnight's ledger specification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LedgerAdt {
    /// Implicit single-value cell wrapping ordinary Compact types (e.g. `Field`, `Boolean`, enums).
    Cell,
    Counter,
}

impl LedgerAdt {
    pub fn name(self) -> &'static str {
        match self {
            Self::Cell => "Cell",
            Self::Counter => "Counter",
        }
    }
}

/// Resolved operations on ledger ADTs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LedgerOp {
    CellRead,
    CellWrite,
    CounterIncrement,
    CounterDecrement,
    CounterRead,
}

impl LedgerOp {
    pub fn name(self) -> &'static str {
        match self {
            Self::CellRead => "read",
            Self::CellWrite => "write",
            Self::CounterIncrement => "increment",
            Self::CounterDecrement => "decrement",
            Self::CounterRead => "read",
        }
    }

    pub fn is_mutating(self) -> bool {
        matches!(
            self,
            Self::CellWrite | Self::CounterIncrement | Self::CounterDecrement
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Field,
    Boolean,
    Uint(u32),
    Tuple(Vec<Type>),
    Enum(EnumId),
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
pub struct EnumDecl {
    pub id: EnumId,
    pub name: String,
    pub variants: Vec<String>,
    pub exported: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct LedgerField {
    pub id: LedgerFieldId,
    pub name: String,
    pub adt: LedgerAdt,
    /// Underlying value type (`Field`/`Enum`/etc. for `Cell`; `Uint(64)` for `Counter`).
    pub value_type: Type,
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
pub enum UnaryOp {
    Not,
    Neg,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
    Eq,
    Neq,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    IntLit(u128),
    BoolLit(bool),
    ParamRef(ParamId),
    LocalRef(LocalId),
    EnumVariant {
        enum_id: EnumId,
        variant_idx: u32,
    },
    Tuple(Vec<Expr>),
    Unary {
        op: UnaryOp,
        operand: Box<Expr>,
    },
    Binary {
        op: BinaryOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Ternary {
        cond: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
    },
    Cast {
        expr: Box<Expr>,
        target: Type,
    },
    Assert {
        cond: Box<Expr>,
        message: String,
    },
    Disclose(Box<Expr>),
    CircuitCall {
        circuit: CircuitId,
        args: Vec<Expr>,
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
    Const {
        local: LocalId,
        name: String,
        ty: Type,
        init: Expr,
        span: Span,
    },
    Expr(Expr),
    Return {
        value: Option<Expr>,
        span: Span,
    },
}

#[derive(Debug, Clone)]
pub struct Circuit {
    pub id: CircuitId,
    pub name: String,
    pub params: Vec<Param>,
    pub ret_type: Type,
    pub body: Vec<Stmt>,
    pub exported: bool,
    /// True when the circuit performs no ledger/emit/witness/cross-contract operations (transitively).
    pub pure: bool,
    /// True when the circuit is exported and requires a ZK proof (i.e. impure).
    pub proof: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Program {
    pub enums: Vec<EnumDecl>,
    pub ledger_fields: Vec<LedgerField>,
    pub circuits: Vec<Circuit>,
}

impl Program {
    pub fn enum_decl(&self, id: EnumId) -> &EnumDecl {
        &self.enums[id.0 as usize]
    }

    pub fn ledger_field(&self, id: LedgerFieldId) -> &LedgerField {
        &self.ledger_fields[id.0 as usize]
    }

    pub fn circuit(&self, id: CircuitId) -> &Circuit {
        &self.circuits[id.0 as usize]
    }

    pub fn proof_circuits(&self) -> impl Iterator<Item = &Circuit> {
        self.circuits.iter().filter(|c| c.proof)
    }

    pub fn format_type(&self, ty: &Type) -> String {
        match ty {
            Type::Field => "Field".into(),
            Type::Boolean => "Boolean".into(),
            Type::Uint(bits) => format!("Uint<{bits}>"),
            Type::Tuple(elems) => {
                let inner: Vec<_> = elems.iter().map(|e| self.format_type(e)).collect();
                format!("[{}]", inner.join(", "))
            }
            Type::Enum(id) => self.enum_decl(*id).name.clone(),
        }
    }

    pub fn dump(&self) -> String {
        let mut out = String::new();
        writeln!(out, "HirProgram").unwrap();
        for e in &self.enums {
            writeln!(
                out,
                "  Enum #{} {}{} {{ {} }}",
                e.id.0,
                if e.exported { "export " } else { "" },
                e.name,
                e.variants.join(", ")
            )
            .unwrap();
        }
        for field in &self.ledger_fields {
            writeln!(
                out,
                "  LedgerField #{} {}{}{}: {}<{}> @ path={:?}",
                field.id.0,
                if field.exported { "export " } else { "" },
                if field.sealed { "sealed " } else { "" },
                field.name,
                field.adt.name(),
                self.format_type(&field.value_type),
                field.path
            )
            .unwrap();
        }
        for circuit in &self.circuits {
            writeln!(
                out,
                "  Circuit #{} {} (exported={}, pure={}, proof={}) -> {}",
                circuit.id.0,
                circuit.name,
                circuit.exported,
                circuit.pure,
                circuit.proof,
                self.format_type(&circuit.ret_type)
            )
            .unwrap();
            for p in &circuit.params {
                writeln!(
                    out,
                    "    Param #{} {}: {}",
                    p.id.0,
                    p.name,
                    self.format_type(&p.ty)
                )
                .unwrap();
            }
            for stmt in &circuit.body {
                match stmt {
                    Stmt::Const {
                        local,
                        name,
                        ty,
                        init,
                        ..
                    } => writeln!(
                        out,
                        "    Const #{} {}: {} = {:?}",
                        local.0,
                        name,
                        self.format_type(ty),
                        init.kind
                    )
                    .unwrap(),
                    Stmt::Expr(e) => writeln!(out, "    ExprStmt {:?}", e.kind).unwrap(),
                    Stmt::Return { value, .. } => writeln!(
                        out,
                        "    Return {:?}",
                        value.as_ref().map(|v| &v.kind)
                    )
                    .unwrap(),
                }
            }
        }
        out
    }
}
