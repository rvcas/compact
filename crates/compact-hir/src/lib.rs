use std::fmt::Write as _;

use compact_span::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EnumId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StructId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NewTypeId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LedgerFieldId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct WitnessId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CircuitId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ParamId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LocalId(pub u32);

/// Built-in ledger Abstract Data Types from Midnight's ledger specification.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LedgerAdt {
    /// Implicit single-value cell wrapping ordinary Compact types (e.g. `Field`, `Bytes<32>`, enums).
    Cell(Box<Type>),
    Counter,
    Set(Box<Type>),
    List(Box<Type>),
    /// Unbounded map whose values can be plain `Cell` types or nested ledger ADTs.
    Map {
        key: Box<Type>,
        value: Box<LedgerAdt>,
    },
    /// Bounded Merkle tree of depth `nat` (`2 <= nat <= 32`).
    MerkleTree {
        depth: u32,
        value: Box<Type>,
    },
    /// Bounded Merkle tree of depth `nat` (`2 <= nat <= 32`) with historic root set.
    HistoricMerkleTree {
        depth: u32,
        value: Box<Type>,
    },
    /// Special top-level Kernel ADT providing transaction/block/token/effects primitives.
    Kernel,
}

impl LedgerAdt {
    pub fn name(&self) -> &'static str {
        match self {
            Self::Cell(_) => "Cell",
            Self::Counter => "Counter",
            Self::Set(_) => "Set",
            Self::List(_) => "List",
            Self::Map { .. } => "Map",
            Self::MerkleTree { .. } => "MerkleTree",
            Self::HistoricMerkleTree { .. } => "HistoricMerkleTree",
            Self::Kernel => "Kernel",
        }
    }

    pub fn is_cell(&self) -> bool {
        matches!(self, Self::Cell(_))
    }

    pub fn cell_type(&self) -> Option<&Type> {
        match self {
            Self::Cell(ty) => Some(ty),
            _ => None,
        }
    }
}

/// Resolved operations on ledger ADTs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LedgerOp {
    CellRead,
    CellWrite,
    CellResetToDefault,
    CounterIncrement,
    CounterDecrement,
    CounterRead,
    CounterLessThan,
    CounterResetToDefault,
    SetMember,
    SetInsert,
    SetRemove,
    SetIsEmpty,
    SetSize,
    SetResetToDefault,
    MapMember,
    MapLookup,
    MapInsert,
    MapInsertDefault,
    MapRemove,
    MapIsEmpty,
    MapSize,
    MapResetToDefault,
    ListPushFront,
    ListPopFront,
    ListHead,
    ListLength,
    ListIsEmpty,
    ListResetToDefault,
    MerkleTreeInsert,
    MerkleTreeCheckRoot,
    MerkleTreeResetToDefault,
    HistoricMerkleTreeInsert,
    HistoricMerkleTreeCheckRoot,
    HistoricMerkleTreeResetToDefault,
    KernelSelf,
    KernelCaller,
    KernelCheckpoint,
    KernelClaimZswapNullifier,
    KernelClaimZswapCoinSpend,
    KernelClaimZswapCoinReceive,
    KernelClaimContractCall,
    KernelMintShielded,
    KernelMintUnshielded,
    KernelClaimUnshieldedCoinSpend,
    KernelIncUnshieldedOutputs,
    KernelIncUnshieldedInputs,
    KernelBalance,
    KernelBalanceLessThan,
    KernelBalanceGreaterThan,
    KernelBlockTimeLessThan,
    KernelBlockTimeGreaterThan,
}

impl LedgerOp {
    pub fn name(self) -> &'static str {
        match self {
            Self::CellRead | Self::CounterRead => "read",
            Self::CellWrite => "write",
            Self::CounterIncrement => "increment",
            Self::CounterDecrement => "decrement",
            Self::CounterLessThan => "lessThan",
            Self::SetMember | Self::MapMember => "member",
            Self::MapLookup => "lookup",
            Self::SetInsert
            | Self::MapInsert
            | Self::MerkleTreeInsert
            | Self::HistoricMerkleTreeInsert => "insert",
            Self::MapInsertDefault => "insertDefault",
            Self::SetRemove | Self::MapRemove => "remove",
            Self::SetIsEmpty | Self::MapIsEmpty | Self::ListIsEmpty => "isEmpty",
            Self::SetSize | Self::MapSize => "size",
            Self::ListPushFront => "pushFront",
            Self::ListPopFront => "popFront",
            Self::ListHead => "head",
            Self::ListLength => "length",
            Self::MerkleTreeCheckRoot | Self::HistoricMerkleTreeCheckRoot => "checkRoot",
            Self::CellResetToDefault
            | Self::CounterResetToDefault
            | Self::SetResetToDefault
            | Self::MapResetToDefault
            | Self::ListResetToDefault
            | Self::MerkleTreeResetToDefault
            | Self::HistoricMerkleTreeResetToDefault => "resetToDefault",
            Self::KernelSelf => "self",
            Self::KernelCaller => "caller",
            Self::KernelCheckpoint => "checkpoint",
            Self::KernelClaimZswapNullifier => "claimZswapNullifier",
            Self::KernelClaimZswapCoinSpend => "claimZswapCoinSpend",
            Self::KernelClaimZswapCoinReceive => "claimZswapCoinReceive",
            Self::KernelClaimContractCall => "claimContractCall",
            Self::KernelMintShielded => "mintShielded",
            Self::KernelMintUnshielded => "mintUnshielded",
            Self::KernelClaimUnshieldedCoinSpend => "claimUnshieldedCoinSpend",
            Self::KernelIncUnshieldedOutputs => "incUnshieldedOutputs",
            Self::KernelIncUnshieldedInputs => "incUnshieldedInputs",
            Self::KernelBalance => "balance",
            Self::KernelBalanceLessThan => "balanceLessThan",
            Self::KernelBalanceGreaterThan => "balanceGreaterThan",
            Self::KernelBlockTimeLessThan => "blockTimeLessThan",
            Self::KernelBlockTimeGreaterThan => "blockTimeGreaterThan",
        }
    }

    pub fn is_mutating(self) -> bool {
        matches!(
            self,
            Self::CellWrite
                | Self::CellResetToDefault
                | Self::CounterIncrement
                | Self::CounterDecrement
                | Self::CounterResetToDefault
                | Self::SetInsert
                | Self::SetRemove
                | Self::SetResetToDefault
                | Self::MapInsert
                | Self::MapInsertDefault
                | Self::MapRemove
                | Self::MapResetToDefault
                | Self::ListPushFront
                | Self::ListPopFront
                | Self::ListResetToDefault
                | Self::MerkleTreeInsert
                | Self::MerkleTreeResetToDefault
                | Self::HistoricMerkleTreeInsert
                | Self::HistoricMerkleTreeResetToDefault
                | Self::KernelCheckpoint
                | Self::KernelClaimZswapNullifier
                | Self::KernelClaimZswapCoinSpend
                | Self::KernelClaimZswapCoinReceive
                | Self::KernelClaimContractCall
                | Self::KernelMintShielded
                | Self::KernelMintUnshielded
                | Self::KernelClaimUnshieldedCoinSpend
                | Self::KernelIncUnshieldedOutputs
                | Self::KernelIncUnshieldedInputs
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Field,
    Boolean,
    Uint(u32),
    Bytes(u32),
    /// Opaque host type (e.g. `Opaque<"string">`, `Opaque<"Uint8Array">`).
    Opaque(String),
    Vector(u32, Box<Type>),
    Tuple(Vec<Type>),
    Enum(EnumId),
    Struct(StructId),
    /// Nominal user-defined `new type Name = Inner;` distinct during type checking,
    /// with the same wire representation as `Inner`.
    NewType(NewTypeId),
    /// Standard-library `Maybe<T> { is_some: Boolean, value: T }`.
    Maybe(Box<Type>),
    /// Standard-library `Either<A, B> { is_left: Boolean, left: A, right: B }`.
    Either(Box<Type>, Box<Type>),
    /// Standard-library `MerkleTreeDigest { field: Field }`.
    MerkleTreeDigest,
    /// Standard-library `MerkleTreePathEntry { sibling: MerkleTreeDigest, goes_left: Boolean }`.
    MerkleTreePathEntry,
    /// Standard-library `MerkleTreePath<N, T> { leaf: T, path: Vector<N, MerkleTreePathEntry> }`.
    MerkleTreePath(u32, Box<Type>),
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
pub struct StructField {
    pub name: String,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct StructDecl {
    pub id: StructId,
    pub name: String,
    pub fields: Vec<StructField>,
    pub exported: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct NewTypeDecl {
    pub id: NewTypeId,
    pub name: String,
    pub inner: Type,
    pub exported: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct LedgerField {
    pub id: LedgerFieldId,
    pub name: String,
    pub adt: LedgerAdt,
    pub path: Vec<u32>,
    pub exported: bool,
    pub sealed: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct WitnessDecl {
    pub id: WitnessId,
    pub name: String,
    pub params: Vec<Param>,
    pub ret_type: Type,
    pub exported: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Constructor {
    pub params: Vec<Param>,
    pub body: Vec<Stmt>,
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
    Mul,
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NativeWitnessKind {
    OwnPublicKey,
    CreateZswapInput,
    CreateZswapOutput,
}

impl NativeWitnessKind {
    pub fn runtime_name(self) -> &'static str {
        match self {
            Self::OwnPublicKey => "ownPublicKey",
            Self::CreateZswapInput => "createZswapInput",
            Self::CreateZswapOutput => "createZswapOutput",
        }
    }
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    IntLit(u128),
    BoolLit(bool),
    /// Fixed-length byte string literal (e.g. from `pad(32, "lares:tiny:pk:")`).
    BytesLit(Vec<u8>),
    /// Zero/default value of a Compact type (`default<T>`).
    Default(Type),
    /// Default initial state value of a ledger ADT (e.g. `default<Counter>`, `default<Map<Field, Counter>>`).
    DefaultAdt(LedgerAdt),
    ParamRef(ParamId),
    LocalRef(LocalId),
    EnumVariant {
        enum_id: EnumId,
        variant_idx: u32,
    },
    Tuple(Vec<Expr>),
    Vector(Vec<Expr>),
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
    WitnessCall {
        witness: WitnessId,
        args: Vec<Expr>,
    },
    NativeWitness {
        kind: NativeWitnessKind,
        args: Vec<Expr>,
    },
    CircuitCall {
        circuit: CircuitId,
        args: Vec<Expr>,
    },
    LedgerCall {
        field: LedgerFieldId,
        /// Runtime map lookup keys chained before invoking `op` on `target_adt`.
        key_path: Vec<Expr>,
        /// Resolved ADT at `field` followed by `key_path`.
        target_adt: LedgerAdt,
        op: LedgerOp,
        args: Vec<Expr>,
    },
    PersistentHash {
        input_ty: Type,
        arg: Box<Expr>,
    },
    TransientHash {
        input_ty: Type,
        arg: Box<Expr>,
    },
    PersistentCommit {
        input_ty: Type,
        value: Box<Expr>,
        rand: Box<Expr>,
    },
    TransientCommit {
        input_ty: Type,
        value: Box<Expr>,
        rand: Box<Expr>,
    },
    DegradeToTransient(Box<Expr>),
    UpgradeFromTransient(Box<Expr>),
    /// Pack `N` `Uint<8>` byte expressions into a `Bytes<N>` value (`Bytes[b0, b1, ...]`).
    BytesPack(Vec<Expr>),
    /// Scoped block expression evaluating `stmts` in order and yielding `tail`.
    Block {
        stmts: Vec<Stmt>,
        tail: Box<Expr>,
    },
    MerkleTreePathRoot {
        depth: u32,
        leaf_ty: Type,
        path: Box<Expr>,
    },
    MaybeSome(Box<Expr>),
    MaybeNone(Type),
    /// Struct literal (fields stored in declaration order).
    StructLit {
        fields: Vec<(String, Expr)>,
    },
    /// Struct field access (`base.field`).
    FieldAccess {
        base: Box<Expr>,
        field: String,
    },
    /// Tuple or vector indexing (`base[index]`).
    Index {
        base: Box<Expr>,
        index: Box<Expr>,
    },
    /// Fixed-length slice (`slice<len>(base, start)`) over `Vector`, `Tuple`, or `Bytes`.
    Slice {
        base: Box<Expr>,
        start: u32,
        len: u32,
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
    If {
        cond: Expr,
        then_branch: Vec<Stmt>,
        else_branch: Vec<Stmt>,
        span: Span,
    },
    ForRange {
        local: LocalId,
        name: String,
        start: u64,
        end: u64,
        body: Vec<Stmt>,
        span: Span,
    },
    ForEach {
        local: LocalId,
        name: String,
        elem_ty: Type,
        iter: Expr,
        len: u32,
        body: Vec<Stmt>,
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
    /// True when the circuit performs no ledger or witness operations (transitively).
    pub pure: bool,
    /// True when the circuit is exported and requires a ZK proof (touches ledger).
    pub proof: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Program {
    pub enums: Vec<EnumDecl>,
    pub structs: Vec<StructDecl>,
    pub new_types: Vec<NewTypeDecl>,
    pub ledger_fields: Vec<LedgerField>,
    pub witnesses: Vec<WitnessDecl>,
    pub constructor: Option<Constructor>,
    pub circuits: Vec<Circuit>,
    /// Exported stdlib type names (e.g. `Maybe`).
    pub exported_stdlib_types: Vec<String>,
}

impl Program {
    pub fn enum_decl(&self, id: EnumId) -> &EnumDecl {
        &self.enums[id.0 as usize]
    }

    pub fn struct_decl(&self, id: StructId) -> &StructDecl {
        &self.structs[id.0 as usize]
    }

    pub fn new_type_decl(&self, id: NewTypeId) -> &NewTypeDecl {
        &self.new_types[id.0 as usize]
    }

    /// Peel any layers of nominal `new type` wrappers to obtain the representation type.
    pub fn underlying_type<'a>(&'a self, mut ty: &'a Type) -> &'a Type {
        while let Type::NewType(id) = ty {
            ty = &self.new_type_decl(*id).inner;
        }
        ty
    }

    /// Return ordered `(field_name, field_type)` pairs for any user-defined or stdlib struct type.
    pub fn struct_fields_of(&self, ty: &Type) -> Option<Vec<(String, Type)>> {
        match self.underlying_type(ty) {
            Type::Struct(id) => Some(
                self.struct_decl(*id)
                    .fields
                    .iter()
                    .map(|f| (f.name.clone(), f.ty.clone()))
                    .collect(),
            ),
            Type::Maybe(inner) => Some(vec![
                ("is_some".to_owned(), Type::Boolean),
                ("value".to_owned(), (**inner).clone()),
            ]),
            Type::Either(left, right) => Some(vec![
                ("is_left".to_owned(), Type::Boolean),
                ("left".to_owned(), (**left).clone()),
                ("right".to_owned(), (**right).clone()),
            ]),
            Type::MerkleTreeDigest => Some(vec![("field".to_owned(), Type::Field)]),
            Type::MerkleTreePathEntry => Some(vec![
                ("sibling".to_owned(), Type::MerkleTreeDigest),
                ("goes_left".to_owned(), Type::Boolean),
            ]),
            Type::MerkleTreePath(depth, leaf) => Some(vec![
                ("leaf".to_owned(), (**leaf).clone()),
                (
                    "path".to_owned(),
                    Type::Vector(*depth, Box::new(Type::MerkleTreePathEntry)),
                ),
            ]),
            _ => None,
        }
    }

    pub fn ledger_field(&self, id: LedgerFieldId) -> &LedgerField {
        &self.ledger_fields[id.0 as usize]
    }

    pub fn witness(&self, id: WitnessId) -> &WitnessDecl {
        &self.witnesses[id.0 as usize]
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
            Type::Bytes(len) => format!("Bytes<{len}>"),
            Type::Opaque(ts_ty) => format!("Opaque<\"{ts_ty}\">"),
            Type::Vector(len, elem) => format!("Vector<{len}, {}>", self.format_type(elem)),
            Type::Tuple(elems) => {
                let inner: Vec<_> = elems.iter().map(|e| self.format_type(e)).collect();
                format!("[{}]", inner.join(", "))
            }
            Type::Enum(id) => self.enum_decl(*id).name.clone(),
            Type::Struct(id) => self.struct_decl(*id).name.clone(),
            Type::NewType(id) => self.new_type_decl(*id).name.clone(),
            Type::Maybe(inner) => format!("Maybe<{}>", self.format_type(inner)),
            Type::Either(left, right) => format!(
                "Either<{}, {}>",
                self.format_type(left),
                self.format_type(right)
            ),
            Type::MerkleTreeDigest => "MerkleTreeDigest".into(),
            Type::MerkleTreePathEntry => "MerkleTreePathEntry".into(),
            Type::MerkleTreePath(depth, leaf) => {
                format!("MerkleTreePath<{depth}, {}>", self.format_type(leaf))
            }
        }
    }

    pub fn format_adt(&self, adt: &LedgerAdt) -> String {
        match adt {
            LedgerAdt::Cell(ty) => format!("Cell<{}>", self.format_type(ty)),
            LedgerAdt::Counter => "Counter<Uint<64>>".into(),
            LedgerAdt::Set(ty) => format!("Set<{}>", self.format_type(ty)),
            LedgerAdt::List(ty) => format!("List<{}>", self.format_type(ty)),
            LedgerAdt::Map { key, value } => {
                format!("Map<{}, {}>", self.format_type(key), self.format_adt(value))
            }
            LedgerAdt::MerkleTree { depth, value } => {
                format!("MerkleTree<{depth}, {}>", self.format_type(value))
            }
            LedgerAdt::HistoricMerkleTree { depth, value } => {
                format!("HistoricMerkleTree<{depth}, {}>", self.format_type(value))
            }
            LedgerAdt::Kernel => "Kernel".into(),
        }
    }

    pub fn dump(&self) -> String {
        let mut out = String::new();
        writeln!(out, "HirProgram").unwrap();
        for name in &self.exported_stdlib_types {
            writeln!(out, "  ExportStdlibType {name}").unwrap();
        }
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
        for s in &self.structs {
            let fields: Vec<_> = s
                .fields
                .iter()
                .map(|f| format!("{}: {}", f.name, self.format_type(&f.ty)))
                .collect();
            writeln!(
                out,
                "  Struct #{} {}{} {{ {} }}",
                s.id.0,
                if s.exported { "export " } else { "" },
                s.name,
                fields.join(", ")
            )
            .unwrap();
        }
        for nt in &self.new_types {
            writeln!(
                out,
                "  NewType #{} {}{} = {}",
                nt.id.0,
                if nt.exported { "export " } else { "" },
                nt.name,
                self.format_type(&nt.inner)
            )
            .unwrap();
        }
        for field in &self.ledger_fields {
            writeln!(
                out,
                "  LedgerField #{} {}{}{}: {} @ path={:?}",
                field.id.0,
                if field.exported { "export " } else { "" },
                if field.sealed { "sealed " } else { "" },
                field.name,
                self.format_adt(&field.adt),
                field.path
            )
            .unwrap();
        }
        for w in &self.witnesses {
            writeln!(
                out,
                "  Witness #{} {}{} -> {}",
                w.id.0,
                if w.exported { "export " } else { "" },
                w.name,
                self.format_type(&w.ret_type)
            )
            .unwrap();
        }
        if let Some(ctor) = &self.constructor {
            writeln!(out, "  Constructor ({} params)", ctor.params.len()).unwrap();
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
                    Stmt::If {
                        cond,
                        then_branch,
                        else_branch,
                        ..
                    } => writeln!(
                        out,
                        "    If {:?} then ({} stmts) else ({} stmts)",
                        cond.kind,
                        then_branch.len(),
                        else_branch.len()
                    )
                    .unwrap(),
                    Stmt::ForRange {
                        local,
                        name,
                        start,
                        end,
                        body,
                        ..
                    } => writeln!(
                        out,
                        "    ForRange #{} {} in {}..{} ({} stmts)",
                        local.0,
                        name,
                        start,
                        end,
                        body.len()
                    )
                    .unwrap(),
                    Stmt::ForEach {
                        local,
                        name,
                        len,
                        body,
                        ..
                    } => writeln!(
                        out,
                        "    ForEach #{} {} (len={len}, {} stmts)",
                        local.0,
                        name,
                        body.len()
                    )
                    .unwrap(),
                    Stmt::Expr(e) => writeln!(out, "    ExprStmt {:?}", e.kind).unwrap(),
                    Stmt::Return { value, .. } => {
                        writeln!(out, "    Return {:?}", value.as_ref().map(|v| &v.kind)).unwrap()
                    }
                }
            }
        }
        out
    }
}
