pub mod aliases;
mod pragma;
mod stdlib;
mod witness;

use std::collections::{BTreeMap, HashMap, HashSet};

use compact_ast::{Ast, NodeIndex, NodeTag, TokenIndex, TokenTag};
use compact_diagnostics::{CompactDiagnostic, DiagnosticBag};
use compact_hir::{
    BinaryOp, Circuit, CircuitId, Constructor, ContractCircuitSig, ContractDecl, ContractId,
    CurveFieldKind, CurveKind, EnumDecl, EnumId, Expr, ExprKind, LedgerAdt, LedgerField,
    LedgerFieldId, LedgerOp, LocalId, NativeWitnessKind, NewTypeDecl, NewTypeId, Param, ParamId,
    Program, Stmt, StructDecl, StructField, StructId, Type, UnaryOp, WitnessDecl, WitnessId,
};
use compact_span::{SourceFile, Span};

/// Error returned by a [`ModuleLoader`] when resolving `include "..."` or `import "..."`.
#[derive(Debug)]
pub enum LoadError {
    NotFound(String),
    ParseFailed(DiagnosticBag),
}

/// Callback interface used by semantic analysis to load and parse external Compact files
/// referenced by `include "<path>";` or `import "<path>";`.
pub trait ModuleLoader {
    fn load(&self, from_file: &SourceFile, specifier: &str)
    -> Result<(SourceFile, Ast), LoadError>;
}

struct NoopLoader;

impl ModuleLoader for NoopLoader {
    fn load(
        &self,
        _from_file: &SourceFile,
        specifier: &str,
    ) -> Result<(SourceFile, Ast), LoadError> {
        Err(LoadError::NotFound(format!(
            "cannot resolve external file `{specifier}` without a module loader"
        )))
    }
}

pub struct CheckResult {
    pub program: Program,
    pub diagnostics: DiagnosticBag,
}

/// A single source-token renaming discovered during `compact-fixup` analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FixupRename {
    pub span: Span,
    pub old_name: String,
    pub new_name: String,
}

/// Collects deprecated-identifier renamings and migration warnings during fixup analysis.
#[derive(Debug, Default)]
pub struct FixupCollector {
    pub renamings: BTreeMap<Span, FixupRename>,
    pub warnings: Vec<CompactDiagnostic>,
}

impl FixupCollector {
    pub fn record_rename(
        &mut self,
        span: Span,
        old_name: impl Into<String>,
        new_name: impl Into<String>,
    ) {
        self.renamings.entry(span).or_insert_with(|| FixupRename {
            span,
            old_name: old_name.into(),
            new_name: new_name.into(),
        });
    }
}

/// Lower a single-file AST into a type-checked, witness-checked [`Program`].
pub fn check(file: &SourceFile, ast: &Ast) -> CheckResult {
    check_with_loader(file, ast, &NoopLoader)
}

/// Lower an AST (resolving `include "..."` and `import "..."` via `loader`) into a
/// type-checked, witness-checked [`Program`].
pub fn check_with_loader(file: &SourceFile, ast: &Ast, loader: &dyn ModuleLoader) -> CheckResult {
    check_impl(file, ast, loader, None)
}

/// Run module expansion and type inference in fixup mode, recording deprecated standard-library
/// and ledger-operator renamings into `fixup` without failing on post-inference WPP checks.
pub fn check_with_loader_for_fixup(
    file: &SourceFile,
    ast: &Ast,
    loader: &dyn ModuleLoader,
    fixup: &mut FixupCollector,
) -> CheckResult {
    check_impl(file, ast, loader, Some(fixup))
}

fn check_impl(
    file: &SourceFile,
    ast: &Ast,
    loader: &dyn ModuleLoader,
    fixup: Option<&mut FixupCollector>,
) -> CheckResult {
    let is_fixup = fixup.is_some();
    let mut analyzer = Analyzer {
        units: UnitArena::new(file, ast),
        loader,
        diagnostics: DiagnosticBag::new(),
        include_stack: vec![file.name.clone()],
        scope: ScopeEnv::default(),
        enums: Vec::new(),
        structs: Vec::new(),
        new_types: Vec::new(),
        contracts: Vec::new(),
        pending_implements: Vec::new(),
        ledger_fields: Vec::new(),
        witnesses: Vec::new(),
        constructor_node: None,
        constructor: None,
        circuit_sigs: Vec::new(),
        circuits: Vec::new(),
        exported_stdlib_types: Vec::new(),
        modules: Vec::new(),
        type_aliases: Vec::new(),
        generic_new_types: Vec::new(),
        generic_new_type_cache: HashMap::new(),
        generic_structs: Vec::new(),
        generic_struct_cache: HashMap::new(),
        generic_circuits: Vec::new(),
        generic_circuit_cache: HashMap::new(),
        resolving_aliases: HashSet::new(),
        instantiating_modules: HashSet::new(),
        instantiating_module_files: HashSet::new(),
        new_type_adts: HashMap::new(),
        const_int_locals: HashMap::new(),
        loop_index_locals: HashSet::new(),
        block_consts: Vec::new(),
        next_mod_instance: 0,
        next_local: 0,
        next_ledger_slot: 0,
        stdlib_exports: None,
        stdlib_unit: None,
        kernel_field_id: None,
        fixup,
    };
    analyzer.run();

    let mut program = Program {
        enums: analyzer.enums,
        structs: analyzer.structs,
        new_types: analyzer.new_types,
        contracts: analyzer.contracts,
        ledger_fields: analyzer.ledger_fields,
        witnesses: analyzer.witnesses,
        constructor: analyzer.constructor,
        circuits: analyzer.circuits,
        exported_stdlib_types: analyzer.exported_stdlib_types,
    };

    if !is_fixup {
        witness::reject_recursive_circuits(file, &program, &mut analyzer.diagnostics);
        propagate_purity(
            file,
            &mut program,
            &analyzer.circuit_sigs,
            &mut analyzer.diagnostics,
        );
        check_contract_implements(
            file,
            &program,
            &analyzer.pending_implements,
            &mut analyzer.diagnostics,
        );
        reject_constructor_forbidden_ops(file, &program, &mut analyzer.diagnostics);
        reject_sealed_mutations(file, &program, &mut analyzer.diagnostics);
        check_returns_and_reachability(file, &program, &mut analyzer.diagnostics);
        reject_case_insensitive_duplicate_exports(file, &program, &mut analyzer.diagnostics);
        if !analyzer.diagnostics.has_errors() {
            witness::check_witness_disclosure(file, &program, &mut analyzer.diagnostics);
        }
    }

    CheckResult {
        program,
        diagnostics: analyzer.diagnostics,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct UnitId(usize);

enum UnitRef<'a> {
    Borrowed(&'a SourceFile, &'a Ast),
    Owned(SourceFile, Box<Ast>),
}

impl UnitRef<'_> {
    fn file(&self) -> &SourceFile {
        match self {
            Self::Borrowed(f, _) => f,
            Self::Owned(f, _) => f,
        }
    }

    fn ast(&self) -> &Ast {
        match self {
            Self::Borrowed(_, a) => a,
            Self::Owned(_, a) => a,
        }
    }
}

struct UnitArena<'a> {
    units: Vec<UnitRef<'a>>,
    cur: UnitId,
}

impl<'a> UnitArena<'a> {
    fn new(file: &'a SourceFile, ast: &'a Ast) -> Self {
        Self {
            units: vec![UnitRef::Borrowed(file, ast)],
            cur: UnitId(0),
        }
    }

    #[inline]
    fn file(&self) -> &SourceFile {
        self.units[self.cur.0].file()
    }

    #[inline]
    fn ast(&self) -> &Ast {
        self.units[self.cur.0].ast()
    }

    #[inline]
    fn switch(&mut self, unit: UnitId) -> UnitId {
        let prev = self.cur;
        self.cur = unit;
        prev
    }

    fn push_owned(&mut self, file: SourceFile, ast: Ast) -> UnitId {
        let id = UnitId(self.units.len());
        self.units.push(UnitRef::Owned(file, Box::new(ast)));
        id
    }
}

#[derive(Debug, Clone)]
struct GenericParamDef {
    name: String,
    is_nat: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum GenericArgVal {
    Type(Type),
    Nat(u32),
    BigNat(String),
}

#[derive(Debug, Clone, Default)]
struct GenericEnv {
    types: HashMap<String, Type>,
    nats: HashMap<String, u32>,
    big_nat_bits: HashMap<String, u32>,
}

#[derive(Debug, Clone, Default)]
struct ScopeEnv {
    enums: HashMap<String, EnumId>,
    structs: HashMap<String, StructId>,
    generic_structs: HashMap<String, usize>,
    type_aliases: HashMap<String, usize>,
    new_types: HashMap<String, NewTypeId>,
    generic_new_types: HashMap<String, usize>,
    contracts: HashMap<String, ContractId>,
    ledger_fields: HashMap<String, LedgerFieldId>,
    witnesses: HashMap<String, WitnessId>,
    circuits: HashMap<String, Vec<CircuitId>>,
    generic_circuits: HashMap<String, Vec<usize>>,
    modules: HashMap<String, usize>,
    stdlib_aliases: HashMap<String, String>,
    stdlib_prefixes: Vec<String>,
    generics: GenericEnv,
    has_stdlib: bool,
}

#[derive(Default)]
struct ModuleExports {
    enums: HashMap<String, EnumId>,
    structs: HashMap<String, StructId>,
    generic_structs: HashMap<String, usize>,
    type_aliases: HashMap<String, usize>,
    new_types: HashMap<String, NewTypeId>,
    generic_new_types: HashMap<String, usize>,
    contracts: HashMap<String, ContractId>,
    ledger_fields: HashMap<String, LedgerFieldId>,
    witnesses: HashMap<String, WitnessId>,
    circuits: HashMap<String, Vec<CircuitId>>,
    generic_circuits: HashMap<String, Vec<usize>>,
    modules: HashMap<String, usize>,
    stdlib_aliases: HashMap<String, String>,
}

#[derive(Clone)]
struct ModuleTemplate {
    unit: UnitId,
    name: String,
    gparams: Vec<GenericParamDef>,
    decls: Vec<NodeIndex>,
    outer_scope: ScopeEnv,
}

#[derive(Clone)]
struct TypeAliasTemplate {
    unit: UnitId,
    gparams: Vec<GenericParamDef>,
    target_node: NodeIndex,
    scope: ScopeEnv,
}

#[derive(Clone)]
struct GenericNewTypeTemplate {
    unit: UnitId,
    name: String,
    gparams: Vec<GenericParamDef>,
    target_node: NodeIndex,
    exported: bool,
    span: Span,
    scope: ScopeEnv,
}

#[derive(Clone)]
struct GenericStructTemplate {
    unit: UnitId,
    name: String,
    gparams: Vec<GenericParamDef>,
    fields_start: u32,
    fields_end: u32,
    exported: bool,
    span: Span,
    scope: ScopeEnv,
}

#[derive(Clone)]
struct GenericCircuitTemplate {
    unit: UnitId,
    name: String,
    gparams: Vec<GenericParamDef>,
    params_start: u32,
    params_end: u32,
    ret_type: NodeIndex,
    body_node: NodeIndex,
    declared_pure: bool,
    span: Span,
    scope: ScopeEnv,
}

struct CircuitSig {
    id: CircuitId,
    unit: UnitId,
    scope: ScopeEnv,
    name: String,
    name_span: Span,
    params: Vec<Param>,
    ret_type: Type,
    body_node: NodeIndex,
    exported: bool,
    declared_pure: bool,
    span: Span,
}

#[derive(Clone)]
enum ValueBinding {
    Param(ParamId, Type),
    Local(LocalId, Type),
}

struct Analyzer<'a> {
    units: UnitArena<'a>,
    loader: &'a dyn ModuleLoader,
    diagnostics: DiagnosticBag,
    include_stack: Vec<String>,
    scope: ScopeEnv,
    enums: Vec<EnumDecl>,
    structs: Vec<StructDecl>,
    new_types: Vec<NewTypeDecl>,
    contracts: Vec<ContractDecl>,
    pending_implements: Vec<(Type, Span)>,
    ledger_fields: Vec<LedgerField>,
    witnesses: Vec<WitnessDecl>,
    constructor_node: Option<(UnitId, NodeIndex, ScopeEnv)>,
    constructor: Option<Constructor>,
    circuit_sigs: Vec<CircuitSig>,
    circuits: Vec<Circuit>,
    exported_stdlib_types: Vec<String>,
    modules: Vec<ModuleTemplate>,
    type_aliases: Vec<TypeAliasTemplate>,
    generic_new_types: Vec<GenericNewTypeTemplate>,
    generic_new_type_cache: HashMap<(usize, Vec<GenericArgVal>), NewTypeId>,
    generic_structs: Vec<GenericStructTemplate>,
    generic_struct_cache: HashMap<(usize, Vec<GenericArgVal>), StructId>,
    generic_circuits: Vec<GenericCircuitTemplate>,
    generic_circuit_cache: HashMap<(usize, Vec<GenericArgVal>), CircuitId>,
    resolving_aliases: HashSet<usize>,
    instantiating_modules: HashSet<usize>,
    instantiating_module_files: HashSet<String>,
    new_type_adts: HashMap<NewTypeId, LedgerAdt>,
    const_int_locals: HashMap<LocalId, u128>,
    loop_index_locals: HashSet<LocalId>,
    block_consts: Vec<HashSet<String>>,
    next_mod_instance: usize,
    next_local: u32,
    next_ledger_slot: u32,
    stdlib_exports: Option<ScopeEnv>,
    stdlib_unit: Option<UnitId>,
    kernel_field_id: Option<LedgerFieldId>,
    fixup: Option<&'a mut FixupCollector>,
}

impl<'a> Analyzer<'a> {
    fn alloc_local(&mut self) -> LocalId {
        let id = LocalId(self.next_local);
        self.next_local += 1;
        id
    }

    /// Strip a known `CompactStandardLibrary` import prefix from `name`, returning the unprefixed name.
    fn strip_stdlib_prefix<'b>(&self, name: &'b str) -> Option<(&str, &'b str)> {
        if !self.scope.has_stdlib {
            return None;
        }
        for p in &self.scope.stdlib_prefixes {
            if let Some(rest) = name.strip_prefix(p.as_str()) {
                return Some((p.as_str(), rest));
            }
        }
        if self.scope.stdlib_prefixes.is_empty() {
            return Some(("", name));
        }
        None
    }

    /// Returns `true` if `name` has a user-defined (non-stdlib) circuit or witness binding in scope.
    fn has_user_callable(&self, name: &str) -> bool {
        if self.scope.circuits.contains_key(name) || self.scope.witnesses.contains_key(name) {
            return true;
        }
        if let Some(gids) = self.scope.generic_circuits.get(name) {
            return gids
                .iter()
                .any(|&gid| Some(self.generic_circuits[gid].unit) != self.stdlib_unit);
        }
        false
    }

    /// Returns `true` if `name` matches a deprecated `CompactStandardLibrary` alias under any
    /// active stdlib import prefix in the current scope.
    fn is_deprecated_stdlib_alias(&self, name: &str) -> bool {
        if !self.scope.has_stdlib {
            return false;
        }
        if self.scope.stdlib_prefixes.is_empty() {
            return aliases::lookup_stdlib_circuit_alias(name).is_some();
        }
        self.scope.stdlib_prefixes.iter().any(|p| {
            name.strip_prefix(p.as_str())
                .and_then(aliases::lookup_stdlib_circuit_alias)
                .is_some()
        })
    }

    /// If `name` refers to a deprecated `CompactStandardLibrary` circuit/builtin alias:
    /// - In fixup mode: records the rename (unless `new_name` is shadowed by a user binding, in
    ///   which case a warning is emitted) and returns `Some((canonical_unprefixed, prefixed_new))`.
    /// - In normal compile mode: emits a diagnostic error pointing to the canonical name and
    ///   returns `None`.
    ///
    /// Returns `None` without error if `name` is not a deprecated stdlib alias.
    fn resolve_fixup_stdlib_alias(
        &mut self,
        name: &str,
        name_span: Span,
    ) -> Option<(String, String)> {
        if !self.scope.has_stdlib {
            return None;
        }
        let matched = self
            .scope
            .stdlib_prefixes
            .iter()
            .find_map(|p| {
                let unprefixed = name.strip_prefix(p.as_str())?;
                let canon = aliases::lookup_stdlib_circuit_alias(unprefixed)?;
                Some((p.clone(), canon))
            })
            .or_else(|| {
                if self.scope.stdlib_prefixes.is_empty() {
                    let canon = aliases::lookup_stdlib_circuit_alias(name)?;
                    Some((String::new(), canon))
                } else {
                    None
                }
            });
        let (prefix, canon) = matched?;
        let prefixed_new = format!("{prefix}{canon}");
        let is_root = self.units.cur == UnitId(0);
        let shadowed = self.has_user_callable(&prefixed_new);

        if self.fixup.is_some() {
            if shadowed {
                let warn = CompactDiagnostic::warning(
                    self.units.file(),
                    name_span,
                    format!(
                        "not renaming reference of `{name}` to `{prefixed_new}` because `{prefixed_new}` has other bindings in scope"
                    ),
                );
                if is_root && let Some(fixup) = self.fixup.as_deref_mut() {
                    fixup.warnings.push(warn);
                }
            } else if is_root && let Some(fixup) = self.fixup.as_deref_mut() {
                fixup.record_rename(name_span, name, &prefixed_new);
            }
            Some((canon.to_owned(), prefixed_new))
        } else {
            self.diagnostics.push(
                CompactDiagnostic::error(
                    self.units.file(),
                    name_span,
                    format!(
                        "apparent use of an old standard-library / ledger operator name `{name}`: the new name is `{prefixed_new}`"
                    ),
                )
                .with_help("run `compact fix` to automatically migrate deprecated names"),
            );
            None
        }
    }

    /// Resolve a potentially deprecated ledger ADT method name.
    fn resolve_ledger_op_name<'b>(
        &mut self,
        method_name: &'b str,
        method_span: Span,
    ) -> Option<&'b str> {
        let Some(canon) = aliases::lookup_ledger_op_alias(method_name) else {
            return Some(method_name);
        };
        let is_root = self.units.cur == UnitId(0);
        if let Some(fixup) = self.fixup.as_deref_mut() {
            if is_root {
                fixup.record_rename(method_span, method_name, canon);
            }
            Some(canon)
        } else {
            self.diagnostics.push(
                CompactDiagnostic::error(
                    self.units.file(),
                    method_span,
                    format!(
                        "apparent use of an old standard-library / ledger operator name `{method_name}`: the new name is `{canon}`"
                    ),
                )
                .with_help("run `compact fix` to automatically migrate deprecated names"),
            );
            None
        }
    }

    /// Lazily parse the embedded Compact standard library and register its structs, type aliases,
    /// and circuits as on-demand templates so only referenced items are materialized.
    fn ensure_stdlib_loaded(&mut self) -> ScopeEnv {
        if let Some(ref cached) = self.stdlib_exports {
            return cached.clone();
        }
        let std_file = SourceFile::new(
            compact_span::FileId(u32::MAX - 1),
            "<CompactStandardLibrary>",
            None,
            stdlib::STDLIB_SOURCE,
        );
        let parsed = compact_parser::parse(&std_file);
        debug_assert!(
            !parsed.diagnostics.has_errors(),
            "embedded CompactStandardLibrary failed to parse: {:?}",
            parsed.diagnostics
        );
        let std_unit = self.units.push_owned(std_file, parsed.ast);
        self.stdlib_unit = Some(std_unit);
        let prev = self.units.switch(std_unit);
        let top_decls: Vec<_> = self.units.ast().root_decls().collect();

        let mut std_internal_scope = ScopeEnv {
            has_stdlib: true,
            ..ScopeEnv::default()
        };
        let mut std_exported_scope = ScopeEnv {
            has_stdlib: true,
            ..ScopeEnv::default()
        };
        let mut created_structs = Vec::new();
        let mut created_aliases = Vec::new();
        let mut created_circuits = Vec::new();

        for decl in top_decls {
            match self.units.ast().node_tag(decl) {
                NodeTag::StructDecl => {
                    let s = self.units.ast().struct_decl(decl);
                    let name = self.text(s.name_token).to_owned();
                    let gparams = self.read_generic_params(s.gparams_start, s.gparams_end);
                    let gid = self.generic_structs.len();
                    self.generic_structs.push(GenericStructTemplate {
                        unit: std_unit,
                        name: name.clone(),
                        gparams,
                        fields_start: s.fields_start,
                        fields_end: s.fields_end,
                        exported: false,
                        span: self.units.ast().node_span(decl),
                        scope: ScopeEnv::default(),
                    });
                    std_internal_scope.generic_structs.insert(name.clone(), gid);
                    if s.exported {
                        std_exported_scope.generic_structs.insert(name, gid);
                    }
                    created_structs.push(gid);
                }
                NodeTag::TypeDecl => {
                    let td = self.units.ast().type_decl(decl);
                    let name = self.text(td.name_token).to_owned();
                    let gparams = self.read_generic_params(td.gparams_start, td.gparams_end);
                    let aid = self.type_aliases.len();
                    self.type_aliases.push(TypeAliasTemplate {
                        unit: std_unit,
                        gparams,
                        target_node: td.target_type,
                        scope: ScopeEnv::default(),
                    });
                    std_internal_scope.type_aliases.insert(name.clone(), aid);
                    if td.exported {
                        std_exported_scope.type_aliases.insert(name, aid);
                    }
                    created_aliases.push(aid);
                }
                NodeTag::CircuitDecl => {
                    let c = self.units.ast().circuit_decl(decl);
                    let name = self.text(c.name_token).to_owned();
                    let gparams = self.read_generic_params(c.gparams_start, c.gparams_end);
                    let gid = self.generic_circuits.len();
                    self.generic_circuits.push(GenericCircuitTemplate {
                        unit: std_unit,
                        name: name.clone(),
                        gparams,
                        params_start: c.params_start,
                        params_end: c.params_end,
                        ret_type: c.ret_type,
                        body_node: c.body,
                        declared_pure: c.pure,
                        span: self.units.ast().node_span(decl),
                        scope: ScopeEnv::default(),
                    });
                    std_internal_scope
                        .generic_circuits
                        .entry(name.clone())
                        .or_default()
                        .push(gid);
                    if c.exported {
                        std_exported_scope
                            .generic_circuits
                            .entry(name)
                            .or_default()
                            .push(gid);
                    }
                    created_circuits.push(gid);
                }
                _ => {}
            }
        }

        for &gid in &created_structs {
            self.generic_structs[gid].scope = std_internal_scope.clone();
        }
        for &aid in &created_aliases {
            self.type_aliases[aid].scope = std_internal_scope.clone();
        }
        for &gid in &created_circuits {
            self.generic_circuits[gid].scope = std_internal_scope.clone();
        }

        self.units.switch(prev);
        self.stdlib_exports = Some(std_exported_scope.clone());
        std_exported_scope
    }

    /// Lazily materialize the implicit `kernel: Kernel` ledger field (with empty state path).
    fn ensure_kernel_field(&mut self) -> LedgerFieldId {
        if let Some(id) = self.kernel_field_id {
            return id;
        }
        let id = LedgerFieldId(self.ledger_fields.len() as u32);
        self.ledger_fields.push(LedgerField {
            id,
            name: "kernel".to_owned(),
            adt: LedgerAdt::Kernel,
            path: Vec::new(),
            exported: false,
            sealed: false,
            span: Span::EMPTY,
        });
        self.kernel_field_id = Some(id);
        id
    }

    /// Resolve a stdlib struct by name (instantiating its lazy 0-param template if needed).
    fn resolve_stdlib_struct(&mut self, name: &str, span: Span) -> Option<Type> {
        let std_scope = self.ensure_stdlib_loaded();
        let &gid = std_scope.generic_structs.get(name)?;
        let sid = self.instantiate_generic_struct(gid, &[], span)?;
        Some(Type::Struct(sid))
    }

    fn text(&self, tok: TokenIndex) -> &str {
        self.units.ast().token_text(tok, self.units.file().text())
    }

    fn underlying_type<'b>(&'b self, mut ty: &'b Type) -> &'b Type {
        let limit = self.new_types.len();
        let mut steps = 0;
        while let Type::NewType(id) = ty {
            if steps > limit {
                break;
            }
            steps += 1;
            ty = &self.new_types[id.0 as usize].inner;
        }
        ty
    }

    fn reject_cyclic_types(&mut self) {
        #[derive(Copy, Clone, PartialEq, Eq, Hash)]
        enum TypeNode {
            NewType(u32),
            Struct(u32),
        }

        fn visit(
            node: TypeNode,
            new_types: &[NewTypeDecl],
            structs: &[StructDecl],
            visiting: &mut HashSet<TypeNode>,
            visited: &mut HashSet<TypeNode>,
            cyclic_new_types: &mut Vec<u32>,
            cyclic_structs: &mut Vec<u32>,
        ) -> bool {
            if visited.contains(&node) {
                return false;
            }
            if !visiting.insert(node) {
                return true;
            }
            let mut has_cycle = false;
            let check_ty = |ty: &Type,
                            visiting: &mut HashSet<TypeNode>,
                            visited: &mut HashSet<TypeNode>,
                            cyclic_nt: &mut Vec<u32>,
                            cyclic_st: &mut Vec<u32>|
             -> bool {
                fn walk(
                    ty: &Type,
                    new_types: &[NewTypeDecl],
                    structs: &[StructDecl],
                    visiting: &mut HashSet<TypeNode>,
                    visited: &mut HashSet<TypeNode>,
                    cyclic_nt: &mut Vec<u32>,
                    cyclic_st: &mut Vec<u32>,
                ) -> bool {
                    match ty {
                        Type::NewType(id) => visit(
                            TypeNode::NewType(id.0),
                            new_types,
                            structs,
                            visiting,
                            visited,
                            cyclic_nt,
                            cyclic_st,
                        ),
                        Type::Struct(id) => visit(
                            TypeNode::Struct(id.0),
                            new_types,
                            structs,
                            visiting,
                            visited,
                            cyclic_nt,
                            cyclic_st,
                        ),
                        Type::Vector(_, inner) | Type::Maybe(inner) => walk(
                            inner, new_types, structs, visiting, visited, cyclic_nt, cyclic_st,
                        ),
                        Type::Either(l, r) => {
                            let a = walk(
                                l, new_types, structs, visiting, visited, cyclic_nt, cyclic_st,
                            );
                            let b = walk(
                                r, new_types, structs, visiting, visited, cyclic_nt, cyclic_st,
                            );
                            a || b
                        }
                        Type::Tuple(elems) => elems.iter().any(|e| {
                            walk(
                                e, new_types, structs, visiting, visited, cyclic_nt, cyclic_st,
                            )
                        }),
                        Type::MerkleTreePath(_, leaf) => walk(
                            leaf, new_types, structs, visiting, visited, cyclic_nt, cyclic_st,
                        ),
                        _ => false,
                    }
                }
                walk(
                    ty, new_types, structs, visiting, visited, cyclic_nt, cyclic_st,
                )
            };

            match node {
                TypeNode::NewType(id) => {
                    let inner = &new_types[id as usize].inner;
                    if check_ty(inner, visiting, visited, cyclic_new_types, cyclic_structs) {
                        has_cycle = true;
                        cyclic_new_types.push(id);
                    }
                }
                TypeNode::Struct(id) => {
                    for f in &structs[id as usize].fields {
                        if check_ty(&f.ty, visiting, visited, cyclic_new_types, cyclic_structs) {
                            has_cycle = true;
                        }
                    }
                    if has_cycle {
                        cyclic_structs.push(id);
                    }
                }
            }
            visiting.remove(&node);
            visited.insert(node);
            has_cycle
        }

        let mut visiting = HashSet::new();
        let mut visited = HashSet::new();
        let mut cyclic_nt = Vec::new();
        let mut cyclic_st = Vec::new();
        for i in 0..self.new_types.len() {
            visit(
                TypeNode::NewType(i as u32),
                &self.new_types,
                &self.structs,
                &mut visiting,
                &mut visited,
                &mut cyclic_nt,
                &mut cyclic_st,
            );
        }
        for i in 0..self.structs.len() {
            visit(
                TypeNode::Struct(i as u32),
                &self.new_types,
                &self.structs,
                &mut visiting,
                &mut visited,
                &mut cyclic_nt,
                &mut cyclic_st,
            );
        }
        cyclic_nt.sort_unstable();
        cyclic_nt.dedup();
        for id in cyclic_nt {
            let nt = &mut self.new_types[id as usize];
            let name = nt.name.clone();
            let span = nt.span;
            nt.inner = Type::unit();
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                span,
                format!("cyclic new type definition `{name}`"),
            ));
        }
        cyclic_st.sort_unstable();
        cyclic_st.dedup();
        for id in cyclic_st {
            let st = &self.structs[id as usize];
            let name = st.name.clone();
            let span = st.span;
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                span,
                format!("cyclic struct definition `{name}`"),
            ));
        }
    }

    fn read_generic_params(&self, start: u32, end: u32) -> Vec<GenericParamDef> {
        self.units
            .ast()
            .extra_nodes(start, end)
            .map(|gp_node| {
                let gp = self.units.ast().generic_param(gp_node);
                GenericParamDef {
                    name: self.text(gp.name_token).to_owned(),
                    is_nat: gp.is_nat,
                }
            })
            .collect()
    }

    fn run(&mut self) {
        let root_decls: Vec<_> = self.units.ast().root_decls().collect();
        let _ = self.process_scope_decls(UnitId(0), &root_decls, None, false);
        self.reject_cyclic_types();

        // Pass 2: type-check constructor & all concrete + on-demand monomorphized circuit bodies.
        if let Some((ctor_unit, ctor_node, ctor_scope)) = self.constructor_node.clone() {
            let prev_unit = self.units.switch(ctor_unit);
            let prev_scope = std::mem::replace(&mut self.scope, ctor_scope);
            self.check_constructor(ctor_node);
            self.scope = prev_scope;
            self.units.switch(prev_unit);
        }

        let mut sig_idx = 0;
        while sig_idx < self.circuit_sigs.len() {
            self.check_circuit_body(sig_idx);
            sig_idx += 1;
        }
    }

    /// Expand `pragma` and `include` declarations into a flat `(UnitId, NodeIndex)` list.
    fn expand_includes(
        &mut self,
        unit: UnitId,
        decls: &[NodeIndex],
        out: &mut Vec<(UnitId, NodeIndex)>,
    ) {
        let prev_unit = self.units.switch(unit);
        for &decl in decls {
            match self.units.ast().node_tag(decl) {
                NodeTag::PragmaDecl => {
                    pragma::check_pragma(
                        self.units.file(),
                        self.units.ast(),
                        decl,
                        &mut self.diagnostics,
                    );
                }
                NodeTag::IncludeDecl => {
                    let inc = self.units.ast().include_decl(decl);
                    let raw_path = self.text(inc.path_token).to_owned();
                    let spec = unquote_string(&raw_path);
                    let span = self.units.ast().node_span(decl);
                    let from_file = self.units.file().clone();
                    match self.loader.load(&from_file, &spec) {
                        Ok((inc_file, inc_ast)) => {
                            let canonical = inc_file
                                .path
                                .as_ref()
                                .map(|p| p.display().to_string())
                                .unwrap_or_else(|| inc_file.name.clone());
                            if self.include_stack.contains(&canonical) {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    span,
                                    format!("include cycle involving `{spec}`"),
                                ));
                                continue;
                            }
                            let child_unit = self.units.push_owned(inc_file, inc_ast);
                            let child_prev = self.units.switch(child_unit);
                            let child_decls: Vec<_> = self.units.ast().root_decls().collect();
                            self.units.switch(child_prev);
                            self.include_stack.push(canonical);
                            self.expand_includes(child_unit, &child_decls, out);
                            self.include_stack.pop();
                        }
                        Err(LoadError::NotFound(msg)) => {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                span,
                                msg,
                            ));
                        }
                        Err(LoadError::ParseFailed(bag)) => {
                            for d in bag.diagnostics {
                                self.diagnostics.push(d);
                            }
                        }
                    }
                }
                _ => out.push((unit, decl)),
            }
        }
        self.units.switch(prev_unit);
    }

    /// Process all declarations within a root file or an instantiated module body.
    /// When `is_module_instance` is true, `export` marks items in the returned [`ModuleExports`]
    /// rather than marking them as public contract entry points.
    fn process_scope_decls(
        &mut self,
        unit: UnitId,
        raw_decls: &[NodeIndex],
        mangle_prefix: Option<&str>,
        is_module_instance: bool,
    ) -> ModuleExports {
        let mut decls = Vec::new();
        self.expand_includes(unit, raw_decls, &mut decls);

        let mut exports = ModuleExports::default();
        let mut export_list_tokens: Vec<(UnitId, TokenIndex)> = Vec::new();
        let mut created_circuits: Vec<usize> = Vec::new();
        let mut created_generic_circuits: Vec<usize> = Vec::new();
        let mut created_generic_structs: Vec<usize> = Vec::new();
        let mut created_type_aliases: Vec<usize> = Vec::new();
        let mut created_generic_new_types: Vec<usize> = Vec::new();
        let mut created_modules: Vec<usize> = Vec::new();
        let mut pending_new_types: Vec<(UnitId, NodeIndex, NewTypeId)> = Vec::new();
        let mut pending_structs: Vec<(UnitId, NodeIndex, StructId)> = Vec::new();
        let mut pending_contracts: Vec<(UnitId, NodeIndex, ContractId)> = Vec::new();
        let mut pending_implements_nodes: Vec<(UnitId, NodeIndex)> = Vec::new();

        // Pass 1a-0: register module templates first so imports can reference modules in any order.
        for &(du, decl) in &decls {
            let prev = self.units.switch(du);
            if self.units.ast().node_tag(decl) == NodeTag::ModuleDecl {
                let m = self.units.ast().module_decl(decl);
                let name = self.text(m.name_token).to_owned();
                let gparams = self.read_generic_params(m.gparams_start, m.gparams_end);
                let body_decls: Vec<_> = self
                    .units
                    .ast()
                    .extra_nodes(m.decls_start, m.decls_end)
                    .collect();
                let mid = self.modules.len();
                self.modules.push(ModuleTemplate {
                    unit: du,
                    name: name.clone(),
                    gparams,
                    decls: body_decls,
                    outer_scope: self.scope.clone(),
                });
                self.scope.modules.insert(name.clone(), mid);
                if m.exported {
                    exports.modules.insert(name, mid);
                }
                created_modules.push(mid);
            }
            self.units.switch(prev);
        }
        if !is_module_instance && !created_modules.is_empty() {
            self.validate_declared_modules(&created_modules);
        }

        // Pass 1a-1: export lists, enums, type aliases, new types, and struct names.
        for &(du, decl) in &decls {
            let prev = self.units.switch(du);
            match self.units.ast().node_tag(decl) {
                NodeTag::ExportListDecl => {
                    let list = self.units.ast().export_list_decl(decl);
                    for tok in self
                        .units
                        .ast()
                        .extra_tokens(list.names_start, list.names_end)
                    {
                        export_list_tokens.push((du, tok));
                    }
                }
                NodeTag::EnumDecl => {
                    if let Some((local_name, eid, exported)) =
                        self.register_enum(decl, mangle_prefix, is_module_instance)
                        && exported
                    {
                        exports.enums.insert(local_name, eid);
                    }
                }
                NodeTag::StructDecl => {
                    let s = self.units.ast().struct_decl(decl);
                    let local_name = self.text(s.name_token).to_owned();
                    let gparams = self.read_generic_params(s.gparams_start, s.gparams_end);
                    if !gparams.is_empty() {
                        let gid = self.generic_structs.len();
                        let hir_name = mangle_name(mangle_prefix, &local_name);
                        self.generic_structs.push(GenericStructTemplate {
                            unit: du,
                            name: hir_name,
                            gparams,
                            fields_start: s.fields_start,
                            fields_end: s.fields_end,
                            exported: !is_module_instance && s.exported,
                            span: self.units.ast().node_span(decl),
                            scope: ScopeEnv::default(),
                        });
                        self.scope.generic_structs.insert(local_name.clone(), gid);
                        if s.exported {
                            exports.generic_structs.insert(local_name, gid);
                        }
                        created_generic_structs.push(gid);
                    } else if let Some((sname, sid, exported)) =
                        self.register_struct_name(decl, mangle_prefix, is_module_instance)
                    {
                        pending_structs.push((du, decl, sid));
                        if exported {
                            exports.structs.insert(sname, sid);
                        }
                    }
                }
                NodeTag::TypeDecl => {
                    let td = self.units.ast().type_decl(decl);
                    let local_name = self.text(td.name_token).to_owned();
                    let name_span = self.units.ast().token_span(td.name_token);
                    if is_builtin_type_name(&local_name)
                        || (self.scope.has_stdlib && is_stdlib_type_name(&local_name))
                    {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            name_span,
                            format!("cannot redefine built-in type `{local_name}`"),
                        ));
                        self.units.switch(prev);
                        continue;
                    }
                    if self.scope.type_aliases.contains_key(&local_name)
                        || self.scope.new_types.contains_key(&local_name)
                        || self.scope.generic_new_types.contains_key(&local_name)
                        || self.scope.structs.contains_key(&local_name)
                        || self.scope.generic_structs.contains_key(&local_name)
                        || self.scope.enums.contains_key(&local_name)
                    {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            name_span,
                            format!("duplicate type definition `{local_name}`"),
                        ));
                        self.units.switch(prev);
                        continue;
                    }
                    let gparams = self.read_generic_params(td.gparams_start, td.gparams_end);
                    if !td.is_new {
                        let aid = self.type_aliases.len();
                        self.type_aliases.push(TypeAliasTemplate {
                            unit: du,
                            gparams,
                            target_node: td.target_type,
                            scope: ScopeEnv::default(),
                        });
                        self.scope.type_aliases.insert(local_name.clone(), aid);
                        if td.exported {
                            exports.type_aliases.insert(local_name, aid);
                        }
                        created_type_aliases.push(aid);
                    } else if !gparams.is_empty() {
                        let gid = self.generic_new_types.len();
                        let hir_name = mangle_name(mangle_prefix, &local_name);
                        self.generic_new_types.push(GenericNewTypeTemplate {
                            unit: du,
                            name: hir_name,
                            gparams,
                            target_node: td.target_type,
                            exported: !is_module_instance && td.exported,
                            span: self.units.ast().node_span(decl),
                            scope: ScopeEnv::default(),
                        });
                        self.scope.generic_new_types.insert(local_name.clone(), gid);
                        if td.exported {
                            exports.generic_new_types.insert(local_name, gid);
                        }
                        created_generic_new_types.push(gid);
                    } else {
                        let nid = NewTypeId(self.new_types.len() as u32);
                        let hir_name = mangle_name(mangle_prefix, &local_name);
                        self.new_types.push(NewTypeDecl {
                            id: nid,
                            name: hir_name,
                            inner: Type::unit(),
                            exported: !is_module_instance && td.exported,
                            span: self.units.ast().node_span(decl),
                        });
                        self.scope.new_types.insert(local_name.clone(), nid);
                        pending_new_types.push((du, decl, nid));
                        if td.exported {
                            exports.new_types.insert(local_name, nid);
                        }
                    }
                }
                NodeTag::ContractDecl => {
                    let cd = self.units.ast().contract_decl(decl);
                    let local_name = self.text(cd.name_token).to_owned();
                    let cid = ContractId(self.contracts.len() as u32);
                    let hir_name = mangle_name(mangle_prefix, &local_name);
                    self.contracts.push(ContractDecl {
                        id: cid,
                        name: hir_name,
                        circuits: Vec::new(),
                        exported: !is_module_instance && cd.exported,
                        span: self.units.ast().node_span(decl),
                    });
                    self.scope.contracts.insert(local_name.clone(), cid);
                    if cd.exported {
                        exports.contracts.insert(local_name, cid);
                    }
                    pending_contracts.push((du, decl, cid));
                }
                NodeTag::ContractImplementsDecl => {
                    pending_implements_nodes.push((du, decl));
                }
                _ => {}
            }
            self.units.switch(prev);
        }

        // Pass 1a-2: process imports (refreshing local template scopes before each import so
        // instantiated modules can see sibling types, aliases, and earlier imports).
        for &(du, decl) in &decls {
            let prev = self.units.switch(du);
            if self.units.ast().node_tag(decl) == NodeTag::ImportDecl {
                let current_scope = self.scope.clone();
                for &aid in &created_type_aliases {
                    self.type_aliases[aid].scope = current_scope.clone();
                }
                for &gid in &created_generic_new_types {
                    self.generic_new_types[gid].scope = current_scope.clone();
                }
                for &gid in &created_generic_structs {
                    self.generic_structs[gid].scope = current_scope.clone();
                }
                for &mid in &created_modules {
                    self.modules[mid].outer_scope = current_scope.clone();
                }
                self.process_import_decl(decl);
            }
            self.units.switch(prev);
        }

        // Snapshot type-level scope into type aliases, generic type templates, and modules so
        // they can resolve sibling and imported types during Pass 1a.5.
        let type_scope = self.scope.clone();
        for &aid in &created_type_aliases {
            self.type_aliases[aid].scope = type_scope.clone();
        }
        for &gid in &created_generic_new_types {
            self.generic_new_types[gid].scope = type_scope.clone();
        }
        for &gid in &created_generic_structs {
            self.generic_structs[gid].scope = type_scope.clone();
        }
        for &mid in &created_modules {
            self.modules[mid].outer_scope = type_scope.clone();
        }

        // Pass 1a.5: populate non-generic new type targets & struct field types.
        for &(du, decl, nid) in &pending_new_types {
            let prev = self.units.switch(du);
            let td = self.units.ast().type_decl(decl);
            if self.is_adt_type_node(td.target_type) {
                if let Some(adt) = self.resolve_ledger_adt(td.target_type) {
                    self.new_type_adts.insert(nid, adt);
                }
            } else if let Some(inner) = self.resolve_type(td.target_type) {
                self.new_types[nid.0 as usize].inner = inner;
            }
            self.units.switch(prev);
        }
        for &(du, decl, sid) in &pending_structs {
            let prev = self.units.switch(du);
            self.populate_struct_fields(decl, sid);
            self.units.switch(prev);
        }
        for &(du, decl, cid) in &pending_contracts {
            let prev = self.units.switch(du);
            self.populate_contract_circuits(decl, cid);
            self.units.switch(prev);
        }
        for &(du, decl) in &pending_implements_nodes {
            let prev = self.units.switch(du);
            let impl_decl = self.units.ast().contract_implements_decl(decl);
            let span = self.units.ast().node_span(decl);
            if let Some(ty) = self.resolve_type(impl_decl.type_node) {
                self.pending_implements.push((ty, span));
            }
            self.units.switch(prev);
        }

        // Pass 1b: ledger declarations, witnesses, constructor, and circuit signatures.
        for &(du, decl) in &decls {
            let prev = self.units.switch(du);
            match self.units.ast().node_tag(decl) {
                NodeTag::LedgerDecl => {
                    if let Some((lname, fid, exported)) =
                        self.register_ledger(decl, mangle_prefix, is_module_instance)
                        && exported
                    {
                        exports.ledger_fields.insert(lname, fid);
                    }
                }
                NodeTag::WitnessDecl => {
                    if let Some((wname, wid, exported)) =
                        self.register_witness(decl, mangle_prefix, is_module_instance)
                        && exported
                    {
                        exports.witnesses.insert(wname, wid);
                    }
                }
                NodeTag::ConstructorDecl => {
                    if is_module_instance {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            self.units.ast().node_span(decl),
                            "`constructor` is not allowed inside a module",
                        ));
                    } else if self.constructor_node.is_some() {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            self.units.ast().node_span(decl),
                            "duplicate `constructor` declaration",
                        ));
                    } else {
                        self.constructor_node = Some((du, decl, ScopeEnv::default()));
                    }
                }
                NodeTag::CircuitDecl => {
                    let c = self.units.ast().circuit_decl(decl);
                    let local_name = self.text(c.name_token).to_owned();
                    let gparams = self.read_generic_params(c.gparams_start, c.gparams_end);
                    if !gparams.is_empty() {
                        let gid = self.generic_circuits.len();
                        let hir_name = mangle_name(mangle_prefix, &local_name);
                        self.generic_circuits.push(GenericCircuitTemplate {
                            unit: du,
                            name: hir_name,
                            gparams,
                            params_start: c.params_start,
                            params_end: c.params_end,
                            ret_type: c.ret_type,
                            body_node: c.body,
                            declared_pure: c.pure,
                            span: self.units.ast().node_span(decl),
                            scope: ScopeEnv::default(),
                        });
                        self.scope
                            .generic_circuits
                            .entry(local_name.clone())
                            .or_default()
                            .push(gid);
                        if c.exported {
                            exports
                                .generic_circuits
                                .entry(local_name)
                                .or_default()
                                .push(gid);
                        }
                        created_generic_circuits.push(gid);
                    } else if let Some((cname, cid, exported)) =
                        self.register_circuit_sig(du, decl, mangle_prefix, is_module_instance)
                    {
                        created_circuits.push(cid.0 as usize);
                        if exported {
                            exports.circuits.entry(cname).or_default().push(cid);
                        }
                    }
                }
                _ => {}
            }
            self.units.switch(prev);
        }

        // Apply standalone `export { ... }` lists.
        for (du, tok) in export_list_tokens {
            let prev = self.units.switch(du);
            let name = self.text(tok).to_owned();
            if let Some(cids) = self.scope.circuits.get(&name).cloned() {
                if is_module_instance {
                    exports.circuits.entry(name).or_default().extend(cids);
                } else {
                    for cid in cids {
                        self.circuit_sigs[cid.0 as usize].exported = true;
                        self.circuit_sigs[cid.0 as usize].name = name.clone();
                    }
                }
            } else if let Some(gids) = self.scope.generic_circuits.get(&name).cloned() {
                if is_module_instance {
                    exports
                        .generic_circuits
                        .entry(name)
                        .or_default()
                        .extend(gids);
                } else {
                    for gid in gids {
                        if self.generic_circuits[gid].gparams.is_empty()
                            && let Some(cid) = self.instantiate_generic_circuit(
                                gid,
                                &[],
                                self.units.ast().token_span(tok),
                            )
                        {
                            self.circuit_sigs[cid.0 as usize].exported = true;
                            self.circuit_sigs[cid.0 as usize].name = name.clone();
                        }
                    }
                }
            } else if let Some(&eid) = self.scope.enums.get(&name) {
                if is_module_instance {
                    exports.enums.insert(name, eid);
                } else {
                    self.enums[eid.0 as usize].exported = true;
                    self.enums[eid.0 as usize].name = name;
                }
            } else if let Some(&sid) = self.scope.structs.get(&name) {
                if is_module_instance {
                    exports.structs.insert(name, sid);
                } else {
                    self.structs[sid.0 as usize].exported = true;
                    self.structs[sid.0 as usize].name = name;
                }
            } else if let Some(&gid) = self.scope.generic_structs.get(&name) {
                if is_module_instance {
                    exports.generic_structs.insert(name, gid);
                } else if self.generic_structs[gid].gparams.is_empty()
                    && let Some(sid) =
                        self.instantiate_generic_struct(gid, &[], self.units.ast().token_span(tok))
                {
                    self.structs[sid.0 as usize].exported = true;
                    self.structs[sid.0 as usize].name = name;
                }
            } else if let Some(&nid) = self.scope.new_types.get(&name) {
                if is_module_instance {
                    exports.new_types.insert(name, nid);
                } else {
                    self.new_types[nid.0 as usize].exported = true;
                    self.new_types[nid.0 as usize].name = name;
                }
            } else if let Some(&cid) = self.scope.contracts.get(&name) {
                if is_module_instance {
                    exports.contracts.insert(name, cid);
                } else {
                    self.contracts[cid.0 as usize].exported = true;
                    self.contracts[cid.0 as usize].name = name;
                }
            } else if let Some(&aid) = self.scope.type_aliases.get(&name) {
                if is_module_instance {
                    exports.type_aliases.insert(name, aid);
                }
            } else if let Some(&fid) = self.scope.ledger_fields.get(&name) {
                if is_module_instance {
                    exports.ledger_fields.insert(name, fid);
                } else {
                    self.ledger_fields[fid.0 as usize].exported = true;
                    self.ledger_fields[fid.0 as usize].name = name;
                }
            } else if let Some(&wid) = self.scope.witnesses.get(&name) {
                if is_module_instance {
                    exports.witnesses.insert(name, wid);
                } else {
                    self.witnesses[wid.0 as usize].exported = true;
                    self.witnesses[wid.0 as usize].name = name;
                }
            } else if let Some(canon) = self.scope.stdlib_aliases.get(&name).cloned() {
                if is_module_instance {
                    exports.stdlib_aliases.insert(name, canon);
                } else if !self.exported_stdlib_types.iter().any(|s| s == &canon) {
                    self.exported_stdlib_types.push(canon);
                }
            } else if !is_module_instance
                && self.scope.has_stdlib
                && matches!(
                    name.as_str(),
                    "Maybe"
                        | "Either"
                        | "MerkleTreeDigest"
                        | "MerkleTreePathEntry"
                        | "MerkleTreePath"
                )
            {
                if !self.exported_stdlib_types.iter().any(|s| s == &name) {
                    self.exported_stdlib_types.push(name);
                }
            } else if self.is_deprecated_stdlib_alias(&name) {
                let tok_span = self.units.ast().token_span(tok);
                if let Some((_canon, prefixed_new)) =
                    self.resolve_fixup_stdlib_alias(&name, tok_span)
                    && let Some(gids) = self.scope.generic_circuits.get(&prefixed_new).cloned()
                    && is_module_instance
                {
                    exports.generic_circuits.insert(prefixed_new, gids);
                }
            } else {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    self.units.ast().token_span(tok),
                    format!("cannot export unknown item `{name}`"),
                ));
            }
            self.units.switch(prev);
        }

        // Capture final scope into every circuit & template defined in this scope.
        let final_scope = self.scope.clone();
        for &cid in &created_circuits {
            self.circuit_sigs[cid].scope = final_scope.clone();
        }
        for &gid in &created_generic_circuits {
            self.generic_circuits[gid].scope = final_scope.clone();
        }
        for &gid in &created_generic_structs {
            self.generic_structs[gid].scope = final_scope.clone();
        }
        for &aid in &created_type_aliases {
            self.type_aliases[aid].scope = final_scope.clone();
        }
        for &gid in &created_generic_new_types {
            self.generic_new_types[gid].scope = final_scope.clone();
        }
        for &mid in &created_modules {
            self.modules[mid].outer_scope = final_scope.clone();
        }
        if !is_module_instance && let Some((_, _, ref mut cscope)) = self.constructor_node {
            *cscope = final_scope;
        }

        exports
    }

    fn process_import_decl(&mut self, node: NodeIndex) {
        let import = self.units.ast().import_decl(node);
        let name_tag = self.units.ast().token_tag(import.name_token);
        let raw_name = self.text(import.name_token).to_owned();
        let name_span = self.units.ast().token_span(import.name_token);
        let prefix = import.prefix_token.map(|t| self.text(t).to_owned());

        let garg_nodes: Vec<_> = self
            .units
            .ast()
            .extra_nodes(import.gargs_start, import.gargs_end)
            .collect();
        let item_nodes: Vec<_> = self
            .units
            .ast()
            .extra_nodes(import.items_start, import.items_end)
            .collect();
        let selections: Vec<(String, String, Span)> = item_nodes
            .into_iter()
            .map(|inode| {
                let item = self.units.ast().import_item(inode);
                let orig = self.text(item.name_token).to_owned();
                let alias = item
                    .alias_token
                    .map(|t| self.text(t).to_owned())
                    .unwrap_or_else(|| orig.clone());
                (orig, alias, self.units.ast().node_span(inode))
            })
            .collect();

        if name_tag == TokenTag::Ident && raw_name == "CompactStandardLibrary" {
            if self.scope.circuits.contains_key("CompactStandardLibrary")
                || self
                    .scope
                    .generic_circuits
                    .contains_key("CompactStandardLibrary")
                || self
                    .scope
                    .type_aliases
                    .contains_key("CompactStandardLibrary")
                || self.scope.new_types.contains_key("CompactStandardLibrary")
                || self
                    .scope
                    .generic_new_types
                    .contains_key("CompactStandardLibrary")
                || self.scope.structs.contains_key("CompactStandardLibrary")
                || self
                    .scope
                    .generic_structs
                    .contains_key("CompactStandardLibrary")
                || self.scope.enums.contains_key("CompactStandardLibrary")
                || self
                    .scope
                    .ledger_fields
                    .contains_key("CompactStandardLibrary")
                || self.scope.witnesses.contains_key("CompactStandardLibrary")
                || self.scope.contracts.contains_key("CompactStandardLibrary")
                || self.scope.modules.contains_key("CompactStandardLibrary")
            {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    name_span,
                    "cannot import `CompactStandardLibrary` because the name is already bound",
                ));
                return;
            }
            self.scope.has_stdlib = true;
            if selections.is_empty() {
                let pref = prefix.clone().unwrap_or_default();
                if !self.scope.stdlib_prefixes.contains(&pref) {
                    self.scope.stdlib_prefixes.push(pref);
                }
            }
            let std_scope = self.ensure_stdlib_loaded();
            let apply_prefix = |name: &str| -> String {
                match &prefix {
                    Some(p) => format!("{p}{name}"),
                    None => name.to_owned(),
                }
            };
            if selections.is_empty() {
                // Reject user-declared types/aliases that collide with imported CompactStandardLibrary names
                // (while allowing idempotent repeated `import CompactStandardLibrary;` in the same scope).
                let check_collision =
                    |imported_name: &str, expected_ta: Option<usize>, diags: &mut DiagnosticBag| {
                        let ta_conflict = self
                            .scope
                            .type_aliases
                            .get(imported_name)
                            .is_some_and(|&aid| Some(aid) != expected_ta);
                        if ta_conflict
                            || self.scope.new_types.contains_key(imported_name)
                            || self.scope.generic_new_types.contains_key(imported_name)
                            || self.scope.structs.contains_key(imported_name)
                            || self.scope.enums.contains_key(imported_name)
                        {
                            diags.push(CompactDiagnostic::error(
                            self.units.file(),
                            name_span,
                            format!(
                                "declaration `{imported_name}` conflicts with imported `CompactStandardLibrary` binding"
                            ),
                        ));
                        }
                    };
                for k in std_scope.generic_structs.keys() {
                    check_collision(&apply_prefix(k), None, &mut self.diagnostics);
                }
                for (k, &aid) in &std_scope.type_aliases {
                    check_collision(&apply_prefix(k), Some(aid), &mut self.diagnostics);
                }
                for std_builtin in [
                    "Maybe",
                    "Either",
                    "MerkleTreeDigest",
                    "MerkleTreePathEntry",
                    "MerkleTreePath",
                    "JubjubScalar",
                    "JubjubPoint",
                    "Secp256k1Base",
                    "Secp256k1Scalar",
                    "Secp256k1Point",
                    "Secp256r1Base",
                    "Secp256r1Scalar",
                    "Secp256r1Point",
                    "Curve25519Base",
                    "Curve25519Scalar",
                    "Curve25519Point",
                ] {
                    check_collision(&apply_prefix(std_builtin), None, &mut self.diagnostics);
                }
                for (k, v) in std_scope.generic_structs {
                    self.scope
                        .generic_structs
                        .entry(apply_prefix(&k))
                        .or_insert(v);
                }
                for (k, v) in std_scope.type_aliases {
                    self.scope.type_aliases.entry(apply_prefix(&k)).or_insert(v);
                }
                for (k, v) in std_scope.generic_circuits {
                    let entry = self
                        .scope
                        .generic_circuits
                        .entry(apply_prefix(&k))
                        .or_default();
                    for gid in v {
                        if !entry.contains(&gid) {
                            entry.push(gid);
                        }
                    }
                }
            } else {
                for (orig, alias, ispan) in selections {
                    let target = apply_prefix(&alias);
                    let expected_ta = std_scope.type_aliases.get(&orig).copied();
                    let ta_conflict = self
                        .scope
                        .type_aliases
                        .get(&target)
                        .is_some_and(|&aid| Some(aid) != expected_ta);
                    if ta_conflict
                        || self.scope.new_types.contains_key(&target)
                        || self.scope.structs.contains_key(&target)
                        || self.scope.enums.contains_key(&target)
                    {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            ispan,
                            format!(
                                "imported `CompactStandardLibrary` name `{target}` conflicts with an existing binding"
                            ),
                        ));
                    }
                    if let Some(&v) = std_scope.generic_structs.get(&orig) {
                        self.scope.generic_structs.insert(target.clone(), v);
                    }
                    if let Some(&v) = std_scope.type_aliases.get(&orig) {
                        self.scope.type_aliases.insert(target.clone(), v);
                    }
                    if let Some(v) = std_scope.generic_circuits.get(&orig) {
                        let entry = self
                            .scope
                            .generic_circuits
                            .entry(target.clone())
                            .or_default();
                        for &gid in v {
                            if !entry.contains(&gid) {
                                entry.push(gid);
                            }
                        }
                    }
                    if is_stdlib_builtin_type(&orig) {
                        self.scope.stdlib_aliases.insert(target, orig);
                    }
                }
            }
            return;
        }

        // Resolve module template: either file import (`import "foo";`) or local module (`import M<...>;`).
        let mut guard_mod_id: Option<usize> = None;
        let mut guard_mod_file: Option<String> = None;
        let template = if name_tag == TokenTag::String {
            let spec = unquote_string(&raw_name);
            let from_file = self.units.file().clone();
            match self.loader.load(&from_file, &spec) {
                Ok((mod_file, mod_ast)) => {
                    let canonical = mod_file.name.clone();
                    if !self.instantiating_module_files.insert(canonical.clone()) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            name_span,
                            format!("cyclic module import `{spec}`"),
                        ));
                        return;
                    }
                    guard_mod_file = Some(canonical);
                    let stem = std::path::Path::new(&spec)
                        .file_stem()
                        .and_then(|s| s.to_str())
                        .unwrap_or(&spec)
                        .to_owned();
                    let mod_unit = self.units.push_owned(mod_file, mod_ast);
                    let prev = self.units.switch(mod_unit);
                    let top_decls: Vec<_> = self.units.ast().root_decls().collect();
                    // If the imported file defines a `module <stem>` (or a single module), instantiate it;
                    // otherwise instantiate the file's top-level declarations as a module.
                    let mut matching_mod = None;
                    for &d in &top_decls {
                        if self.units.ast().node_tag(d) == NodeTag::ModuleDecl {
                            let md = self.units.ast().module_decl(d);
                            let mname = self.text(md.name_token);
                            if mname == stem || matching_mod.is_none() {
                                let gparams =
                                    self.read_generic_params(md.gparams_start, md.gparams_end);
                                let body_decls: Vec<_> = self
                                    .units
                                    .ast()
                                    .extra_nodes(md.decls_start, md.decls_end)
                                    .collect();
                                matching_mod = Some(ModuleTemplate {
                                    unit: mod_unit,
                                    name: mname.to_owned(),
                                    gparams,
                                    decls: body_decls,
                                    outer_scope: ScopeEnv {
                                        has_stdlib: true,
                                        ..ScopeEnv::default()
                                    },
                                });
                            }
                        }
                    }
                    self.units.switch(prev);
                    matching_mod.unwrap_or_else(|| ModuleTemplate {
                        unit: mod_unit,
                        name: stem,
                        gparams: Vec::new(),
                        decls: top_decls,
                        outer_scope: ScopeEnv {
                            has_stdlib: true,
                            ..ScopeEnv::default()
                        },
                    })
                }
                Err(LoadError::NotFound(msg)) => {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        name_span,
                        msg,
                    ));
                    return;
                }
                Err(LoadError::ParseFailed(bag)) => {
                    for d in bag.diagnostics {
                        self.diagnostics.push(d);
                    }
                    return;
                }
            }
        } else if let Some(&mid) = self.scope.modules.get(&raw_name) {
            if !self.instantiating_modules.insert(mid) {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    name_span,
                    format!("cyclic module import `{raw_name}`"),
                ));
                return;
            }
            guard_mod_id = Some(mid);
            self.modules[mid].clone()
        } else {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                name_span,
                format!("unknown module `{raw_name}`"),
            ));
            return;
        };

        // Bind generic arguments against the importer's current scope.
        let Some(bound_generics) =
            self.resolve_generic_args(&template.name, &template.gparams, &garg_nodes, name_span)
        else {
            if let Some(mid) = guard_mod_id {
                self.instantiating_modules.remove(&mid);
            }
            if let Some(f) = guard_mod_file {
                self.instantiating_module_files.remove(&f);
            }
            return;
        };

        let mut mod_scope = template.outer_scope.clone();
        mod_scope.generics = bound_generics;
        mod_scope.has_stdlib |= self.scope.has_stdlib;

        let inst_id = self.next_mod_instance;
        self.next_mod_instance += 1;
        let mangle_prefix = match &prefix {
            Some(p) => p.clone(),
            None => format!("__m{inst_id}_"),
        };

        let saved_scope = std::mem::replace(&mut self.scope, mod_scope);
        let mod_exports =
            self.process_scope_decls(template.unit, &template.decls, Some(&mangle_prefix), true);
        self.scope = saved_scope;
        if let Some(mid) = guard_mod_id {
            self.instantiating_modules.remove(&mid);
        }
        if let Some(f) = guard_mod_file {
            self.instantiating_module_files.remove(&f);
        }

        // Bind imported items into the importer's scope (either selective `{ a as b } from` or all exports).
        let apply_prefix = |name: &str| -> String {
            match &prefix {
                Some(p) => format!("{p}{name}"),
                None => name.to_owned(),
            }
        };

        if selections.is_empty() {
            for (k, v) in mod_exports.enums {
                self.scope.enums.insert(apply_prefix(&k), v);
            }
            for (k, v) in mod_exports.structs {
                self.scope.structs.insert(apply_prefix(&k), v);
            }
            for (k, v) in mod_exports.generic_structs {
                self.scope.generic_structs.insert(apply_prefix(&k), v);
            }
            for (k, v) in mod_exports.type_aliases {
                self.scope.type_aliases.insert(apply_prefix(&k), v);
            }
            for (k, v) in mod_exports.new_types {
                self.scope.new_types.insert(apply_prefix(&k), v);
            }
            for (k, v) in mod_exports.generic_new_types {
                self.scope.generic_new_types.insert(apply_prefix(&k), v);
            }
            for (k, v) in mod_exports.contracts {
                self.scope.contracts.insert(apply_prefix(&k), v);
            }
            for (k, v) in mod_exports.ledger_fields {
                self.scope.ledger_fields.insert(apply_prefix(&k), v);
            }
            for (k, v) in mod_exports.witnesses {
                self.scope.witnesses.insert(apply_prefix(&k), v);
            }
            for (k, v) in mod_exports.circuits {
                let entry = self.scope.circuits.entry(apply_prefix(&k)).or_default();
                for cid in v {
                    if !entry.contains(&cid) {
                        entry.push(cid);
                    }
                }
            }
            for (k, v) in mod_exports.generic_circuits {
                let entry = self
                    .scope
                    .generic_circuits
                    .entry(apply_prefix(&k))
                    .or_default();
                for gid in v {
                    if !entry.contains(&gid) {
                        entry.push(gid);
                    }
                }
            }
            for (k, v) in mod_exports.modules {
                self.scope.modules.insert(apply_prefix(&k), v);
            }
            for (k, v) in mod_exports.stdlib_aliases {
                self.scope.stdlib_aliases.insert(apply_prefix(&k), v);
            }
        } else {
            for (orig, alias, ispan) in selections {
                let target = apply_prefix(&alias);
                let mut found = false;
                if let Some(canon) = mod_exports.stdlib_aliases.get(&orig) {
                    self.scope
                        .stdlib_aliases
                        .insert(target.clone(), canon.clone());
                    found = true;
                }
                if let Some(&v) = mod_exports.enums.get(&orig) {
                    self.scope.enums.insert(target.clone(), v);
                    found = true;
                }
                if let Some(&v) = mod_exports.structs.get(&orig) {
                    self.scope.structs.insert(target.clone(), v);
                    found = true;
                }
                if let Some(&v) = mod_exports.generic_structs.get(&orig) {
                    self.scope.generic_structs.insert(target.clone(), v);
                    found = true;
                }
                if let Some(&v) = mod_exports.type_aliases.get(&orig) {
                    self.scope.type_aliases.insert(target.clone(), v);
                    found = true;
                }
                if let Some(&v) = mod_exports.new_types.get(&orig) {
                    self.scope.new_types.insert(target.clone(), v);
                    found = true;
                }
                if let Some(&v) = mod_exports.generic_new_types.get(&orig) {
                    self.scope.generic_new_types.insert(target.clone(), v);
                    found = true;
                }
                if let Some(&v) = mod_exports.contracts.get(&orig) {
                    self.scope.contracts.insert(target.clone(), v);
                    found = true;
                }
                if let Some(&v) = mod_exports.ledger_fields.get(&orig) {
                    if let Some(&prev) = self.scope.ledger_fields.get(&target)
                        && prev != v
                    {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            ispan,
                            format!("duplicate imported ledger field binding `{target}`"),
                        ));
                    }
                    self.scope.ledger_fields.insert(target.clone(), v);
                    found = true;
                }
                if let Some(&v) = mod_exports.witnesses.get(&orig) {
                    self.scope.witnesses.insert(target.clone(), v);
                    found = true;
                }
                if let Some(v) = mod_exports.circuits.get(&orig) {
                    let entry = self.scope.circuits.entry(target.clone()).or_default();
                    for &cid in v {
                        if !entry.contains(&cid) {
                            entry.push(cid);
                        }
                    }
                    found = true;
                }
                if let Some(v) = mod_exports.generic_circuits.get(&orig) {
                    let entry = self
                        .scope
                        .generic_circuits
                        .entry(target.clone())
                        .or_default();
                    for &gid in v {
                        if !entry.contains(&gid) {
                            entry.push(gid);
                        }
                    }
                    found = true;
                }
                if let Some(&v) = mod_exports.modules.get(&orig) {
                    self.scope.modules.insert(target, v);
                    found = true;
                }
                if !found {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        ispan,
                        format!("module `{}` does not export `{orig}`", template.name),
                    ));
                }
            }
        }
    }

    fn resolve_generic_args(
        &mut self,
        owner: &str,
        gparams: &[GenericParamDef],
        arg_nodes: &[NodeIndex],
        span: Span,
    ) -> Option<GenericEnv> {
        if gparams.len() != arg_nodes.len() {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                span,
                format!(
                    "`{owner}` expects {} generic argument(s), found {}",
                    gparams.len(),
                    arg_nodes.len()
                ),
            ));
            return None;
        }
        let mut env = GenericEnv::default();
        for (i, gp) in gparams.iter().enumerate() {
            if gp.is_nat {
                let arg = arg_nodes[i];
                if self.units.ast().node_tag(arg) == NodeTag::TypeNat {
                    let raw = self.text(self.units.ast().node_main_token(arg)).to_owned();
                    if let Some(n) = compact_ast::parse_nat_u32(&raw) {
                        env.nats.insert(gp.name.clone(), n);
                    } else if let Some((_, bw)) = compact_ast::nat_literal_bit_width(&raw) {
                        env.big_nat_bits.insert(gp.name.clone(), bw);
                    } else {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            self.units.ast().node_span(arg),
                            format!("invalid numeric size `{raw}`"),
                        ));
                        return None;
                    }
                } else {
                    let n = self.expect_type_nat(arg_nodes, i, owner, span)?;
                    env.nats.insert(gp.name.clone(), n);
                }
            } else {
                let ty = self.resolve_type(arg_nodes[i])?;
                env.types.insert(gp.name.clone(), ty);
            }
        }
        Some(env)
    }

    fn resolve_generic_arg_vals(
        &mut self,
        owner: &str,
        gparams: &[GenericParamDef],
        arg_nodes: &[NodeIndex],
        span: Span,
    ) -> Option<(Vec<GenericArgVal>, GenericEnv)> {
        if gparams.len() != arg_nodes.len() {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                span,
                format!(
                    "`{owner}` expects {} generic argument(s), found {}",
                    gparams.len(),
                    arg_nodes.len()
                ),
            ));
            return None;
        }
        let mut vals = Vec::with_capacity(gparams.len());
        let mut env = GenericEnv::default();
        for (i, gp) in gparams.iter().enumerate() {
            if gp.is_nat {
                let arg = arg_nodes[i];
                if self.units.ast().node_tag(arg) == NodeTag::TypeNat {
                    let raw = self.text(self.units.ast().node_main_token(arg)).to_owned();
                    if let Some(n) = compact_ast::parse_nat_u32(&raw) {
                        vals.push(GenericArgVal::Nat(n));
                        env.nats.insert(gp.name.clone(), n);
                    } else if let Some((_, bw)) = compact_ast::nat_literal_bit_width(&raw) {
                        vals.push(GenericArgVal::BigNat(raw));
                        env.big_nat_bits.insert(gp.name.clone(), bw);
                    } else {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            self.units.ast().node_span(arg),
                            format!("invalid numeric size `{raw}`"),
                        ));
                        return None;
                    }
                } else {
                    let n = self.expect_type_nat(arg_nodes, i, owner, span)?;
                    vals.push(GenericArgVal::Nat(n));
                    env.nats.insert(gp.name.clone(), n);
                }
            } else {
                let ty = self.resolve_type(arg_nodes[i])?;
                vals.push(GenericArgVal::Type(ty.clone()));
                env.types.insert(gp.name.clone(), ty);
            }
        }
        Some((vals, env))
    }

    fn instantiate_generic_struct(
        &mut self,
        gid: usize,
        arg_nodes: &[NodeIndex],
        span: Span,
    ) -> Option<StructId> {
        let tmpl = self.generic_structs[gid].clone();
        let (vals, bound) =
            self.resolve_generic_arg_vals(&tmpl.name, &tmpl.gparams, arg_nodes, span)?;
        let key = (gid, vals.clone());
        if let Some(&sid) = self.generic_struct_cache.get(&key) {
            return Some(sid);
        }

        let sid = StructId(self.structs.len() as u32);
        let mangled = if vals.is_empty() {
            tmpl.name.clone()
        } else {
            format!("{}_{}", tmpl.name, self.format_generic_suffix(&vals))
        };
        self.structs.push(StructDecl {
            id: sid,
            name: mangled,
            fields: Vec::new(),
            exported: tmpl.exported,
            span: tmpl.span,
        });
        self.generic_struct_cache.insert(key, sid);

        let mut inst_scope = tmpl.scope.clone();
        inst_scope.generics.types.extend(bound.types);
        inst_scope.generics.nats.extend(bound.nats);
        inst_scope.generics.big_nat_bits.extend(bound.big_nat_bits);
        let prev_unit = self.units.switch(tmpl.unit);
        let prev_scope = std::mem::replace(&mut self.scope, inst_scope);

        let field_nodes: Vec<_> = self
            .units
            .ast()
            .extra_nodes(tmpl.fields_start, tmpl.fields_end)
            .collect();
        let mut fields = Vec::with_capacity(field_nodes.len());
        for fnode in field_nodes {
            let sf = self.units.ast().struct_field(fnode);
            let fname = self.text(sf.name_token).to_owned();
            if let Some(fty) = self.resolve_type(sf.type_node) {
                fields.push(StructField {
                    name: fname,
                    ty: fty,
                    span: self.units.ast().node_span(fnode),
                });
            }
        }
        self.structs[sid.0 as usize].fields = fields;

        self.scope = prev_scope;
        self.units.switch(prev_unit);
        Some(sid)
    }

    fn instantiate_generic_new_type(
        &mut self,
        gid: usize,
        arg_nodes: &[NodeIndex],
        span: Span,
    ) -> Option<NewTypeId> {
        let tmpl = self.generic_new_types[gid].clone();
        let (vals, bound) =
            self.resolve_generic_arg_vals(&tmpl.name, &tmpl.gparams, arg_nodes, span)?;
        let key = (gid, vals.clone());
        if let Some(&nid) = self.generic_new_type_cache.get(&key) {
            return Some(nid);
        }

        let nid = NewTypeId(self.new_types.len() as u32);
        let mangled = format!("{}_{}", tmpl.name, self.format_generic_suffix(&vals));
        self.new_types.push(NewTypeDecl {
            id: nid,
            name: mangled,
            inner: Type::unit(),
            exported: tmpl.exported,
            span: tmpl.span,
        });
        self.generic_new_type_cache.insert(key, nid);

        let mut inst_scope = tmpl.scope.clone();
        inst_scope.generics.types.extend(bound.types);
        inst_scope.generics.nats.extend(bound.nats);
        inst_scope.generics.big_nat_bits.extend(bound.big_nat_bits);
        let prev_unit = self.units.switch(tmpl.unit);
        let prev_scope = std::mem::replace(&mut self.scope, inst_scope);

        if let Some(inner) = self.resolve_type(tmpl.target_node) {
            self.new_types[nid.0 as usize].inner = inner;
        }

        self.scope = prev_scope;
        self.units.switch(prev_unit);
        Some(nid)
    }

    fn instantiate_generic_circuit(
        &mut self,
        gid: usize,
        arg_nodes: &[NodeIndex],
        span: Span,
    ) -> Option<CircuitId> {
        let tmpl = self.generic_circuits[gid].clone();
        let (vals, bound) =
            self.resolve_generic_arg_vals(&tmpl.name, &tmpl.gparams, arg_nodes, span)?;
        let key = (gid, vals.clone());
        if let Some(&cid) = self.generic_circuit_cache.get(&key) {
            return Some(cid);
        }

        let mut inst_scope = tmpl.scope.clone();
        inst_scope.generics.types.extend(bound.types);
        inst_scope.generics.nats.extend(bound.nats);
        inst_scope.generics.big_nat_bits.extend(bound.big_nat_bits);

        let prev_unit = self.units.switch(tmpl.unit);
        let prev_scope = std::mem::replace(&mut self.scope, inst_scope.clone());

        let params = self.resolve_params(tmpl.params_start, tmpl.params_end);
        let ret_type = self.resolve_type(tmpl.ret_type);

        self.scope = prev_scope;
        self.units.switch(prev_unit);

        let ret_type = ret_type?;
        let cid = CircuitId(self.circuit_sigs.len() as u32);
        let base_mangled = if vals.is_empty() {
            tmpl.name.clone()
        } else {
            format!("{}_{}", tmpl.name, self.format_generic_suffix(&vals))
        };
        let mangled = if self.circuit_sigs.iter().any(|s| s.name == base_mangled) {
            format!("{base_mangled}$ov{}", cid.0)
        } else {
            base_mangled
        };
        self.circuit_sigs.push(CircuitSig {
            id: cid,
            unit: tmpl.unit,
            scope: inst_scope,
            name: mangled,
            name_span: tmpl.span,
            params,
            ret_type,
            body_node: tmpl.body_node,
            exported: false,
            declared_pure: tmpl.declared_pure,
            span: tmpl.span,
        });
        self.generic_circuit_cache.insert(key, cid);
        Some(cid)
    }

    fn format_generic_suffix(&self, vals: &[GenericArgVal]) -> String {
        vals.iter()
            .map(|v| match v {
                GenericArgVal::Nat(n) => n.to_string(),
                GenericArgVal::BigNat(s) => format!("bn{}", s.len()),
                GenericArgVal::Type(ty) => self
                    .format_type(ty)
                    .chars()
                    .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
                    .collect::<String>(),
            })
            .collect::<Vec<_>>()
            .join("_")
    }

    fn register_enum(
        &mut self,
        node: NodeIndex,
        mangle_prefix: Option<&str>,
        is_module_instance: bool,
    ) -> Option<(String, EnumId, bool)> {
        let decl = self.units.ast().enum_decl(node);
        let local_name = self.text(decl.name_token).to_owned();
        let name_span = self.units.ast().token_span(decl.name_token);
        if self.scope.enums.contains_key(&local_name) {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                name_span,
                format!("duplicate enum `{local_name}`"),
            ));
            return None;
        }
        let mut variants = Vec::new();
        for vtok in self
            .units
            .ast()
            .extra_tokens(decl.variants_start, decl.variants_end)
        {
            let vname = self.text(vtok).to_owned();
            if variants.contains(&vname) {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    self.units.ast().token_span(vtok),
                    format!("duplicate variant `{vname}` in enum `{local_name}`"),
                ));
                continue;
            }
            variants.push(vname);
        }
        if variants.is_empty() {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                name_span,
                format!("enum `{local_name}` must declare at least one variant"),
            ));
            return None;
        }
        let id = EnumId(self.enums.len() as u32);
        self.enums.push(EnumDecl {
            id,
            name: mangle_name(mangle_prefix, &local_name),
            variants,
            exported: !is_module_instance && decl.exported,
            span: self.units.ast().node_span(node),
        });
        self.scope.enums.insert(local_name.clone(), id);
        Some((local_name, id, decl.exported))
    }

    fn register_struct_name(
        &mut self,
        node: NodeIndex,
        mangle_prefix: Option<&str>,
        is_module_instance: bool,
    ) -> Option<(String, StructId, bool)> {
        let decl = self.units.ast().struct_decl(node);
        let local_name = self.text(decl.name_token).to_owned();
        let name_span = self.units.ast().token_span(decl.name_token);
        if self.scope.structs.contains_key(&local_name)
            || self.scope.enums.contains_key(&local_name)
        {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                name_span,
                format!("duplicate type `{local_name}`"),
            ));
            return None;
        }
        let id = StructId(self.structs.len() as u32);
        self.structs.push(StructDecl {
            id,
            name: mangle_name(mangle_prefix, &local_name),
            fields: Vec::new(),
            exported: !is_module_instance && decl.exported,
            span: self.units.ast().node_span(node),
        });
        self.scope.structs.insert(local_name.clone(), id);
        Some((local_name, id, decl.exported))
    }

    fn populate_struct_fields(&mut self, node: NodeIndex, sid: StructId) {
        let decl = self.units.ast().struct_decl(node);
        let name = self.text(decl.name_token).to_owned();
        let field_nodes: Vec<_> = self
            .units
            .ast()
            .extra_nodes(decl.fields_start, decl.fields_end)
            .collect();
        let mut fields = Vec::with_capacity(field_nodes.len());
        let mut seen = HashMap::new();
        for fnode in field_nodes {
            let sf = self.units.ast().struct_field(fnode);
            let fname = self.text(sf.name_token).to_owned();
            if seen.contains_key(&fname) {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    self.units.ast().token_span(sf.name_token),
                    format!("duplicate field `{fname}` in struct `{name}`"),
                ));
                continue;
            }
            let Some(fty) = self.resolve_type(sf.type_node) else {
                continue;
            };
            seen.insert(fname.clone(), ());
            fields.push(StructField {
                name: fname,
                ty: fty,
                span: self.units.ast().node_span(fnode),
            });
        }
        self.structs[sid.0 as usize].fields = fields;
    }

    fn is_adt_type_node(&self, node: NodeIndex) -> bool {
        match self.units.ast().node_tag(node) {
            NodeTag::TypeNamed => {
                let name = self.text(self.units.ast().node_main_token(node));
                if matches!(name, "Counter" | "Kernel") {
                    return true;
                }
                if let Some(&nid) = self.scope.new_types.get(name) {
                    return self.new_type_adts.contains_key(&nid);
                }
                false
            }
            NodeTag::TypeGeneric => {
                let name = self.text(self.units.ast().node_main_token(node));
                matches!(
                    name,
                    "Set" | "List" | "Map" | "MerkleTree" | "HistoricMerkleTree"
                )
            }
            _ => false,
        }
    }

    fn resolve_ledger_adt(&mut self, node: NodeIndex) -> Option<LedgerAdt> {
        match self.units.ast().node_tag(node) {
            NodeTag::TypeNamed => {
                let name = self.text(self.units.ast().node_main_token(node)).to_owned();
                if name == "Counter" {
                    return Some(LedgerAdt::Counter);
                }
                if name == "Kernel" {
                    return Some(LedgerAdt::Kernel);
                }
                if let Some(&nid) = self.scope.new_types.get(&name)
                    && let Some(adt) = self.new_type_adts.get(&nid).cloned()
                {
                    return Some(adt);
                }
                if let Some(&aid) = self.scope.type_aliases.get(&name) {
                    return self.expand_type_alias_as_adt(
                        aid,
                        &[],
                        self.units.ast().node_span(node),
                    );
                }
                let ty = self.resolve_type(node)?;
                Some(LedgerAdt::Cell(Box::new(ty)))
            }
            NodeTag::TypeGeneric => {
                let adt_name = self.text(self.units.ast().node_main_token(node)).to_owned();
                let data = self.units.ast().node_data(node);
                let arg_nodes: Vec<_> = self.units.ast().extra_nodes(data.lhs, data.rhs).collect();
                match adt_name.as_str() {
                    "Set" => {
                        if arg_nodes.len() != 1 {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                self.units.ast().node_span(node),
                                format!("`Set` expects 1 type argument, found {}", arg_nodes.len()),
                            ));
                            return None;
                        }
                        let elem_ty = self.resolve_type(arg_nodes[0])?;
                        Some(LedgerAdt::Set(Box::new(elem_ty)))
                    }
                    "List" => {
                        if arg_nodes.len() != 1 {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                self.units.ast().node_span(node),
                                format!(
                                    "`List` expects 1 type argument, found {}",
                                    arg_nodes.len()
                                ),
                            ));
                            return None;
                        }
                        let elem_ty = self.resolve_type(arg_nodes[0])?;
                        Some(LedgerAdt::List(Box::new(elem_ty)))
                    }
                    "Map" => {
                        if arg_nodes.len() != 2 {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                self.units.ast().node_span(node),
                                format!(
                                    "`Map` expects 2 type arguments (key, value), found {}",
                                    arg_nodes.len()
                                ),
                            ));
                            return None;
                        }
                        let key_ty = self.resolve_type(arg_nodes[0])?;
                        let val_adt = self.resolve_ledger_adt(arg_nodes[1])?;
                        Some(LedgerAdt::Map {
                            key: Box::new(key_ty),
                            value: Box::new(val_adt),
                        })
                    }
                    "MerkleTree" | "HistoricMerkleTree" => {
                        if arg_nodes.len() != 2 {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                self.units.ast().node_span(node),
                                format!(
                                    "`{adt_name}` expects 2 type arguments (depth, element type), found {}",
                                    arg_nodes.len()
                                ),
                            ));
                            return None;
                        }
                        let depth = self.expect_type_nat(
                            &arg_nodes,
                            0,
                            &adt_name,
                            self.units.ast().node_span(node),
                        )?;
                        let elem_ty = self.resolve_type(arg_nodes[1])?;
                        if adt_name == "HistoricMerkleTree" {
                            Some(LedgerAdt::HistoricMerkleTree {
                                depth,
                                value: Box::new(elem_ty),
                            })
                        } else {
                            Some(LedgerAdt::MerkleTree {
                                depth,
                                value: Box::new(elem_ty),
                            })
                        }
                    }
                    _ => {
                        if let Some(&aid) = self.scope.type_aliases.get(&adt_name) {
                            return self.expand_type_alias_as_adt(
                                aid,
                                &arg_nodes,
                                self.units.ast().node_span(node),
                            );
                        }
                        let ty = self.resolve_type(node)?;
                        Some(LedgerAdt::Cell(Box::new(ty)))
                    }
                }
            }
            _ => {
                let ty = self.resolve_type(node)?;
                Some(LedgerAdt::Cell(Box::new(ty)))
            }
        }
    }

    fn expand_type_alias_as_adt(
        &mut self,
        aid: usize,
        arg_nodes: &[NodeIndex],
        span: Span,
    ) -> Option<LedgerAdt> {
        if !self.resolving_aliases.insert(aid) {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                span,
                "cyclic type alias definition",
            ));
            return None;
        }
        let tmpl = self.type_aliases[aid].clone();
        let bound = self.resolve_generic_args("type alias", &tmpl.gparams, arg_nodes, span);
        let result = if let Some(bound) = bound {
            let mut inst_scope = tmpl.scope.clone();
            inst_scope.generics.types.extend(bound.types);
            inst_scope.generics.nats.extend(bound.nats);
            inst_scope.generics.big_nat_bits.extend(bound.big_nat_bits);
            let prev_unit = self.units.switch(tmpl.unit);
            let prev_scope = std::mem::replace(&mut self.scope, inst_scope);
            let adt = self.resolve_ledger_adt(tmpl.target_node);
            self.scope = prev_scope;
            self.units.switch(prev_unit);
            adt
        } else {
            None
        };
        self.resolving_aliases.remove(&aid);
        result
    }

    fn register_ledger(
        &mut self,
        node: NodeIndex,
        mangle_prefix: Option<&str>,
        is_module_instance: bool,
    ) -> Option<(String, LedgerFieldId, bool)> {
        let decl = self.units.ast().ledger_decl(node);
        let local_name = self.text(decl.name_token).to_owned();
        let name_span = self.units.ast().token_span(decl.name_token);

        if self.scope.ledger_fields.contains_key(&local_name) {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                name_span,
                format!("duplicate ledger field `{local_name}`"),
            ));
            return None;
        }

        let adt = self.resolve_ledger_adt(decl.type_node)?;
        let id = LedgerFieldId(self.ledger_fields.len() as u32);
        let path = if matches!(adt, LedgerAdt::Kernel) {
            Vec::new()
        } else {
            let slot = self.next_ledger_slot;
            self.next_ledger_slot += 1;
            vec![slot]
        };
        self.ledger_fields.push(LedgerField {
            id,
            name: mangle_name(mangle_prefix, &local_name),
            adt,
            path,
            exported: !is_module_instance && decl.exported,
            sealed: decl.sealed,
            span: self.units.ast().node_span(node),
        });
        self.scope.ledger_fields.insert(local_name.clone(), id);
        Some((local_name, id, decl.exported))
    }

    fn register_witness(
        &mut self,
        node: NodeIndex,
        mangle_prefix: Option<&str>,
        is_module_instance: bool,
    ) -> Option<(String, WitnessId, bool)> {
        let decl = self.units.ast().witness_decl(node);
        let local_name = self.text(decl.name_token).to_owned();
        let name_span = self.units.ast().token_span(decl.name_token);

        if self.scope.witnesses.contains_key(&local_name) {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                name_span,
                format!("duplicate witness `{local_name}`"),
            ));
            return None;
        }

        let params = self.resolve_params(decl.params_start, decl.params_end);
        let ret_type = self.resolve_type(decl.ret_type)?;

        let id = WitnessId(self.witnesses.len() as u32);
        self.scope.witnesses.insert(local_name.clone(), id);
        self.witnesses.push(WitnessDecl {
            id,
            name: mangle_name(mangle_prefix, &local_name),
            params,
            ret_type,
            exported: !is_module_instance && decl.exported,
            span: self.units.ast().node_span(node),
        });
        Some((local_name, id, decl.exported))
    }

    fn register_circuit_sig(
        &mut self,
        unit: UnitId,
        node: NodeIndex,
        mangle_prefix: Option<&str>,
        is_module_instance: bool,
    ) -> Option<(String, CircuitId, bool)> {
        let decl = self.units.ast().circuit_decl(node);
        let local_name = self.text(decl.name_token).to_owned();
        let name_span = self.units.ast().token_span(decl.name_token);

        let params = self.resolve_params(decl.params_start, decl.params_end);
        let ret_type = self.resolve_type(decl.ret_type)?;
        let param_tys: Vec<Type> = params.iter().map(|p| p.ty.clone()).collect();

        let existing_count = if let Some(existing) = self.scope.circuits.get(&local_name) {
            for &prev_cid in existing {
                let prev = &self.circuit_sigs[prev_cid.0 as usize];
                if prev.unit != self.units.cur {
                    continue;
                }
                let prev_tys: Vec<Type> = prev.params.iter().map(|p| p.ty.clone()).collect();
                if prev_tys == param_tys || (!is_module_instance && decl.exported && prev.exported)
                {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        name_span,
                        format!("duplicate circuit `{local_name}` with identical parameter types"),
                    ));
                    return None;
                }
            }
            existing.len()
        } else {
            0
        };

        let id = CircuitId(self.circuit_sigs.len() as u32);
        self.scope
            .circuits
            .entry(local_name.clone())
            .or_default()
            .push(id);
        let base_name = mangle_name(mangle_prefix, &local_name);
        let hir_name = if existing_count > 0 && (is_module_instance || !decl.exported) {
            format!("{base_name}$ov{}", id.0)
        } else {
            base_name
        };
        self.circuit_sigs.push(CircuitSig {
            id,
            unit,
            scope: ScopeEnv::default(),
            name: hir_name,
            name_span,
            params,
            ret_type,
            body_node: decl.body,
            exported: !is_module_instance && decl.exported,
            declared_pure: decl.pure,
            span: self.units.ast().node_span(node),
        });
        Some((local_name, id, decl.exported))
    }

    fn resolve_params(&mut self, start: u32, end: u32) -> Vec<Param> {
        let mut params = Vec::new();
        let mut seen = HashMap::new();
        let param_nodes: Vec<_> = self.units.ast().extra_nodes(start, end).collect();
        for pnode in param_nodes {
            let p = self.units.ast().param(pnode);
            let pname = self.text(p.name_token).to_owned();
            if seen.contains_key(&pname) {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    self.units.ast().token_span(p.name_token),
                    format!("duplicate parameter `{pname}`"),
                ));
                continue;
            }
            let Some(pty) = self.resolve_type(p.type_node) else {
                continue;
            };
            let pid = ParamId(params.len() as u32);
            seen.insert(pname.clone(), pid);
            params.push(Param {
                id: pid,
                name: pname,
                ty: pty,
                span: self.units.ast().node_span(pnode),
            });
        }
        params
    }

    fn resolve_type(&mut self, node: NodeIndex) -> Option<Type> {
        match self.units.ast().node_tag(node) {
            NodeTag::TypeNamed => {
                let tok = self.units.ast().node_main_token(node);
                let raw_name = self.text(tok).to_owned();
                if let Some(ty) = self.scope.generics.types.get(&raw_name).cloned() {
                    return Some(ty);
                }
                let name = self
                    .scope
                    .stdlib_aliases
                    .get(&raw_name)
                    .cloned()
                    .unwrap_or(raw_name);
                match name.as_str() {
                    "Field" => Some(Type::Field),
                    "Boolean" => Some(Type::Boolean),
                    "JubjubScalar" => Some(Type::CurveField(CurveFieldKind::JubjubScalar)),
                    "JubjubPoint" => Some(Type::CurvePoint(CurveKind::Jubjub)),
                    "Secp256k1Base" => Some(Type::CurveField(CurveFieldKind::Secp256k1Base)),
                    "Secp256k1Scalar" => Some(Type::CurveField(CurveFieldKind::Secp256k1Scalar)),
                    "Secp256k1Point" => Some(Type::CurvePoint(CurveKind::Secp256k1)),
                    "Secp256r1Base" => Some(Type::CurveField(CurveFieldKind::Secp256r1Base)),
                    "Secp256r1Scalar" => Some(Type::CurveField(CurveFieldKind::Secp256r1Scalar)),
                    "Secp256r1Point" => Some(Type::CurvePoint(CurveKind::Secp256r1)),
                    "Curve25519Base" => Some(Type::CurveField(CurveFieldKind::Curve25519Base)),
                    "Curve25519Scalar" => Some(Type::CurveField(CurveFieldKind::Curve25519Scalar)),
                    "Curve25519Point" => Some(Type::CurvePoint(CurveKind::Curve25519)),
                    "MerkleTreeDigest" => Some(Type::MerkleTreeDigest),
                    "MerkleTreePathEntry" => Some(Type::MerkleTreePathEntry),
                    _ => {
                        if let Some(&eid) = self.scope.enums.get(&name) {
                            Some(Type::Enum(eid))
                        } else if let Some(&sid) = self.scope.structs.get(&name) {
                            Some(Type::Struct(sid))
                        } else if let Some(&gid) = self.scope.generic_structs.get(&name)
                            && self.generic_structs[gid].gparams.is_empty()
                        {
                            let sid = self.instantiate_generic_struct(
                                gid,
                                &[],
                                self.units.ast().token_span(tok),
                            )?;
                            Some(Type::Struct(sid))
                        } else if let Some(&nid) = self.scope.new_types.get(&name) {
                            Some(Type::NewType(nid))
                        } else if let Some(&cid) = self.scope.contracts.get(&name) {
                            Some(Type::Contract(cid))
                        } else if let Some(&aid) = self.scope.type_aliases.get(&name) {
                            self.expand_type_alias(aid, &[], self.units.ast().token_span(tok))
                        } else {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                self.units.ast().token_span(tok),
                                format!("unknown type `{name}`"),
                            ));
                            None
                        }
                    }
                }
            }
            NodeTag::TypeGeneric => {
                let tok = self.units.ast().node_main_token(node);
                let raw_name = self.text(tok).to_owned();
                let name = self
                    .scope
                    .stdlib_aliases
                    .get(&raw_name)
                    .cloned()
                    .unwrap_or(raw_name);
                let span = self.units.ast().node_span(node);
                let data = self.units.ast().node_data(node);
                let arg_nodes: Vec<_> = self.units.ast().extra_nodes(data.lhs, data.rhs).collect();
                match name.as_str() {
                    "Bytes" => {
                        let len = self.expect_type_nat(&arg_nodes, 0, "Bytes", span)?;
                        Some(Type::Bytes(len))
                    }
                    "Uint" => {
                        if arg_nodes.len() != 1 {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                span,
                                format!(
                                    "`Uint` expects 1 size or range argument, found {}",
                                    arg_nodes.len()
                                ),
                            ));
                            return None;
                        }
                        let arg0 = arg_nodes[0];
                        if self.units.ast().node_tag(arg0) == NodeTag::TypeRange {
                            let rdata = self.units.ast().node_data(arg0);
                            let lo_node = NodeIndex(rdata.lhs);
                            let hi_node = NodeIndex(rdata.rhs);
                            let lo_val = self.expect_type_nat(&[lo_node], 0, "Uint", span)?;
                            if lo_val != 0 {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    self.units.ast().node_span(lo_node),
                                    format!("`Uint` range lower bound must be 0, found {lo_val}"),
                                ));
                                return None;
                            }
                            let bits = if self.units.ast().node_tag(hi_node) == NodeTag::TypeNamed {
                                let hname = self.text(self.units.ast().node_main_token(hi_node));
                                if let Some(&n) = self.scope.generics.nats.get(hname) {
                                    32 - n.leading_zeros()
                                } else if let Some(&bw) =
                                    self.scope.generics.big_nat_bits.get(hname)
                                {
                                    bw
                                } else {
                                    self.diagnostics.push(CompactDiagnostic::error(
                                        self.units.file(),
                                        self.units.ast().node_span(hi_node),
                                        "`Uint` range upper bound must be a numeric literal or generic size",
                                    ));
                                    return None;
                                }
                            } else if self.units.ast().node_tag(hi_node) == NodeTag::TypeNat {
                                let raw = self
                                    .text(self.units.ast().node_main_token(hi_node))
                                    .to_owned();
                                match compact_ast::nat_literal_bit_width(&raw) {
                                    Some((_is_zero, bw)) => bw,
                                    None => {
                                        self.diagnostics.push(CompactDiagnostic::error(
                                            self.units.file(),
                                            self.units.ast().node_span(hi_node),
                                            format!("invalid numeric bound `{raw}`"),
                                        ));
                                        return None;
                                    }
                                }
                            } else {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    self.units.ast().node_span(hi_node),
                                    "`Uint` range upper bound must be a numeric literal",
                                ));
                                return None;
                            };
                            if bits > 248 {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    span,
                                    format!(
                                        "`Uint` range exceeds maximum 248-bit width ({bits} bits)"
                                    ),
                                ));
                                return None;
                            }
                            Some(Type::Uint(bits))
                        } else {
                            let bits = self.expect_type_nat(&arg_nodes, 0, "Uint", span)?;
                            if bits > 248 {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    span,
                                    format!("`Uint<{bits}>` exceeds maximum bit width 248"),
                                ));
                                return None;
                            }
                            Some(Type::Uint(bits))
                        }
                    }
                    "Opaque" => {
                        if arg_nodes.len() != 1
                            || self.units.ast().node_tag(arg_nodes[0]) != NodeTag::TypeString
                        {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                span,
                                "`Opaque` expects 1 string literal type argument (e.g. `Opaque<\"string\">`)",
                            ));
                            return None;
                        }
                        let ts_ty = unquote_string(
                            self.text(self.units.ast().node_main_token(arg_nodes[0])),
                        );
                        Some(Type::Opaque(ts_ty))
                    }
                    "Vector" => {
                        if arg_nodes.len() != 2 {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                span,
                                format!(
                                    "`Vector` expects 2 type arguments, found {}",
                                    arg_nodes.len()
                                ),
                            ));
                            return None;
                        }
                        let len = self.expect_type_nat(&arg_nodes, 0, "Vector", span)?;
                        if len > 16_777_216 {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                span,
                                format!(
                                    "`Vector` length {len} exceeds maximum allowed length 16777216"
                                ),
                            ));
                            return None;
                        }
                        let elem = self.resolve_type(arg_nodes[1])?;
                        Some(Type::Vector(len, Box::new(elem)))
                    }
                    "Maybe" => {
                        if !self.scope.has_stdlib {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                self.units.ast().token_span(tok),
                                "unknown type `Maybe` (missing `import CompactStandardLibrary;`)",
                            ));
                            return None;
                        }
                        if arg_nodes.len() != 1 {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                span,
                                format!(
                                    "`Maybe` expects 1 type argument, found {}",
                                    arg_nodes.len()
                                ),
                            ));
                            return None;
                        }
                        let inner = self.resolve_type(arg_nodes[0])?;
                        Some(Type::Maybe(Box::new(inner)))
                    }
                    "Either" => {
                        if !self.scope.has_stdlib {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                self.units.ast().token_span(tok),
                                "unknown type `Either` (missing `import CompactStandardLibrary;`)",
                            ));
                            return None;
                        }
                        if arg_nodes.len() != 2 {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                span,
                                format!(
                                    "`Either` expects 2 type arguments, found {}",
                                    arg_nodes.len()
                                ),
                            ));
                            return None;
                        }
                        let left = self.resolve_type(arg_nodes[0])?;
                        let right = self.resolve_type(arg_nodes[1])?;
                        Some(Type::Either(Box::new(left), Box::new(right)))
                    }
                    "MerkleTreePath" => {
                        if !self.scope.has_stdlib {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                self.units.ast().token_span(tok),
                                "unknown type `MerkleTreePath` (missing `import CompactStandardLibrary;`)",
                            ));
                            return None;
                        }
                        if arg_nodes.len() != 2 {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                span,
                                format!(
                                    "`MerkleTreePath` expects 2 type arguments, found {}",
                                    arg_nodes.len()
                                ),
                            ));
                            return None;
                        }
                        let depth = self.expect_type_nat(&arg_nodes, 0, "MerkleTreePath", span)?;
                        let leaf = self.resolve_type(arg_nodes[1])?;
                        Some(Type::MerkleTreePath(depth, Box::new(leaf)))
                    }
                    _ => {
                        if let Some(&gid) = self.scope.generic_structs.get(&name) {
                            let sid = self.instantiate_generic_struct(gid, &arg_nodes, span)?;
                            Some(Type::Struct(sid))
                        } else if let Some(&gid) = self.scope.generic_new_types.get(&name) {
                            let nid = self.instantiate_generic_new_type(gid, &arg_nodes, span)?;
                            Some(Type::NewType(nid))
                        } else if let Some(&aid) = self.scope.type_aliases.get(&name) {
                            self.expand_type_alias(aid, &arg_nodes, span)
                        } else {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                self.units.ast().token_span(tok),
                                format!("unknown generic type `{name}`"),
                            ));
                            None
                        }
                    }
                }
            }
            NodeTag::TypeTuple => {
                let data = self.units.ast().node_data(node);
                let elem_nodes: Vec<_> = self.units.ast().extra_nodes(data.lhs, data.rhs).collect();
                let mut elems = Vec::with_capacity(elem_nodes.len());
                for enode in elem_nodes {
                    elems.push(self.resolve_type(enode)?);
                }
                Some(Type::Tuple(elems))
            }
            _ => None,
        }
    }

    fn expand_type_alias(
        &mut self,
        aid: usize,
        arg_nodes: &[NodeIndex],
        span: Span,
    ) -> Option<Type> {
        if !self.resolving_aliases.insert(aid) {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                span,
                "cyclic type alias definition",
            ));
            return None;
        }
        let tmpl = self.type_aliases[aid].clone();
        let bound = self.resolve_generic_args("type alias", &tmpl.gparams, arg_nodes, span);
        let result = if let Some(bound) = bound {
            let mut inst_scope = tmpl.scope.clone();
            inst_scope.generics.types.extend(bound.types);
            inst_scope.generics.nats.extend(bound.nats);
            inst_scope.generics.big_nat_bits.extend(bound.big_nat_bits);
            let prev_unit = self.units.switch(tmpl.unit);
            let prev_scope = std::mem::replace(&mut self.scope, inst_scope);
            let ty = self.resolve_type(tmpl.target_node);
            self.scope = prev_scope;
            self.units.switch(prev_unit);
            ty
        } else {
            None
        };
        self.resolving_aliases.remove(&aid);
        result
    }

    fn expect_type_nat(
        &mut self,
        args: &[NodeIndex],
        index: usize,
        type_name: &str,
        span: Span,
    ) -> Option<u32> {
        let Some(&arg) = args.get(index) else {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                span,
                format!("`{type_name}` is missing a numeric size argument"),
            ));
            return None;
        };
        if self.units.ast().node_tag(arg) == NodeTag::TypeNamed {
            let name = self.text(self.units.ast().node_main_token(arg));
            if let Some(&n) = self.scope.generics.nats.get(name) {
                return Some(n);
            }
        }
        if self.units.ast().node_tag(arg) != NodeTag::TypeNat {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                self.units.ast().node_span(arg),
                format!("`{type_name}` size argument must be a numeric literal"),
            ));
            return None;
        }
        let raw = self.text(self.units.ast().node_main_token(arg)).to_owned();
        match compact_ast::parse_nat_u32(&raw) {
            Some(n) => Some(n),
            None => {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    self.units.ast().node_span(arg),
                    format!("invalid numeric size `{raw}`"),
                ));
                None
            }
        }
    }

    fn struct_fields_of(&self, ty: &Type) -> Option<Vec<(String, Type)>> {
        match self.underlying_type(ty) {
            Type::Struct(id) => Some(
                self.structs[id.0 as usize]
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

    fn format_type(&self, ty: &Type) -> String {
        match ty {
            Type::Field => "Field".into(),
            Type::Boolean => "Boolean".into(),
            Type::Uint(bits) => format!("Uint<{bits}>"),
            Type::Bytes(len) => format!("Bytes<{len}>"),
            Type::CurveField(f) => f.type_name().into(),
            Type::CurvePoint(c) => c.point_type_name().into(),
            Type::Opaque(ts_ty) => format!("Opaque<\"{ts_ty}\">"),
            Type::Vector(len, elem) => format!("Vector<{len}, {}>", self.format_type(elem)),
            Type::Tuple(elems) => {
                let inner: Vec<_> = elems.iter().map(|e| self.format_type(e)).collect();
                format!("[{}]", inner.join(", "))
            }
            Type::Enum(id) => self.enums[id.0 as usize].name.clone(),
            Type::Struct(id) => self.structs[id.0 as usize].name.clone(),
            Type::NewType(id) => self.new_types[id.0 as usize].name.clone(),
            Type::Contract(id) => self.contracts[id.0 as usize].name.clone(),
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

    fn populate_contract_circuits(&mut self, node: NodeIndex, cid: ContractId) {
        let decl = self.units.ast().contract_decl(node);
        let cc_nodes: Vec<_> = self
            .units
            .ast()
            .extra_nodes(decl.circuits_start, decl.circuits_end)
            .collect();
        let mut circuits = Vec::with_capacity(cc_nodes.len());
        let mut seen = HashSet::new();
        for cc_node in cc_nodes {
            let cc = self.units.ast().contract_circuit(cc_node);
            let cname = self.text(cc.name_token).to_owned();
            let cspan = self.units.ast().node_span(cc_node);
            if !seen.insert(cname.clone()) {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    self.units.ast().token_span(cc.name_token),
                    format!("duplicate circuit `{cname}` in contract declaration"),
                ));
                continue;
            }
            let params = self.resolve_params(cc.params_start, cc.params_end);
            let Some(ret_type) = self.resolve_type(cc.ret_type) else {
                continue;
            };
            circuits.push(ContractCircuitSig {
                name: cname,
                pure: cc.pure,
                params,
                ret_type,
                span: cspan,
            });
        }
        self.contracts[cid.0 as usize].circuits = circuits;
    }

    fn serialized_byte_len(&self, ty: &Type) -> Option<u32> {
        match self.underlying_type(ty) {
            Type::Boolean => Some(1),
            Type::Field | Type::CurveField(_) => Some(32),
            Type::Uint(bits) => {
                if *bits == 0 {
                    Some(0)
                } else {
                    Some((*bits).div_ceil(8))
                }
            }
            Type::Bytes(len) => Some(*len),
            Type::Enum(id) => {
                let count = self.enums[id.0 as usize].variants.len() as u32;
                let maxval = count.saturating_sub(1);
                if maxval == 0 {
                    Some(0)
                } else {
                    Some((u32::BITS - maxval.leading_zeros()).div_ceil(8))
                }
            }
            Type::Vector(len, elem) => self.serialized_byte_len(elem)?.checked_mul(*len),
            Type::Tuple(elems) => {
                let mut total = 0u32;
                for e in elems {
                    total = total.checked_add(self.serialized_byte_len(e)?)?;
                }
                Some(total)
            }
            Type::Struct(_)
            | Type::Maybe(_)
            | Type::Either(_, _)
            | Type::MerkleTreeDigest
            | Type::MerkleTreePathEntry
            | Type::MerkleTreePath(_, _) => {
                let mut total = 0u32;
                for (_, fty) in self.struct_fields_of(ty)? {
                    total = total.checked_add(self.serialized_byte_len(&fty)?)?;
                }
                Some(total)
            }
            Type::CurvePoint(_) | Type::Contract(_) | Type::Opaque(_) => None,
            Type::NewType(_) => unreachable!("underlying_type peeled all NewType layers"),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn check_contract_call(
        &mut self,
        cid: ContractId,
        receiver: Expr,
        method_name: &str,
        method_span: Span,
        arg_nodes: &[NodeIndex],
        call_span: Span,
        scope: &HashMap<String, ValueBinding>,
    ) -> Option<Expr> {
        let decl = self.contracts[cid.0 as usize].clone();
        let Some(sig) = decl.circuits.iter().find(|c| c.name == method_name) else {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                method_span,
                format!("contract `{}` has no circuit `{method_name}`", decl.name),
            ));
            return None;
        };
        if arg_nodes.len() != sig.params.len() {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                call_span,
                format!(
                    "`{}.{method_name}` expects {} argument(s), found {}",
                    decl.name,
                    sig.params.len(),
                    arg_nodes.len()
                ),
            ));
            return None;
        }
        let mut args = Vec::with_capacity(arg_nodes.len());
        for (&anode, param) in arg_nodes.iter().zip(&sig.params) {
            let mut arg = self.check_expr(anode, scope, Some(&param.ty))?;
            if !self.coerce_or_check(&mut arg, &param.ty) {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    arg.span,
                    format!(
                        "`{}.{method_name}` argument `{}` mismatch: expected `{}`, found `{}`",
                        decl.name,
                        param.name,
                        self.format_type(&param.ty),
                        self.format_type(&arg.ty)
                    ),
                ));
                return None;
            }
            args.push(arg);
        }
        Some(Expr {
            kind: ExprKind::ContractCall {
                contract: cid,
                receiver: Box::new(receiver),
                method: method_name.to_owned(),
                args,
            },
            ty: sig.ret_type.clone(),
            span: call_span,
        })
    }

    fn check_constructor(&mut self, node: NodeIndex) {
        let decl = self.units.ast().constructor_decl(node);
        let params = self.resolve_params(decl.params_start, decl.params_end);
        let mut scope: HashMap<String, ValueBinding> = HashMap::new();
        for p in &params {
            scope.insert(p.name.clone(), ValueBinding::Param(p.id, p.ty.clone()));
        }
        self.next_local = 0;
        let ret_unit = Type::unit();
        let body = self.check_stmt_list(decl.body, &scope, &ret_unit);
        self.constructor = Some(Constructor {
            params,
            body,
            span: self.units.ast().node_span(node),
        });
    }

    fn check_circuit_body(&mut self, sig_idx: usize) {
        let id = self.circuit_sigs[sig_idx].id;
        let unit = self.circuit_sigs[sig_idx].unit;
        let saved_scope = self.circuit_sigs[sig_idx].scope.clone();
        let name = self.circuit_sigs[sig_idx].name.clone();
        let params = self.circuit_sigs[sig_idx].params.clone();
        let ret_type = self.circuit_sigs[sig_idx].ret_type.clone();
        let body_node = self.circuit_sigs[sig_idx].body_node;
        let exported = self.circuit_sigs[sig_idx].exported;
        let span = self.circuit_sigs[sig_idx].span;

        let prev_unit = self.units.switch(unit);
        let prev_scope = std::mem::replace(&mut self.scope, saved_scope);

        let mut scope: HashMap<String, ValueBinding> = HashMap::new();
        for p in &params {
            scope.insert(p.name.clone(), ValueBinding::Param(p.id, p.ty.clone()));
        }
        self.next_local = 0;

        let body = self.check_stmt_list(body_node, &scope, &ret_type);

        self.scope = prev_scope;
        self.units.switch(prev_unit);

        self.circuits.push(Circuit {
            id,
            name,
            params,
            ret_type,
            body,
            exported,
            pure: true,
            proof: false,
            span,
        });
    }

    fn ast_stmt_always_returns(&self, node: NodeIndex) -> bool {
        match self.units.ast().node_tag(node) {
            NodeTag::ReturnStmt => true,
            NodeTag::Block => {
                let d = self.units.ast().node_data(node);
                let stmts: Vec<_> = self.units.ast().extra_nodes(d.lhs, d.rhs).collect();
                stmts.into_iter().any(|s| self.ast_stmt_always_returns(s))
            }
            NodeTag::IfStmt => {
                let stmt = self.units.ast().if_stmt(node);
                let Some(eb) = stmt.else_branch else {
                    return false;
                };
                self.ast_stmt_always_returns(stmt.then_branch) && self.ast_stmt_always_returns(eb)
            }
            _ => false,
        }
    }

    fn check_stmt_list(
        &mut self,
        node: NodeIndex,
        scope: &HashMap<String, ValueBinding>,
        expected_ret: &Type,
    ) -> Vec<Stmt> {
        let mut inner_scope = scope.clone();
        let mut stmts = Vec::new();
        self.block_consts.push(HashSet::new());
        if self.units.ast().node_tag(node) == NodeTag::Block {
            let block_data = self.units.ast().node_data(node);
            let stmt_nodes: Vec<_> = self
                .units
                .ast()
                .extra_nodes(block_data.lhs, block_data.rhs)
                .collect();
            let mut terminated = false;
            for snode in stmt_nodes {
                if terminated {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        self.units.ast().node_span(snode),
                        "unreachable statement after return",
                    ));
                }
                self.check_stmt(snode, &mut inner_scope, expected_ret, &mut stmts);
                if self.ast_stmt_always_returns(snode) {
                    terminated = true;
                }
            }
        } else {
            self.check_stmt(node, &mut inner_scope, expected_ret, &mut stmts);
        }
        self.block_consts.pop();
        stmts
    }

    fn bind_pattern(
        &mut self,
        pat: NodeIndex,
        val: Expr,
        scope: &mut HashMap<String, ValueBinding>,
        out: &mut Vec<Stmt>,
        stmt_span: Span,
    ) {
        let pat_span = self.units.ast().node_span(pat);
        match self.units.ast().node_tag(pat) {
            NodeTag::PatIdent => {
                let name = self.text(self.units.ast().node_main_token(pat)).to_owned();
                if let Some(current) = self.block_consts.last_mut()
                    && !current.insert(name.clone())
                {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        pat_span,
                        format!("duplicate `const` binding `{name}` in the same block"),
                    ));
                }
                let local = self.alloc_local();
                let ty = val.ty.clone();
                if let Some(v) = self.eval_const_u128_in_scope(&val) {
                    self.const_int_locals.insert(local, v);
                }
                scope.insert(name.clone(), ValueBinding::Local(local, ty.clone()));
                out.push(Stmt::Const {
                    local,
                    name,
                    ty,
                    init: val,
                    span: stmt_span,
                });
            }
            NodeTag::PatTuple => {
                let data = self.units.ast().node_data(pat);
                let elems: Vec<_> = self.units.ast().extra_nodes(data.lhs, data.rhs).collect();
                let val_u = self.underlying_type(&val.ty).clone();
                let elem_tys: Vec<Type> = match val_u {
                    Type::Tuple(tys) => {
                        if elems.len() > tys.len() {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                pat_span,
                                format!(
                                    "tuple destructuring pattern has {} element(s), but value has {}",
                                    elems.len(),
                                    tys.len()
                                ),
                            ));
                            return;
                        }
                        tys.into_iter().take(elems.len()).collect()
                    }
                    Type::Vector(len, ety) => {
                        if elems.len() > len as usize {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                pat_span,
                                format!(
                                    "vector destructuring pattern has {} element(s), but `Vector<{len}, ...>` has {len}",
                                    elems.len()
                                ),
                            ));
                            return;
                        }
                        vec![(*ety).clone(); elems.len()]
                    }
                    other => {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            pat_span,
                            format!(
                                "cannot destructure type `{}` with a tuple/vector pattern",
                                self.format_type(&other)
                            ),
                        ));
                        return;
                    }
                };
                // Bind the scrutinee once so side-effecting expressions are evaluated once.
                let tmp = self.alloc_local();
                let tmp_ty = val.ty.clone();
                out.push(Stmt::Const {
                    local: tmp,
                    name: format!("__pat_{}", tmp.0),
                    ty: tmp_ty.clone(),
                    init: val,
                    span: stmt_span,
                });
                for (i, (sub_pat, ety)) in elems.into_iter().zip(elem_tys).enumerate() {
                    if !sub_pat.is_some() {
                        continue;
                    }
                    let elem_expr = Expr {
                        kind: ExprKind::Index {
                            base: Box::new(Expr {
                                kind: ExprKind::LocalRef(tmp),
                                ty: tmp_ty.clone(),
                                span: stmt_span,
                            }),
                            index: Box::new(Expr {
                                kind: ExprKind::IntLit(i as u128),
                                ty: Type::Uint(64),
                                span: stmt_span,
                            }),
                        },
                        ty: ety,
                        span: self.units.ast().node_span(sub_pat),
                    };
                    self.bind_pattern(sub_pat, elem_expr, scope, out, stmt_span);
                }
            }
            NodeTag::PatStruct => {
                let data = self.units.ast().node_data(pat);
                let field_nodes: Vec<_> =
                    self.units.ast().extra_nodes(data.lhs, data.rhs).collect();
                let Some(struct_fields) = self.struct_fields_of(&val.ty) else {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        pat_span,
                        format!(
                            "cannot destructure non-struct type `{}` with a struct pattern",
                            self.format_type(&val.ty)
                        ),
                    ));
                    return;
                };
                let tmp = self.alloc_local();
                let tmp_ty = val.ty.clone();
                out.push(Stmt::Const {
                    local: tmp,
                    name: format!("__pat_{}", tmp.0),
                    ty: tmp_ty.clone(),
                    init: val,
                    span: stmt_span,
                });
                for fnode in field_nodes {
                    let sf = self.units.ast().pat_struct_field(fnode);
                    let fname = self.text(sf.name_token).to_owned();
                    let fspan = self.units.ast().token_span(sf.name_token);
                    let Some((_, fty)) = struct_fields.iter().find(|(n, _)| *n == fname) else {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            fspan,
                            format!(
                                "struct `{}` has no field `{fname}`",
                                self.format_type(&tmp_ty)
                            ),
                        ));
                        continue;
                    };
                    let field_expr = Expr {
                        kind: ExprKind::FieldAccess {
                            base: Box::new(Expr {
                                kind: ExprKind::LocalRef(tmp),
                                ty: tmp_ty.clone(),
                                span: stmt_span,
                            }),
                            field: fname.clone(),
                        },
                        ty: fty.clone(),
                        span: fspan,
                    };
                    if let Some(sub_pat) = sf.pat {
                        self.bind_pattern(sub_pat, field_expr, scope, out, stmt_span);
                    } else {
                        let local = self.alloc_local();
                        scope.insert(fname.clone(), ValueBinding::Local(local, fty.clone()));
                        out.push(Stmt::Const {
                            local,
                            name: fname,
                            ty: fty.clone(),
                            init: field_expr,
                            span: stmt_span,
                        });
                    }
                }
            }
            _ => {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    pat_span,
                    "unsupported binding pattern",
                ));
            }
        }
    }

    fn check_stmt(
        &mut self,
        node: NodeIndex,
        scope: &mut HashMap<String, ValueBinding>,
        expected_ret: &Type,
        out: &mut Vec<Stmt>,
    ) {
        let data = self.units.ast().node_data(node);
        match self.units.ast().node_tag(node) {
            NodeTag::Block => {
                let stmts = self.check_stmt_list(node, scope, expected_ret);
                out.extend(stmts);
            }
            NodeTag::IfStmt => {
                let stmt = self.units.ast().if_stmt(node);
                let Some(cond) = self.check_expr(stmt.cond, scope, Some(&Type::Boolean)) else {
                    return;
                };
                if cond.ty != Type::Boolean {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        cond.span,
                        format!(
                            "`if` condition must be `Boolean`, found `{}`",
                            self.format_type(&cond.ty)
                        ),
                    ));
                    return;
                }
                let then_branch = self.check_stmt_list(stmt.then_branch, scope, expected_ret);
                let else_branch = match stmt.else_branch {
                    Some(eb) => self.check_stmt_list(eb, scope, expected_ret),
                    None => Vec::new(),
                };
                out.push(Stmt::If {
                    cond,
                    then_branch,
                    else_branch,
                    span: self.units.ast().node_span(node),
                });
            }
            NodeTag::ForRangeStmt => {
                let stmt = self.units.ast().for_range_stmt(node);
                let var_name = self.text(stmt.name_token).to_owned();
                let Some(start_expr) = self.check_expr(stmt.start, scope, Some(&Type::Uint(64)))
                else {
                    return;
                };
                let Some(end_expr) = self.check_expr(stmt.end, scope, Some(&Type::Uint(64))) else {
                    return;
                };
                let Some(start) = self.eval_const_u128_in_scope(&start_expr) else {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        start_expr.span,
                        "`for` range lower bound must be a compile-time integer constant",
                    ));
                    return;
                };
                let Some(end) = self.eval_const_u128_in_scope(&end_expr) else {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        end_expr.span,
                        "`for` range upper bound must be a compile-time integer constant",
                    ));
                    return;
                };
                if start > end {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        self.units.ast().node_span(node),
                        format!("invalid `for` range `{start}..{end}`: start exceeds end"),
                    ));
                    return;
                }
                let local = self.alloc_local();
                self.loop_index_locals.insert(local);
                let mut loop_scope = scope.clone();
                loop_scope.insert(var_name.clone(), ValueBinding::Local(local, Type::Uint(64)));
                let body = self.check_stmt_list(stmt.body, &loop_scope, expected_ret);
                out.push(Stmt::ForRange {
                    local,
                    name: var_name,
                    start: start as u64,
                    end: end as u64,
                    body,
                    span: self.units.ast().node_span(node),
                });
            }
            NodeTag::ForEachStmt => {
                let stmt = self.units.ast().for_each_stmt(node);
                let var_name = self.text(stmt.name_token).to_owned();
                let Some(iter) = self.check_expr(stmt.iter, scope, None) else {
                    return;
                };
                let iter_u = self.underlying_type(&iter.ty).clone();
                let (len, elem_ty) = match iter_u {
                    Type::Vector(len, elem) => (len, (*elem).clone()),
                    Type::Bytes(len) => (len, Type::Uint(8)),
                    Type::Tuple(elems) if elems.is_empty() => (0, Type::unit()),
                    Type::Tuple(elems)
                        if elems
                            .iter()
                            .all(|t| self.can_implicitly_widen(t, &elems[0])) =>
                    {
                        (elems.len() as u32, elems[0].clone())
                    }
                    other => {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            iter.span,
                            format!(
                                "`for` loop iterable must be a `Vector`, found `{}`",
                                self.format_type(&other)
                            ),
                        ));
                        return;
                    }
                };
                let local = self.alloc_local();
                if matches!(self.underlying_type(&elem_ty), Type::Uint(_)) {
                    self.loop_index_locals.insert(local);
                }
                let mut loop_scope = scope.clone();
                loop_scope.insert(
                    var_name.clone(),
                    ValueBinding::Local(local, elem_ty.clone()),
                );
                let body = self.check_stmt_list(stmt.body, &loop_scope, expected_ret);
                out.push(Stmt::ForEach {
                    local,
                    name: var_name,
                    elem_ty,
                    iter,
                    len,
                    body,
                    span: self.units.ast().node_span(node),
                });
            }
            NodeTag::ConstStmt => {
                let stmt = self.units.ast().const_stmt(node);
                let annotated = match stmt.ty {
                    Some(ty_node) => match self.resolve_type(ty_node) {
                        Some(t) => Some(t),
                        None => return,
                    },
                    None => None,
                };
                let Some(mut init) = self.check_expr(stmt.init, scope, annotated.as_ref()) else {
                    return;
                };
                if let Some(ann) = annotated {
                    if !self.coerce_or_check(&mut init, &ann) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            init.span,
                            format!(
                                "type mismatch in `const` binding: expected `{}`, found `{}`",
                                self.format_type(&ann),
                                self.format_type(&init.ty)
                            ),
                        ));
                    } else {
                        init.ty = ann;
                    }
                }
                let stmt_span = self.units.ast().node_span(node);
                self.bind_pattern(stmt.pat, init, scope, out, stmt_span);
            }
            NodeTag::AssignStmt => {
                let stmt = self.units.ast().assign_stmt(node);
                let assign_span = self.units.ast().node_span(node);
                let op_tag = self.units.ast().token_tag(stmt.eq_token);

                if matches!(op_tag, TokenTag::PlusEq | TokenTag::MinusEq) {
                    let Some((field_id, key_path, target_adt)) =
                        self.try_extract_ledger_chain(stmt.lhs, scope)
                    else {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            self.units.ast().node_span(stmt.lhs),
                            format!(
                                "left-hand side of `{}` must be a `Counter` ledger target",
                                op_tag.as_str()
                            ),
                        ));
                        return;
                    };
                    if target_adt != LedgerAdt::Counter {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            assign_span,
                            format!(
                                "cannot use `{}` on ledger ADT `{}`; only `Counter` supports compound assignment",
                                op_tag.as_str(),
                                target_adt.name()
                            ),
                        ));
                        return;
                    }
                    let expected = Type::Uint(16);
                    let Some(mut rhs) = self.check_expr(stmt.rhs, scope, Some(&expected)) else {
                        return;
                    };
                    if !self.coerce_or_check(&mut rhs, &expected) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            rhs.span,
                            format!(
                                "`{}` on `Counter` expects `Uint<16>`, found `{}`",
                                op_tag.as_str(),
                                self.format_type(&rhs.ty)
                            ),
                        ));
                        return;
                    }
                    let op = if op_tag == TokenTag::PlusEq {
                        LedgerOp::CounterIncrement
                    } else {
                        LedgerOp::CounterDecrement
                    };
                    out.push(Stmt::Expr(Expr {
                        kind: ExprKind::LedgerCall {
                            field: field_id,
                            key_path,
                            target_adt,
                            op,
                            args: vec![rhs],
                        },
                        ty: Type::unit(),
                        span: assign_span,
                    }));
                    return;
                }

                if self.units.ast().node_tag(stmt.lhs) != NodeTag::IdentExpr {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        self.units.ast().node_span(stmt.lhs),
                        "left-hand side of assignment must be a ledger field",
                    ));
                    return;
                }
                let lhs_tok = self.units.ast().node_main_token(stmt.lhs);
                let field_name = self.text(lhs_tok).to_owned();
                let Some(&field_id) = self.scope.ledger_fields.get(&field_name) else {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        self.units.ast().token_span(lhs_tok),
                        format!("cannot assign to `{field_name}`: not a ledger field"),
                    ));
                    return;
                };
                let field = &self.ledger_fields[field_id.0 as usize];
                let Some(expected_val_ty) = field.adt.cell_type().cloned() else {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        assign_span,
                        format!(
                            "cannot directly assign to ledger `{field_name}` of ADT type `{}`; use its methods instead",
                            field.adt.name()
                        ),
                    ));
                    return;
                };
                let target_adt = field.adt.clone();
                let Some(mut rhs) = self.check_expr(stmt.rhs, scope, Some(&expected_val_ty)) else {
                    return;
                };
                if !self.coerce_or_check(&mut rhs, &expected_val_ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        rhs.span,
                        format!(
                            "cannot assign `{}` to ledger field `{field_name}` of type `{}`",
                            self.format_type(&rhs.ty),
                            self.format_type(&expected_val_ty)
                        ),
                    ));
                    return;
                }
                out.push(Stmt::Expr(Expr {
                    kind: ExprKind::LedgerCall {
                        field: field_id,
                        key_path: Vec::new(),
                        target_adt,
                        op: LedgerOp::CellWrite,
                        args: vec![rhs],
                    },
                    ty: Type::unit(),
                    span: assign_span,
                }));
            }
            NodeTag::ExprStmt => {
                if let Some(expr) = self.check_expr(NodeIndex(data.lhs), scope, None) {
                    out.push(Stmt::Expr(expr));
                }
            }
            NodeTag::ReturnStmt => {
                let span = self.units.ast().node_span(node);
                let value = if let Some(expr_node) = NodeIndex(data.lhs).into_option() {
                    let Some(mut expr) = self.check_expr(expr_node, scope, Some(expected_ret))
                    else {
                        return;
                    };
                    if !self.coerce_or_check(&mut expr, expected_ret) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            expr.span,
                            format!(
                                "mismatched return type: expected `{}`, found `{}`",
                                self.format_type(expected_ret),
                                self.format_type(&expr.ty)
                            ),
                        ));
                    }
                    Some(expr)
                } else {
                    if !expected_ret.is_unit() {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            span,
                            format!(
                                "empty `return` in circuit returning `{}`",
                                self.format_type(expected_ret)
                            ),
                        ));
                    }
                    None
                };
                out.push(Stmt::Return { value, span });
            }
            _ => {}
        }
    }

    fn structs_structurally_equal(&self, a: StructId, b: StructId) -> bool {
        if a == b {
            return true;
        }
        let sa = &self.structs[a.0 as usize];
        let sb = &self.structs[b.0 as usize];
        sa.fields.len() == sb.fields.len()
            && sa
                .fields
                .iter()
                .zip(&sb.fields)
                .all(|(fa, fb)| fa.name == fb.name && self.can_implicitly_widen(&fa.ty, &fb.ty))
    }

    fn enums_structurally_equal(&self, a: EnumId, b: EnumId) -> bool {
        if a == b {
            return true;
        }
        self.enums[a.0 as usize].variants == self.enums[b.0 as usize].variants
    }

    fn can_implicitly_widen(&self, src: &Type, dst: &Type) -> bool {
        if src == dst {
            return true;
        }
        match (src, dst) {
            (Type::Uint(a), Type::Uint(b)) => a <= b,
            (Type::Struct(a), Type::Struct(b)) => self.structs_structurally_equal(*a, *b),
            (Type::Enum(a), Type::Enum(b)) => self.enums_structurally_equal(*a, *b),
            (Type::Vector(n1, e1), Type::Vector(n2, e2)) => {
                n1 == n2 && self.can_implicitly_widen(e1, e2)
            }
            (Type::Vector(n, e), Type::Tuple(dst_elems)) => {
                *n as usize == dst_elems.len()
                    && dst_elems.iter().all(|d| self.can_implicitly_widen(e, d))
            }
            (Type::Tuple(src_elems), Type::Vector(n, dst_e)) => {
                src_elems.len() == *n as usize
                    && src_elems
                        .iter()
                        .all(|s| self.can_implicitly_widen(s, dst_e))
            }
            (Type::Tuple(s), Type::Tuple(d)) => {
                s.len() == d.len()
                    && s.iter()
                        .zip(d.iter())
                        .all(|(a, b)| self.can_implicitly_widen(a, b))
            }
            _ => false,
        }
    }

    fn coerce_or_check(&self, expr: &mut Expr, expected: &Type) -> bool {
        if expr.ty == *expected {
            return true;
        }
        // Implicit unsigned integer widening (`Uint<M>` -> `Uint<N>` when `M <= N`).
        if let (Type::Uint(src_bits), Type::Uint(dst_bits)) = (&expr.ty, expected)
            && src_bits <= dst_bits
            && !matches!(&expr.kind, ExprKind::IntLit(_))
        {
            return true;
        }
        if let ExprKind::IntLit(v) = &expr.kind {
            match expected {
                Type::Field => {
                    expr.ty = Type::Field;
                    return true;
                }
                Type::Uint(bits) if *bits >= 128 || *v < (1u128 << bits) => {
                    expr.ty = expected.clone();
                    return true;
                }
                _ => {}
            }
        }
        if let Type::Tuple(dst_elems) = expected {
            if let ExprKind::Tuple(elems) = &mut expr.kind
                && elems.len() == dst_elems.len()
                && elems
                    .iter_mut()
                    .zip(dst_elems.iter())
                    .all(|(e, dt)| self.coerce_or_check(e, dt))
            {
                expr.ty = expected.clone();
                return true;
            }
            if let ExprKind::Vector(elems) = &mut expr.kind
                && elems.len() == dst_elems.len()
                && elems
                    .iter_mut()
                    .zip(dst_elems.iter())
                    .all(|(e, dt)| self.coerce_or_check(e, dt))
            {
                let moved = std::mem::take(elems);
                expr.kind = ExprKind::Tuple(moved);
                expr.ty = expected.clone();
                return true;
            }
            if let ExprKind::Block { tail, .. } = &mut expr.kind
                && self.coerce_or_check(tail, expected)
            {
                expr.ty = expected.clone();
                return true;
            }
        }
        if let Type::Vector(expected_len, elem_ty) = expected {
            match &mut expr.kind {
                ExprKind::Tuple(elems) if elems.len() == *expected_len as usize => {
                    if elems.iter_mut().all(|e| self.coerce_or_check(e, elem_ty)) {
                        let moved = std::mem::take(elems);
                        expr.kind = ExprKind::Vector(moved);
                        expr.ty = expected.clone();
                        return true;
                    }
                }
                ExprKind::Vector(elems) if elems.len() == *expected_len as usize => {
                    if elems.iter_mut().all(|e| self.coerce_or_check(e, elem_ty)) {
                        expr.ty = expected.clone();
                        return true;
                    }
                }
                ExprKind::Block { tail, .. } => {
                    if self.coerce_or_check(tail, expected) {
                        expr.ty = expected.clone();
                        return true;
                    }
                }
                _ => {}
            }
        }
        !matches!(&expr.kind, ExprKind::IntLit(_)) && self.can_implicitly_widen(&expr.ty, expected)
    }

    fn check_expr(
        &mut self,
        node: NodeIndex,
        scope: &HashMap<String, ValueBinding>,
        expected: Option<&Type>,
    ) -> Option<Expr> {
        let span = self.units.ast().node_span(node);
        match self.units.ast().node_tag(node) {
            NodeTag::IntLitExpr => {
                let tok = self.units.ast().node_main_token(node);
                let raw = self.text(tok);
                let val: u128 = match compact_ast::parse_nat_u128(raw) {
                    Some(v) => v,
                    None => {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            span,
                            format!("integer literal `{raw}` is out of range"),
                        ));
                        return None;
                    }
                };
                let ty = match expected {
                    Some(Type::Uint(bits)) if *bits >= 128 || val < (1u128 << bits) => {
                        Type::Uint(*bits)
                    }
                    _ => Type::Uint(64),
                };
                Some(Expr {
                    kind: ExprKind::IntLit(val),
                    ty,
                    span,
                })
            }
            NodeTag::StringLitExpr => {
                let tok = self.units.ast().node_main_token(node);
                let bytes = compact_ast::unescape_string_bytes(self.text(tok));
                let len = bytes.len() as u32;
                Some(Expr {
                    kind: ExprKind::BytesLit(bytes),
                    ty: Type::Bytes(len),
                    span,
                })
            }
            NodeTag::BoolLitExpr => {
                let tok = self.units.ast().node_main_token(node);
                let val = self.units.ast().token_tag(tok) == TokenTag::True;
                Some(Expr {
                    kind: ExprKind::BoolLit(val),
                    ty: Type::Boolean,
                    span,
                })
            }
            NodeTag::DefaultExpr => {
                let data = self.units.ast().node_data(node);
                let ty = self.resolve_type(NodeIndex(data.lhs))?;
                Some(Expr {
                    kind: ExprKind::Default(ty.clone()),
                    ty,
                    span,
                })
            }
            NodeTag::IdentExpr => {
                let tok = self.units.ast().node_main_token(node);
                let name = self.text(tok).to_owned();
                if let Some(binding) = scope.get(&name) {
                    return Some(match binding {
                        ValueBinding::Param(pid, ty) => Expr {
                            kind: ExprKind::ParamRef(*pid),
                            ty: ty.clone(),
                            span,
                        },
                        ValueBinding::Local(lid, ty) => Expr {
                            kind: ExprKind::LocalRef(*lid),
                            ty: ty.clone(),
                            span,
                        },
                    });
                }
                if let Some(&n) = self.scope.generics.nats.get(&name) {
                    let ty = match expected {
                        Some(Type::Uint(bits)) if *bits < 128 && (n as u128) < (1u128 << bits) => {
                            Type::Uint(*bits)
                        }
                        Some(Type::Field) => Type::Field,
                        _ => Type::Uint(64),
                    };
                    return Some(Expr {
                        kind: ExprKind::IntLit(n as u128),
                        ty,
                        span,
                    });
                }
                if let Some(&field_id) = self.scope.ledger_fields.get(&name) {
                    let field = &self.ledger_fields[field_id.0 as usize];
                    if let Some(val_ty) = field.adt.cell_type().cloned() {
                        return Some(Expr {
                            kind: ExprKind::LedgerCall {
                                field: field_id,
                                key_path: Vec::new(),
                                target_adt: field.adt.clone(),
                                op: LedgerOp::CellRead,
                                args: Vec::new(),
                            },
                            ty: val_ty,
                            span,
                        });
                    }
                    if field.adt == LedgerAdt::Counter {
                        return Some(Expr {
                            kind: ExprKind::LedgerCall {
                                field: field_id,
                                key_path: Vec::new(),
                                target_adt: LedgerAdt::Counter,
                                op: LedgerOp::CounterRead,
                                args: Vec::new(),
                            },
                            ty: Type::Uint(64),
                            span,
                        });
                    }
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        span,
                        format!(
                            "ledger field `{name}` of type `{}` cannot be read directly as a value",
                            field.adt.name()
                        ),
                    ));
                    return None;
                }
                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    span,
                    format!("unbound identifier `{name}`"),
                ));
                None
            }
            NodeTag::IndexExpr => {
                let idx_expr = self.units.ast().index_expr(node);
                let base = self.check_expr(idx_expr.base, scope, None)?;
                let mut index = self.check_expr(idx_expr.index, scope, Some(&Type::Uint(64)))?;
                let base_underlying = self.underlying_type(&base.ty).clone();
                let const_idx = self.eval_const_u128_in_scope(&index);
                let is_loop_idx = self.is_loop_index_expr(&index);
                if let Some(k) = const_idx {
                    index = Expr {
                        kind: ExprKind::IntLit(k),
                        ty: Type::Uint(64),
                        span: index.span,
                    };
                }
                match base_underlying {
                    Type::Vector(len, elem) => {
                        if let Some(k) = const_idx {
                            if k >= len as u128 {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    index.span,
                                    format!(
                                        "vector index {k} out of bounds for `Vector<{len}, ...>`"
                                    ),
                                ));
                                return None;
                            }
                        } else if !is_loop_idx {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                index.span,
                                "vector index must be a compile-time integer constant",
                            ));
                            return None;
                        }
                        Some(Expr {
                            kind: ExprKind::Index {
                                base: Box::new(base),
                                index: Box::new(index),
                            },
                            ty: *elem,
                            span,
                        })
                    }
                    Type::Bytes(len) => {
                        if let Some(k) = const_idx {
                            if k >= len as u128 {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    index.span,
                                    format!("bytes index {k} out of bounds for `Bytes<{len}>`"),
                                ));
                                return None;
                            }
                        } else if !is_loop_idx {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                index.span,
                                "bytes index must be a compile-time integer constant",
                            ));
                            return None;
                        }
                        Some(Expr {
                            kind: ExprKind::Index {
                                base: Box::new(base),
                                index: Box::new(index),
                            },
                            ty: Type::Uint(8),
                            span,
                        })
                    }
                    Type::Tuple(elems) => {
                        if let Some(k) = const_idx {
                            let Some(elem_ty) = elems.get(k as usize).cloned() else {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    index.span,
                                    format!(
                                        "tuple index {k} out of bounds for tuple of length {}",
                                        elems.len()
                                    ),
                                ));
                                return None;
                            };
                            Some(Expr {
                                kind: ExprKind::Index {
                                    base: Box::new(base),
                                    index: Box::new(index),
                                },
                                ty: elem_ty,
                                span,
                            })
                        } else if is_loop_idx
                            && !elems.is_empty()
                            && elems.iter().all(|e| *e == elems[0])
                        {
                            Some(Expr {
                                kind: ExprKind::Index {
                                    base: Box::new(base),
                                    index: Box::new(index),
                                },
                                ty: elems[0].clone(),
                                span,
                            })
                        } else {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                index.span,
                                "tuple index must be a compile-time integer constant",
                            ));
                            None
                        }
                    }
                    other => {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            span,
                            format!(
                                "cannot index into type `{}` (expected `Vector`, `Bytes`, or tuple)",
                                self.format_type(&other)
                            ),
                        ));
                        None
                    }
                }
            }
            NodeTag::MemberExpr => {
                let data = self.units.ast().node_data(node);
                let lhs = NodeIndex(data.lhs);
                let field_tok = TokenIndex(data.rhs);
                let field_name = self.text(field_tok).to_owned();
                if self.units.ast().node_tag(lhs) == NodeTag::IdentExpr {
                    let type_name = self.text(self.units.ast().node_main_token(lhs)).to_owned();
                    if let Some(&enum_id) = self.scope.enums.get(&type_name) {
                        if let Some(idx) = self.enums[enum_id.0 as usize]
                            .variants
                            .iter()
                            .position(|v| v == &field_name)
                        {
                            return Some(Expr {
                                kind: ExprKind::EnumVariant {
                                    enum_id,
                                    variant_idx: idx as u32,
                                },
                                ty: Type::Enum(enum_id),
                                span,
                            });
                        }
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            self.units.ast().token_span(field_tok),
                            format!("enum `{type_name}` has no variant `{field_name}`"),
                        ));
                        return None;
                    }
                }
                let base = self.check_expr(lhs, scope, None)?;
                if let Some(fields) = self.struct_fields_of(&base.ty) {
                    if let Some((_, field_ty)) = fields.into_iter().find(|(n, _)| n == &field_name)
                    {
                        return Some(Expr {
                            kind: ExprKind::FieldAccess {
                                base: Box::new(base),
                                field: field_name,
                            },
                            ty: field_ty,
                            span,
                        });
                    }
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        self.units.ast().token_span(field_tok),
                        format!(
                            "type `{}` has no field `{field_name}`",
                            self.format_type(&base.ty)
                        ),
                    ));
                    return None;
                }
                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    span,
                    format!(
                        "cannot access field `{field_name}` on type `{}`",
                        self.format_type(&base.ty)
                    ),
                ));
                None
            }
            NodeTag::StructLitExpr => {
                let lit = self.units.ast().struct_lit_expr(node);
                let ty = self.resolve_type(lit.type_node)?;
                let Some(expected_fields) = self.struct_fields_of(&ty) else {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        self.units.ast().node_span(lit.type_node),
                        format!("`{}` is not a struct type", self.format_type(&ty)),
                    ));
                    return None;
                };
                let lit_nodes: Vec<_> = self
                    .units
                    .ast()
                    .extra_nodes(lit.fields_start, lit.fields_end)
                    .collect();
                let mut prelude: Vec<Stmt> = Vec::new();
                let mut provided: HashMap<String, Expr> = HashMap::new();
                let mut pos_idx = 0usize;
                for fnode in lit_nodes {
                    if self.units.ast().node_tag(fnode) == NodeTag::SpreadExpr {
                        let sdata = self.units.ast().node_data(fnode);
                        let base_expr = self.check_expr(NodeIndex(sdata.lhs), scope, Some(&ty))?;
                        if base_expr.ty != ty {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                base_expr.span,
                                format!(
                                    "struct spread expects `{}`, found `{}`",
                                    self.format_type(&ty),
                                    self.format_type(&base_expr.ty)
                                ),
                            ));
                            return None;
                        }
                        let tmp = self.alloc_local();
                        let bspan = base_expr.span;
                        prelude.push(Stmt::Const {
                            local: tmp,
                            name: format!("__spread_{}", tmp.0),
                            ty: ty.clone(),
                            init: base_expr,
                            span: bspan,
                        });
                        for (fname, fty) in &expected_fields {
                            provided.insert(
                                fname.clone(),
                                Expr {
                                    kind: ExprKind::FieldAccess {
                                        base: Box::new(Expr {
                                            kind: ExprKind::LocalRef(tmp),
                                            ty: ty.clone(),
                                            span: bspan,
                                        }),
                                        field: fname.clone(),
                                    },
                                    ty: fty.clone(),
                                    span: bspan,
                                },
                            );
                        }
                        continue;
                    }
                    if self.units.ast().node_tag(fnode) == NodeTag::StructLitField {
                        let sf = self.units.ast().struct_lit_field(fnode);
                        let fname = self.text(sf.name_token).to_owned();
                        let Some((_, expected_ty)) =
                            expected_fields.iter().find(|(n, _)| *n == fname)
                        else {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                self.units.ast().token_span(sf.name_token),
                                format!(
                                    "struct `{}` has no field `{fname}`",
                                    self.format_type(&ty)
                                ),
                            ));
                            return None;
                        };
                        let mut val = self.check_expr(sf.value, scope, Some(expected_ty))?;
                        if !self.coerce_or_check(&mut val, expected_ty) {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                val.span,
                                format!(
                                    "type mismatch for field `{fname}`: expected `{}`, found `{}`",
                                    self.format_type(expected_ty),
                                    self.format_type(&val.ty)
                                ),
                            ));
                            return None;
                        }
                        provided.insert(fname, val);
                    } else {
                        // Positional struct literal argument.
                        let Some((fname, expected_ty)) = expected_fields.get(pos_idx) else {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                self.units.ast().node_span(fnode),
                                format!(
                                    "too many positional fields for struct `{}` (expected {})",
                                    self.format_type(&ty),
                                    expected_fields.len()
                                ),
                            ));
                            return None;
                        };
                        pos_idx += 1;
                        let mut val = self.check_expr(fnode, scope, Some(expected_ty))?;
                        if !self.coerce_or_check(&mut val, expected_ty) {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                val.span,
                                format!(
                                    "type mismatch for field `{fname}`: expected `{}`, found `{}`",
                                    self.format_type(expected_ty),
                                    self.format_type(&val.ty)
                                ),
                            ));
                            return None;
                        }
                        provided.insert(fname.clone(), val);
                    }
                }
                let mut ordered = Vec::with_capacity(expected_fields.len());
                for (fname, _) in expected_fields {
                    let Some(val) = provided.remove(&fname) else {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            span,
                            format!(
                                "missing field `{fname}` in struct `{}` literal",
                                self.format_type(&ty)
                            ),
                        ));
                        return None;
                    };
                    ordered.push((fname, val));
                }
                let struct_expr = Expr {
                    kind: ExprKind::StructLit { fields: ordered },
                    ty: ty.clone(),
                    span,
                };
                if prelude.is_empty() {
                    Some(struct_expr)
                } else {
                    Some(Expr {
                        kind: ExprKind::Block {
                            stmts: prelude,
                            tail: Box::new(struct_expr),
                        },
                        ty,
                        span,
                    })
                }
            }
            NodeTag::BytesLitExpr => {
                let lit = self.units.ast().bytes_lit_expr(node);
                let elem_nodes: Vec<_> = self
                    .units
                    .ast()
                    .extra_nodes(lit.elems_start, lit.elems_end)
                    .collect();
                let mut prelude: Vec<Stmt> = Vec::new();
                let mut byte_exprs: Vec<Expr> = Vec::new();
                for enode in elem_nodes {
                    if self.units.ast().node_tag(enode) == NodeTag::SpreadExpr {
                        let sdata = self.units.ast().node_data(enode);
                        let inner = self.check_expr(NodeIndex(sdata.lhs), scope, None)?;
                        let inner_span = inner.span;
                        let inner_u = self.underlying_type(&inner.ty).clone();
                        match inner_u {
                            Type::Bytes(k) => {
                                let vec_ty = Type::Vector(k, Box::new(Type::Uint(8)));
                                let tmp = self.alloc_local();
                                prelude.push(Stmt::Const {
                                    local: tmp,
                                    name: format!("__bspread_{}", tmp.0),
                                    ty: vec_ty.clone(),
                                    init: Expr {
                                        kind: ExprKind::Cast {
                                            expr: Box::new(inner),
                                            target: vec_ty.clone(),
                                        },
                                        ty: vec_ty.clone(),
                                        span: inner_span,
                                    },
                                    span: inner_span,
                                });
                                for i in 0..k {
                                    byte_exprs.push(Expr {
                                        kind: ExprKind::Index {
                                            base: Box::new(Expr {
                                                kind: ExprKind::LocalRef(tmp),
                                                ty: vec_ty.clone(),
                                                span: inner_span,
                                            }),
                                            index: Box::new(Expr {
                                                kind: ExprKind::IntLit(i as u128),
                                                ty: Type::Uint(64),
                                                span: inner_span,
                                            }),
                                        },
                                        ty: Type::Uint(8),
                                        span: inner_span,
                                    });
                                }
                            }
                            Type::Vector(k, ety)
                                if *self.underlying_type(&ety) == Type::Uint(8) =>
                            {
                                let vec_ty = inner.ty.clone();
                                let tmp = self.alloc_local();
                                prelude.push(Stmt::Const {
                                    local: tmp,
                                    name: format!("__bspread_{}", tmp.0),
                                    ty: vec_ty.clone(),
                                    init: inner,
                                    span: inner_span,
                                });
                                for i in 0..k {
                                    byte_exprs.push(Expr {
                                        kind: ExprKind::Index {
                                            base: Box::new(Expr {
                                                kind: ExprKind::LocalRef(tmp),
                                                ty: vec_ty.clone(),
                                                span: inner_span,
                                            }),
                                            index: Box::new(Expr {
                                                kind: ExprKind::IntLit(i as u128),
                                                ty: Type::Uint(64),
                                                span: inner_span,
                                            }),
                                        },
                                        ty: Type::Uint(8),
                                        span: inner_span,
                                    });
                                }
                            }
                            other => {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    inner_span,
                                    format!(
                                        "spread inside `Bytes[...]` expects `Bytes<N>` or `Vector<N, Uint<8>>`, found `{}`",
                                        self.format_type(&other)
                                    ),
                                ));
                                return None;
                            }
                        }
                    } else {
                        let mut e = self.check_expr(enode, scope, Some(&Type::Uint(8)))?;
                        if !self.coerce_or_check(&mut e, &Type::Uint(8)) {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                e.span,
                                format!(
                                    "`Bytes[...]` element must be `Uint<8>`, found `{}`",
                                    self.format_type(&e.ty)
                                ),
                            ));
                            return None;
                        }
                        byte_exprs.push(e);
                    }
                }
                let ty = Type::Bytes(byte_exprs.len() as u32);
                let pack = Expr {
                    kind: ExprKind::BytesPack(byte_exprs),
                    ty: ty.clone(),
                    span,
                };
                if prelude.is_empty() {
                    Some(pack)
                } else {
                    Some(Expr {
                        kind: ExprKind::Block {
                            stmts: prelude,
                            tail: Box::new(pack),
                        },
                        ty,
                        span,
                    })
                }
            }
            NodeTag::TupleExpr => {
                let data = self.units.ast().node_data(node);
                let elem_nodes: Vec<_> = self.units.ast().extra_nodes(data.lhs, data.rhs).collect();
                let has_spread = elem_nodes
                    .iter()
                    .any(|&n| self.units.ast().node_tag(n) == NodeTag::SpreadExpr);
                if has_spread {
                    let expected_elem_ty = match expected {
                        Some(Type::Vector(_, elem_ty)) => Some(elem_ty.as_ref()),
                        _ => None,
                    };
                    let mut prelude: Vec<Stmt> = Vec::new();
                    let mut flat: Vec<Expr> = Vec::new();
                    let mut tys: Vec<Type> = Vec::new();
                    let mut empty_spread_elem_ty: Option<Type> = None;
                    for enode in elem_nodes {
                        if self.units.ast().node_tag(enode) == NodeTag::SpreadExpr {
                            let sdata = self.units.ast().node_data(enode);
                            let inner = self.check_expr(NodeIndex(sdata.lhs), scope, None)?;
                            let inner_span = inner.span;
                            let inner_ty = inner.ty.clone();
                            let inner_u = self.underlying_type(&inner_ty).clone();
                            let spread_tys: Vec<Type> = match inner_u {
                                Type::Vector(k, ety) => {
                                    if k == 0 && empty_spread_elem_ty.is_none() {
                                        empty_spread_elem_ty = Some((*ety).clone());
                                    }
                                    vec![(*ety).clone(); k as usize]
                                }
                                Type::Bytes(k) => {
                                    if k == 0 && empty_spread_elem_ty.is_none() {
                                        empty_spread_elem_ty = Some(Type::Uint(8));
                                    }
                                    vec![Type::Uint(8); k as usize]
                                }
                                Type::Tuple(etys) => etys,
                                other => {
                                    self.diagnostics.push(CompactDiagnostic::error(
                                        self.units.file(),
                                        inner_span,
                                        format!(
                                            "cannot spread type `{}` inside `[...]`; expected `Vector`, `Bytes`, or tuple",
                                            self.format_type(&other)
                                        ),
                                    ));
                                    return None;
                                }
                            };
                            let tmp = self.alloc_local();
                            prelude.push(Stmt::Const {
                                local: tmp,
                                name: format!("__spread_{}", tmp.0),
                                ty: inner_ty.clone(),
                                init: inner,
                                span: inner_span,
                            });
                            for (i, ety) in spread_tys.into_iter().enumerate() {
                                tys.push(ety.clone());
                                flat.push(Expr {
                                    kind: ExprKind::Index {
                                        base: Box::new(Expr {
                                            kind: ExprKind::LocalRef(tmp),
                                            ty: inner_ty.clone(),
                                            span: inner_span,
                                        }),
                                        index: Box::new(Expr {
                                            kind: ExprKind::IntLit(i as u128),
                                            ty: Type::Uint(64),
                                            span: inner_span,
                                        }),
                                    },
                                    ty: ety,
                                    span: inner_span,
                                });
                            }
                        } else {
                            let e = self.check_expr(enode, scope, expected_elem_ty)?;
                            tys.push(e.ty.clone());
                            flat.push(e);
                        }
                    }
                    if let Some(Type::Vector(expected_len, elem_ty)) = expected {
                        if flat.len() != *expected_len as usize {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                span,
                                format!(
                                    "expected `Vector` of length {expected_len}, found {} element(s)",
                                    flat.len()
                                ),
                            ));
                            return None;
                        }
                        for e in &mut flat {
                            if !self.coerce_or_check(e, elem_ty) {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    e.span,
                                    format!(
                                        "vector element type mismatch: expected `{}`, found `{}`",
                                        self.format_type(elem_ty),
                                        self.format_type(&e.ty)
                                    ),
                                ));
                                return None;
                            }
                        }
                        let ty = Type::Vector(*expected_len, elem_ty.clone());
                        return Some(Expr {
                            kind: ExprKind::Block {
                                stmts: prelude,
                                tail: Box::new(Expr {
                                    kind: ExprKind::Vector(flat),
                                    ty: ty.clone(),
                                    span,
                                }),
                            },
                            ty,
                            span,
                        });
                    }
                    let ty = if tys.is_empty()
                        && let Some(elem_ty) = empty_spread_elem_ty
                    {
                        Type::Vector(0, Box::new(elem_ty))
                    } else {
                        Type::Tuple(tys)
                    };
                    let tail_kind = if matches!(ty, Type::Vector(..)) {
                        ExprKind::Vector(flat)
                    } else {
                        ExprKind::Tuple(flat)
                    };
                    return Some(Expr {
                        kind: ExprKind::Block {
                            stmts: prelude,
                            tail: Box::new(Expr {
                                kind: tail_kind,
                                ty: ty.clone(),
                                span,
                            }),
                        },
                        ty,
                        span,
                    });
                }

                if let Some(Type::Vector(expected_len, elem_ty)) = expected {
                    if elem_nodes.len() != *expected_len as usize {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            span,
                            format!(
                                "expected `Vector` of length {expected_len}, found {} element(s)",
                                elem_nodes.len()
                            ),
                        ));
                        return None;
                    }
                    let mut exprs = Vec::with_capacity(elem_nodes.len());
                    for enode in elem_nodes {
                        let mut e = self.check_expr(enode, scope, Some(elem_ty))?;
                        if !self.coerce_or_check(&mut e, elem_ty) {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                e.span,
                                format!(
                                    "vector element type mismatch: expected `{}`, found `{}`",
                                    self.format_type(elem_ty),
                                    self.format_type(&e.ty)
                                ),
                            ));
                            return None;
                        }
                        exprs.push(e);
                    }
                    return Some(Expr {
                        kind: ExprKind::Vector(exprs),
                        ty: Type::Vector(*expected_len, elem_ty.clone()),
                        span,
                    });
                }

                let mut exprs = Vec::with_capacity(elem_nodes.len());
                let mut tys = Vec::with_capacity(elem_nodes.len());
                for enode in elem_nodes {
                    let e = self.check_expr(enode, scope, None)?;
                    tys.push(e.ty.clone());
                    exprs.push(e);
                }
                Some(Expr {
                    kind: ExprKind::Tuple(exprs),
                    ty: Type::Tuple(tys),
                    span,
                })
            }
            NodeTag::UnaryExpr => {
                let op_tok = self.units.ast().node_main_token(node);
                let data = self.units.ast().node_data(node);
                let operand = self.check_expr(NodeIndex(data.lhs), scope, expected)?;
                match self.units.ast().token_tag(op_tok) {
                    TokenTag::Bang => {
                        if operand.ty != Type::Boolean {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                operand.span,
                                format!(
                                    "logical `!` expects `Boolean`, found `{}`",
                                    self.format_type(&operand.ty)
                                ),
                            ));
                            return None;
                        }
                        Some(Expr {
                            kind: ExprKind::Unary {
                                op: UnaryOp::Not,
                                operand: Box::new(operand),
                            },
                            ty: Type::Boolean,
                            span,
                        })
                    }
                    TokenTag::Minus => {
                        let op_u = self.underlying_type(&operand.ty);
                        if !matches!(op_u, Type::Field | Type::CurveField(_)) {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                operand.span,
                                format!(
                                    "unary `-` expects a field type, found `{}`",
                                    self.format_type(&operand.ty)
                                ),
                            ));
                            return None;
                        }
                        let ty = operand.ty.clone();
                        Some(Expr {
                            kind: ExprKind::Unary {
                                op: UnaryOp::Neg,
                                operand: Box::new(operand),
                            },
                            ty,
                            span,
                        })
                    }
                    _ => None,
                }
            }
            NodeTag::BinaryExpr => {
                let op_tok = self.units.ast().node_main_token(node);
                let op = match self.units.ast().token_tag(op_tok) {
                    TokenTag::Plus => BinaryOp::Add,
                    TokenTag::Minus => BinaryOp::Sub,
                    TokenTag::Star => BinaryOp::Mul,
                    TokenTag::EqEq => BinaryOp::Eq,
                    TokenTag::BangEq => BinaryOp::Neq,
                    TokenTag::LAngle => BinaryOp::Lt,
                    TokenTag::LtEq => BinaryOp::Le,
                    TokenTag::RAngle => BinaryOp::Gt,
                    TokenTag::GtEq => BinaryOp::Ge,
                    TokenTag::AmpAmp => BinaryOp::And,
                    TokenTag::PipePipe => BinaryOp::Or,
                    other => {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            self.units.ast().token_span(op_tok),
                            format!("unsupported binary operator `{}`", other.as_str()),
                        ));
                        return None;
                    }
                };
                let data = self.units.ast().node_data(node);
                if matches!(op, BinaryOp::And | BinaryOp::Or) {
                    let lhs = self.check_expr(NodeIndex(data.lhs), scope, Some(&Type::Boolean))?;
                    let rhs = self.check_expr(NodeIndex(data.rhs), scope, Some(&Type::Boolean))?;
                    if lhs.ty != Type::Boolean || rhs.ty != Type::Boolean {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            span,
                            format!(
                                "logical `{}` expects `Boolean` operands, found `{}` and `{}`",
                                self.units.ast().token_tag(op_tok).as_str(),
                                self.format_type(&lhs.ty),
                                self.format_type(&rhs.ty)
                            ),
                        ));
                        return None;
                    }
                    return Some(Expr {
                        kind: ExprKind::Binary {
                            op,
                            lhs: Box::new(lhs),
                            rhs: Box::new(rhs),
                        },
                        ty: Type::Boolean,
                        span,
                    });
                }
                let mut lhs = self.check_expr(NodeIndex(data.lhs), scope, None)?;
                let mut rhs = self.check_expr(NodeIndex(data.rhs), scope, Some(&lhs.ty))?;
                if !self.coerce_or_check(&mut rhs, &lhs.ty)
                    && !self.coerce_or_check(&mut lhs, &rhs.ty)
                {
                    if let (Type::Uint(a), Type::Uint(b)) =
                        (self.underlying_type(&lhs.ty), self.underlying_type(&rhs.ty))
                    {
                        let widened = Type::Uint((*a).max(*b));
                        lhs.ty = widened.clone();
                        rhs.ty = widened;
                    } else if matches!(op, BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul)
                        && matches!(
                            (self.underlying_type(&lhs.ty), self.underlying_type(&rhs.ty)),
                            (Type::Field, Type::Uint(_)) | (Type::Uint(_), Type::Field)
                        )
                    {
                        lhs.ty = Type::Field;
                        rhs.ty = Type::Field;
                    } else {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            span,
                            format!(
                                "incompatible operand types `{}` and `{}`",
                                self.format_type(&lhs.ty),
                                self.format_type(&rhs.ty)
                            ),
                        ));
                        return None;
                    }
                }
                if matches!(op, BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul)
                    && !matches!(
                        self.underlying_type(&lhs.ty),
                        Type::Field | Type::Uint(_) | Type::CurveField(_)
                    )
                {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        span,
                        format!(
                            "arithmetic operator `{}` requires numeric or field operands, found `{}`",
                            self.units.ast().token_tag(op_tok).as_str(),
                            self.format_type(&lhs.ty)
                        ),
                    ));
                    return None;
                }
                if matches!(
                    op,
                    BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge
                ) && !matches!(self.underlying_type(&lhs.ty), Type::Uint(_))
                {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        span,
                        format!(
                            "comparison `{}` requires `Uint` operands, found `{}`",
                            self.units.ast().token_tag(op_tok).as_str(),
                            self.format_type(&lhs.ty)
                        ),
                    ));
                    return None;
                }
                let ty = match op {
                    BinaryOp::Eq
                    | BinaryOp::Neq
                    | BinaryOp::Lt
                    | BinaryOp::Le
                    | BinaryOp::Gt
                    | BinaryOp::Ge
                    | BinaryOp::And
                    | BinaryOp::Or => Type::Boolean,
                    BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul => lhs.ty.clone(),
                };
                Some(Expr {
                    kind: ExprKind::Binary {
                        op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    },
                    ty,
                    span,
                })
            }
            NodeTag::TernaryExpr => {
                let t = self.units.ast().ternary_expr(node);
                let cond = self.check_expr(t.cond, scope, Some(&Type::Boolean))?;
                if *self.underlying_type(&cond.ty) != Type::Boolean {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        cond.span,
                        format!(
                            "ternary condition must be `Boolean`, found `{}`",
                            self.format_type(&cond.ty)
                        ),
                    ));
                    return None;
                }
                let then_branch = self.check_expr(t.then_branch, scope, expected)?;
                let mut else_branch =
                    self.check_expr(t.else_branch, scope, Some(&then_branch.ty))?;
                if !self.coerce_or_check(&mut else_branch, &then_branch.ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        span,
                        format!(
                            "ternary branches have incompatible types `{}` and `{}`",
                            self.format_type(&then_branch.ty),
                            self.format_type(&else_branch.ty)
                        ),
                    ));
                    return None;
                }
                let ty = then_branch.ty.clone();
                Some(Expr {
                    kind: ExprKind::Ternary {
                        cond: Box::new(cond),
                        then_branch: Box::new(then_branch),
                        else_branch: Box::new(else_branch),
                    },
                    ty,
                    span,
                })
            }
            NodeTag::CastExpr => {
                let data = self.units.ast().node_data(node);
                let target = self.resolve_type(NodeIndex(data.rhs))?;
                let mut inner = self.check_expr(NodeIndex(data.lhs), scope, None)?;
                let dst_u = self.underlying_type(&target).clone();
                // Allow tuple literals like `[1, 2, 3, 4] as Bytes<4>` or `[1, 2] as Vector<2, Uint<32>>`
                // by coercing the tuple to the appropriate vector type before casting.
                if let Type::Bytes(n) = &dst_u
                    && let Type::Tuple(ref elems) = *self.underlying_type(&inner.ty)
                    && elems.len() == *n as usize
                {
                    let vec_u8 = Type::Vector(*n, Box::new(Type::Uint(8)));
                    let _ = self.coerce_or_check(&mut inner, &vec_u8);
                } else if let Type::Vector(n, ref elem_ty) = dst_u
                    && let Type::Tuple(ref elems) = *self.underlying_type(&inner.ty)
                    && elems.len() == n as usize
                {
                    let vec_t = Type::Vector(n, elem_ty.clone());
                    let _ = self.coerce_or_check(&mut inner, &vec_t);
                }
                let src_u = self.underlying_type(&inner.ty);
                let valid = inner.ty == target
                    || *src_u == dst_u
                    || matches!(
                        (src_u, &dst_u),
                        (
                            Type::Uint(_),
                            Type::Field | Type::Uint(_) | Type::Boolean | Type::Enum(_)
                        ) | (
                            Type::Field,
                            Type::Uint(_) | Type::Field | Type::Boolean | Type::Enum(_)
                        ) | (Type::Boolean, Type::Field | Type::Uint(_) | Type::Boolean)
                            | (Type::Enum(_), Type::Field | Type::Uint(_))
                            | (Type::Contract(_), Type::Contract(_))
                            | (
                                Type::Field | Type::Uint(_) | Type::Boolean | Type::Enum(_),
                                Type::CurveField(CurveFieldKind::JubjubScalar)
                            )
                            | (
                                Type::CurveField(CurveFieldKind::JubjubScalar),
                                Type::Field | Type::Uint(_)
                            )
                            | (Type::CurveField(_), Type::Bytes(32))
                            | (Type::Bytes(32), Type::CurveField(_))
                            | (
                                Type::Bytes(64),
                                Type::CurveField(CurveFieldKind::Curve25519Scalar)
                            )
                    )
                    || matches!(
                        (src_u, &dst_u),
                        (Type::Bytes(n), Type::Field | Type::Uint(_)) if *n <= 31
                    )
                    || matches!(
                        (src_u, &dst_u),
                        (Type::Field, Type::Bytes(n)) if *n <= 32
                    )
                    || matches!((src_u, &dst_u), (Type::Uint(_), Type::Bytes(_)))
                    || matches!(
                        (src_u, &dst_u),
                        (Type::Bytes(n), Type::Vector(m, elem))
                            if n == m && matches!(self.underlying_type(elem), Type::Uint(bits) if *bits >= 8)
                    )
                    || matches!(
                        (src_u, &dst_u),
                        (Type::Bytes(n), Type::Tuple(elems))
                            if *n as usize == elems.len()
                                && elems.iter().all(|e| matches!(self.underlying_type(e), Type::Field | Type::Uint(8..=248)))
                    )
                    || matches!(
                        (src_u, &dst_u),
                        (Type::Vector(n, elem), Type::Bytes(m))
                            if n == m && matches!(self.underlying_type(elem), Type::Uint(bits) if *bits <= 8)
                    )
                    || matches!(
                        (src_u, &dst_u),
                        (Type::Tuple(elems), Type::Bytes(m))
                            if elems.len() == *m as usize
                                && elems.iter().all(|e| matches!(self.underlying_type(e), Type::Uint(bits) if *bits <= 8))
                    )
                    || matches!(
                        (src_u, &dst_u),
                        (Type::Vector(n, s_elem), Type::Vector(m, d_elem))
                            if n == m && self.can_implicitly_widen(s_elem, d_elem)
                    )
                    || matches!(
                        (src_u, &dst_u),
                        (Type::Vector(n, s_elem), Type::Tuple(d_elems))
                            if *n as usize == d_elems.len()
                                && d_elems.iter().all(|d| self.can_implicitly_widen(s_elem, d))
                    )
                    || matches!(
                        (src_u, &dst_u),
                        (Type::Tuple(s_elems), Type::Vector(n, d_elem))
                            if s_elems.len() == *n as usize
                                && s_elems.iter().all(|s| self.can_implicitly_widen(s, d_elem))
                    )
                    || matches!(
                        (src_u, &dst_u),
                        (Type::Struct(a), Type::Struct(b))
                            if self.structs_structurally_equal(*a, *b)
                    )
                    || matches!(
                        (src_u, &dst_u),
                        (Type::Enum(a), Type::Enum(b))
                            if self.enums_structurally_equal(*a, *b)
                    )
                    || matches!(
                        (src_u, &dst_u),
                        (Type::Tuple(s_elems), Type::Tuple(d_elems))
                            if s_elems.len() == d_elems.len()
                                && s_elems
                                    .iter()
                                    .zip(d_elems.iter())
                                    .all(|(s, d)| self.can_implicitly_widen(s, d))
                    );
                if !valid {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        span,
                        format!(
                            "cannot cast `{}` to `{}`",
                            self.format_type(&inner.ty),
                            self.format_type(&target)
                        ),
                    ));
                    return None;
                }
                Some(Expr {
                    kind: ExprKind::Cast {
                        expr: Box::new(inner),
                        target: target.clone(),
                    },
                    ty: target,
                    span,
                })
            }
            NodeTag::AssertExpr => {
                let a = self.units.ast().assert_expr(node);
                let cond = self.check_expr(a.cond, scope, Some(&Type::Boolean))?;
                if cond.ty != Type::Boolean {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        cond.span,
                        format!(
                            "`assert` condition must be `Boolean`, found `{}`",
                            self.format_type(&cond.ty)
                        ),
                    ));
                    return None;
                }
                if self.units.ast().node_tag(a.msg) != NodeTag::StringLitExpr {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        self.units.ast().node_span(a.msg),
                        "`assert` message must be a string literal",
                    ));
                    return None;
                }
                let raw_msg = self.text(self.units.ast().node_main_token(a.msg));
                let message = unquote_string(raw_msg);
                Some(Expr {
                    kind: ExprKind::Assert {
                        cond: Box::new(cond),
                        message,
                    },
                    ty: Type::unit(),
                    span,
                })
            }
            NodeTag::DiscloseExpr => {
                let data = self.units.ast().node_data(node);
                let inner = self.check_expr(NodeIndex(data.lhs), scope, expected)?;
                let ty = inner.ty.clone();
                Some(Expr {
                    kind: ExprKind::Disclose(Box::new(inner)),
                    ty,
                    span,
                })
            }
            NodeTag::GenericCallExpr => {
                let call = self.units.ast().generic_call_expr(node);
                let targ_nodes: Vec<_> = self
                    .units
                    .ast()
                    .extra_nodes(call.targs_start, call.targs_end)
                    .collect();
                let arg_nodes: Vec<_> = self
                    .units
                    .ast()
                    .extra_nodes(call.args_start, call.args_end)
                    .collect();
                if self.units.ast().node_tag(call.callee) == NodeTag::IdentExpr {
                    let callee_tok = self.units.ast().node_main_token(call.callee);
                    let callee_name = self.text(callee_tok).to_owned();
                    let callee_span = self.units.ast().token_span(callee_tok);
                    if let Some(gids) = self.scope.generic_circuits.get(&callee_name).cloned() {
                        return self.resolve_generic_circuit_overload(
                            &callee_name,
                            &gids,
                            &targ_nodes,
                            &arg_nodes,
                            span,
                            scope,
                        );
                    }
                    if !self.has_user_callable(&callee_name)
                        && self.is_deprecated_stdlib_alias(&callee_name)
                    {
                        let (canon, prefixed_new) =
                            self.resolve_fixup_stdlib_alias(&callee_name, callee_span)?;
                        if let Some(gids) = self.scope.generic_circuits.get(&prefixed_new).cloned()
                        {
                            let std_gids: Vec<usize> = gids
                                .into_iter()
                                .filter(|&gid| {
                                    Some(self.generic_circuits[gid].unit) == self.stdlib_unit
                                })
                                .collect();
                            if !std_gids.is_empty() {
                                return self.resolve_generic_circuit_overload(
                                    &canon,
                                    &std_gids,
                                    &targ_nodes,
                                    &arg_nodes,
                                    span,
                                    scope,
                                );
                            }
                        }
                        if let Some(std_gids) = self
                            .stdlib_exports
                            .as_ref()
                            .and_then(|s| s.generic_circuits.get(&canon))
                            .cloned()
                        {
                            return self.resolve_generic_circuit_overload(
                                &canon,
                                &std_gids,
                                &targ_nodes,
                                &arg_nodes,
                                span,
                                scope,
                            );
                        }
                        return self.check_generic_builtin(
                            &canon,
                            callee_span,
                            &targ_nodes,
                            &arg_nodes,
                            span,
                            scope,
                        );
                    }
                    let builtin_name = self
                        .strip_stdlib_prefix(&callee_name)
                        .map(|(_, rest)| rest.to_owned())
                        .unwrap_or(callee_name);
                    return self.check_generic_builtin(
                        &builtin_name,
                        callee_span,
                        &targ_nodes,
                        &arg_nodes,
                        span,
                        scope,
                    );
                }
                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    span,
                    "unsupported generic call target",
                ));
                None
            }
            NodeTag::CallExpr => {
                let call = self.units.ast().call_expr(node);
                let arg_nodes: Vec<_> = self
                    .units
                    .ast()
                    .extra_nodes(call.args_start, call.args_end)
                    .collect();

                // 1. Direct identifier call: builtins (`pad`, `map`, `fold`, `degradeToTransient`,
                // `upgradeFromTransient`), circuit call, or witness call.
                if self.units.ast().node_tag(call.callee) == NodeTag::IdentExpr {
                    let callee_tok = self.units.ast().node_main_token(call.callee);
                    let raw_callee_name = self.text(callee_tok).to_owned();
                    let callee_span = self.units.ast().token_span(callee_tok);
                    let (callee_name, circuit_lookup_name, alias_canon) = if !self
                        .has_user_callable(&raw_callee_name)
                        && self.is_deprecated_stdlib_alias(&raw_callee_name)
                    {
                        let (canon, prefixed_new) =
                            self.resolve_fixup_stdlib_alias(&raw_callee_name, callee_span)?;
                        (canon.clone(), prefixed_new, Some(canon))
                    } else {
                        let stripped = self
                            .strip_stdlib_prefix(&raw_callee_name)
                            .map(|(_, rest)| rest.to_owned())
                            .unwrap_or_else(|| raw_callee_name.clone());
                        (stripped, raw_callee_name.clone(), None)
                    };
                    match callee_name.as_str() {
                        "pad" => return self.check_pad_call(&arg_nodes, span),
                        "map" => return self.check_map_call(&arg_nodes, span, scope),
                        "fold" => return self.check_fold_call(&arg_nodes, span, scope),
                        "degradeToTransient" => {
                            if arg_nodes.len() != 1 {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    span,
                                    format!(
                                        "`degradeToTransient` expects 1 argument, found {}",
                                        arg_nodes.len()
                                    ),
                                ));
                                return None;
                            }
                            let expected = Type::Bytes(32);
                            let mut arg = self.check_expr(arg_nodes[0], scope, Some(&expected))?;
                            if !self.coerce_or_check(&mut arg, &expected) {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    arg.span,
                                    format!(
                                        "`degradeToTransient` expects `Bytes<32>`, found `{}`",
                                        self.format_type(&arg.ty)
                                    ),
                                ));
                                return None;
                            }
                            return Some(Expr {
                                kind: ExprKind::DegradeToTransient(Box::new(arg)),
                                ty: Type::Field,
                                span,
                            });
                        }
                        "upgradeFromTransient" => {
                            if arg_nodes.len() != 1 {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    span,
                                    format!(
                                        "`upgradeFromTransient` expects 1 argument, found {}",
                                        arg_nodes.len()
                                    ),
                                ));
                                return None;
                            }
                            let expected = Type::Field;
                            let mut arg = self.check_expr(arg_nodes[0], scope, Some(&expected))?;
                            if !self.coerce_or_check(&mut arg, &expected) {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    arg.span,
                                    format!(
                                        "`upgradeFromTransient` expects `Field`, found `{}`",
                                        self.format_type(&arg.ty)
                                    ),
                                ));
                                return None;
                            }
                            return Some(Expr {
                                kind: ExprKind::UpgradeFromTransient(Box::new(arg)),
                                ty: Type::Bytes(32),
                                span,
                            });
                        }
                        "neg" | "inv" => {
                            let is_inv = callee_name == "inv";
                            if arg_nodes.len() != 1 {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    span,
                                    format!(
                                        "`{callee_name}` expects 1 argument, found {}",
                                        arg_nodes.len()
                                    ),
                                ));
                                return None;
                            }
                            let arg = self.check_expr(arg_nodes[0], scope, None)?;
                            let arg_u = self.underlying_type(&arg.ty).clone();
                            if !matches!(arg_u, Type::CurveField(f) if f.is_foreign()) {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    arg.span,
                                    format!(
                                        "`{callee_name}` expects a foreign field element, found `{}`",
                                        self.format_type(&arg.ty)
                                    ),
                                ));
                                return None;
                            }
                            let ty = arg.ty.clone();
                            let kind = if is_inv {
                                ExprKind::FieldInv(Box::new(arg))
                            } else {
                                ExprKind::Unary {
                                    op: UnaryOp::Neg,
                                    operand: Box::new(arg),
                                }
                            };
                            return Some(Expr { kind, ty, span });
                        }
                        "ecAdd" => {
                            if arg_nodes.len() != 2 {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    span,
                                    format!(
                                        "`ecAdd` expects 2 arguments, found {}",
                                        arg_nodes.len()
                                    ),
                                ));
                                return None;
                            }
                            let lhs = self.check_expr(arg_nodes[0], scope, None)?;
                            let rhs = self.check_expr(arg_nodes[1], scope, Some(&lhs.ty))?;
                            let lhs_u = self.underlying_type(&lhs.ty).clone();
                            let rhs_u = self.underlying_type(&rhs.ty).clone();
                            let Type::CurvePoint(curve) = lhs_u else {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    lhs.span,
                                    format!(
                                        "`ecAdd` expects elliptic curve points, found `{}`",
                                        self.format_type(&lhs.ty)
                                    ),
                                ));
                                return None;
                            };
                            if rhs_u != Type::CurvePoint(curve) {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    rhs.span,
                                    format!(
                                        "`ecAdd` curve mismatch: expected `{}`, found `{}`",
                                        curve.point_type_name(),
                                        self.format_type(&rhs.ty)
                                    ),
                                ));
                                return None;
                            }
                            return Some(Expr {
                                kind: ExprKind::EcAdd {
                                    lhs: Box::new(lhs),
                                    rhs: Box::new(rhs),
                                },
                                ty: Type::CurvePoint(curve),
                                span,
                            });
                        }
                        "ecNeg" => {
                            if arg_nodes.len() != 1 {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    span,
                                    format!(
                                        "`ecNeg` expects 1 argument, found {}",
                                        arg_nodes.len()
                                    ),
                                ));
                                return None;
                            }
                            let expected = Type::CurvePoint(CurveKind::Jubjub);
                            let arg = self.check_expr(arg_nodes[0], scope, Some(&expected))?;
                            if *self.underlying_type(&arg.ty) != expected {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    arg.span,
                                    format!(
                                        "`ecNeg` expects `JubjubPoint`, found `{}`",
                                        self.format_type(&arg.ty)
                                    ),
                                ));
                                return None;
                            }
                            return Some(Expr {
                                kind: ExprKind::EcNeg(Box::new(arg)),
                                ty: expected,
                                span,
                            });
                        }
                        "ecMul" => {
                            if arg_nodes.len() != 2 {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    span,
                                    format!(
                                        "`ecMul` expects 2 arguments, found {}",
                                        arg_nodes.len()
                                    ),
                                ));
                                return None;
                            }
                            let point = self.check_expr(arg_nodes[0], scope, None)?;
                            let point_u = self.underlying_type(&point.ty).clone();
                            let Type::CurvePoint(curve) = point_u else {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    point.span,
                                    format!(
                                        "`ecMul` first argument must be an elliptic curve point, found `{}`",
                                        self.format_type(&point.ty)
                                    ),
                                ));
                                return None;
                            };
                            let expected_scalar = Type::CurveField(curve.scalar_field());
                            let scalar =
                                self.check_expr(arg_nodes[1], scope, Some(&expected_scalar))?;
                            if *self.underlying_type(&scalar.ty) != expected_scalar {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    scalar.span,
                                    format!(
                                        "`ecMul` scalar mismatch: expected `{}`, found `{}`",
                                        curve.scalar_field().type_name(),
                                        self.format_type(&scalar.ty)
                                    ),
                                ));
                                return None;
                            }
                            return Some(Expr {
                                kind: ExprKind::EcMul {
                                    point: Box::new(point),
                                    scalar: Box::new(scalar),
                                },
                                ty: Type::CurvePoint(curve),
                                span,
                            });
                        }
                        "ecMulGenerator" => {
                            if arg_nodes.len() != 1 {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    span,
                                    format!(
                                        "`ecMulGenerator` expects 1 argument, found {}",
                                        arg_nodes.len()
                                    ),
                                ));
                                return None;
                            }
                            let scalar = self.check_expr(arg_nodes[0], scope, None)?;
                            let scalar_u = self.underlying_type(&scalar.ty).clone();
                            let curve = match scalar_u {
                                Type::CurveField(f) => f.scalar_curve(),
                                _ => None,
                            };
                            let Some(curve) = curve else {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    scalar.span,
                                    format!(
                                        "`ecMulGenerator` expects a curve scalar field, found `{}`",
                                        self.format_type(&scalar.ty)
                                    ),
                                ));
                                return None;
                            };
                            return Some(Expr {
                                kind: ExprKind::EcMulGenerator(Box::new(scalar)),
                                ty: Type::CurvePoint(curve),
                                span,
                            });
                        }
                        "constructJubjubPoint" => {
                            if arg_nodes.len() != 2 {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    span,
                                    format!(
                                        "`constructJubjubPoint` expects 2 arguments, found {}",
                                        arg_nodes.len()
                                    ),
                                ));
                                return None;
                            }
                            let mut x = self.check_expr(arg_nodes[0], scope, Some(&Type::Field))?;
                            let mut y = self.check_expr(arg_nodes[1], scope, Some(&Type::Field))?;
                            if !self.coerce_or_check(&mut x, &Type::Field) {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    x.span,
                                    format!(
                                        "`constructJubjubPoint` x coordinate expects `Field`, found `{}`",
                                        self.format_type(&x.ty)
                                    ),
                                ));
                                return None;
                            }
                            if !self.coerce_or_check(&mut y, &Type::Field) {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    y.span,
                                    format!(
                                        "`constructJubjubPoint` y coordinate expects `Field`, found `{}`",
                                        self.format_type(&y.ty)
                                    ),
                                ));
                                return None;
                            }
                            return Some(Expr {
                                kind: ExprKind::ConstructJubjubPoint {
                                    x: Box::new(x),
                                    y: Box::new(y),
                                },
                                ty: Type::CurvePoint(CurveKind::Jubjub),
                                span,
                            });
                        }
                        "jubjubPointX" | "jubjubPointY" | "secp256k1PointX" | "secp256k1PointY"
                        | "secp256r1PointX" | "secp256r1PointY" | "curve25519PointX"
                        | "curve25519PointY" => {
                            let (curve, is_y) = match callee_name.as_str() {
                                "jubjubPointX" => (CurveKind::Jubjub, false),
                                "jubjubPointY" => (CurveKind::Jubjub, true),
                                "secp256k1PointX" => (CurveKind::Secp256k1, false),
                                "secp256k1PointY" => (CurveKind::Secp256k1, true),
                                "secp256r1PointX" => (CurveKind::Secp256r1, false),
                                "secp256r1PointY" => (CurveKind::Secp256r1, true),
                                "curve25519PointX" => (CurveKind::Curve25519, false),
                                "curve25519PointY" => (CurveKind::Curve25519, true),
                                _ => unreachable!(),
                            };
                            if arg_nodes.len() != 1 {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    span,
                                    format!(
                                        "`{callee_name}` expects 1 argument, found {}",
                                        arg_nodes.len()
                                    ),
                                ));
                                return None;
                            }
                            let expected = Type::CurvePoint(curve);
                            let pt = self.check_expr(arg_nodes[0], scope, Some(&expected))?;
                            if *self.underlying_type(&pt.ty) != expected {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    pt.span,
                                    format!(
                                        "`{callee_name}` expects `{}`, found `{}`",
                                        curve.point_type_name(),
                                        self.format_type(&pt.ty)
                                    ),
                                ));
                                return None;
                            }
                            return Some(Expr {
                                kind: ExprKind::PointCoord {
                                    point: Box::new(pt),
                                    is_y,
                                },
                                ty: curve.coord_type(),
                                span,
                            });
                        }
                        "ownPublicKey" if self.scope.has_stdlib => {
                            if !arg_nodes.is_empty() {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    span,
                                    format!(
                                        "`ownPublicKey` expects 0 arguments, found {}",
                                        arg_nodes.len()
                                    ),
                                ));
                                return None;
                            }
                            let ret_ty = self.resolve_stdlib_struct("ZswapCoinPublicKey", span)?;
                            return Some(Expr {
                                kind: ExprKind::NativeWitness {
                                    kind: NativeWitnessKind::OwnPublicKey,
                                    args: Vec::new(),
                                },
                                ty: ret_ty,
                                span,
                            });
                        }
                        "createZswapInput" if self.scope.has_stdlib => {
                            if arg_nodes.len() != 1 {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    span,
                                    format!(
                                        "`createZswapInput` expects 1 argument, found {}",
                                        arg_nodes.len()
                                    ),
                                ));
                                return None;
                            }
                            let expected =
                                self.resolve_stdlib_struct("QualifiedShieldedCoinInfo", span)?;
                            let mut arg = self.check_expr(arg_nodes[0], scope, Some(&expected))?;
                            if !self.coerce_or_check(&mut arg, &expected) {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    arg.span,
                                    format!(
                                        "`createZswapInput` expects `QualifiedShieldedCoinInfo`, found `{}`",
                                        self.format_type(&arg.ty)
                                    ),
                                ));
                                return None;
                            }
                            return Some(Expr {
                                kind: ExprKind::NativeWitness {
                                    kind: NativeWitnessKind::CreateZswapInput,
                                    args: vec![arg],
                                },
                                ty: Type::unit(),
                                span,
                            });
                        }
                        "createZswapOutput" if self.scope.has_stdlib => {
                            if arg_nodes.len() != 2 {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    span,
                                    format!(
                                        "`createZswapOutput` expects 2 arguments, found {}",
                                        arg_nodes.len()
                                    ),
                                ));
                                return None;
                            }
                            let coin_ty = self.resolve_stdlib_struct("ShieldedCoinInfo", span)?;
                            let pk_ty = self.resolve_stdlib_struct("ZswapCoinPublicKey", span)?;
                            let addr_ty = self.resolve_stdlib_struct("ContractAddress", span)?;
                            let recip_ty = Type::Either(Box::new(pk_ty), Box::new(addr_ty));
                            let mut coin = self.check_expr(arg_nodes[0], scope, Some(&coin_ty))?;
                            if !self.coerce_or_check(&mut coin, &coin_ty) {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    coin.span,
                                    format!(
                                        "`createZswapOutput` expects `ShieldedCoinInfo`, found `{}`",
                                        self.format_type(&coin.ty)
                                    ),
                                ));
                                return None;
                            }
                            let mut recip =
                                self.check_expr(arg_nodes[1], scope, Some(&recip_ty))?;
                            if !self.coerce_or_check(&mut recip, &recip_ty) {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    recip.span,
                                    format!(
                                        "`createZswapOutput` expects `{}`, found `{}`",
                                        self.format_type(&recip_ty),
                                        self.format_type(&recip.ty)
                                    ),
                                ));
                                return None;
                            }
                            return Some(Expr {
                                kind: ExprKind::NativeWitness {
                                    kind: NativeWitnessKind::CreateZswapOutput,
                                    args: vec![coin, recip],
                                },
                                ty: Type::unit(),
                                span,
                            });
                        }
                        _ => {}
                    }
                    let mut candidates: Vec<CircuitId> = if alias_canon.is_some() {
                        Vec::new()
                    } else {
                        self.scope
                            .circuits
                            .get(&circuit_lookup_name)
                            .cloned()
                            .unwrap_or_default()
                    };
                    let generic_gids: Vec<usize> = if let Some(ref canon) = alias_canon {
                        self.stdlib_exports
                            .as_ref()
                            .and_then(|s| s.generic_circuits.get(canon))
                            .cloned()
                            .unwrap_or_default()
                    } else {
                        self.scope
                            .generic_circuits
                            .get(&circuit_lookup_name)
                            .cloned()
                            .unwrap_or_default()
                    };
                    for gid in generic_gids {
                        if self.generic_circuits[gid].gparams.is_empty()
                            && let Some(cid) = self.instantiate_generic_circuit(gid, &[], span)
                        {
                            candidates.push(cid);
                        }
                    }
                    if !candidates.is_empty() {
                        return self.resolve_circuit_overload(
                            &circuit_lookup_name,
                            &candidates,
                            &arg_nodes,
                            span,
                            scope,
                        );
                    }
                    if alias_canon.is_none()
                        && let Some(&wid) = self.scope.witnesses.get(&circuit_lookup_name)
                    {
                        return self.check_witness_call(wid, &arg_nodes, span, scope);
                    }
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        callee_span,
                        format!("unknown circuit or witness `{raw_callee_name}`"),
                    ));
                    return None;
                }

                // 2. Ledger ADT method call (or cross-contract call on a ledger cell / expression).
                if self.units.ast().node_tag(call.callee) == NodeTag::MemberExpr {
                    let mdata = self.units.ast().node_data(call.callee);
                    let recv = NodeIndex(mdata.lhs);
                    let method_tok = TokenIndex(mdata.rhs);
                    let method_name = self.text(method_tok).to_owned();
                    let method_span = self.units.ast().token_span(method_tok);
                    if let Some((field_id, key_path, target_adt)) =
                        self.try_extract_ledger_chain(recv, scope)
                    {
                        // If the ledger target is a Cell holding a Contract reference and the
                        // method is not a Cell operation, auto-read the cell and make a cross-contract call.
                        let canonical_method = aliases::lookup_ledger_op_alias(&method_name)
                            .unwrap_or(method_name.as_str());
                        if let LedgerAdt::Cell(ref cell_ty) = target_adt
                            && !matches!(
                                canonical_method,
                                "read" | "write" | "writeCoin" | "resetToDefault"
                            )
                            && let Type::Contract(cid) = *self.underlying_type(cell_ty)
                        {
                            let recv_expr = Expr {
                                kind: ExprKind::LedgerCall {
                                    field: field_id,
                                    key_path,
                                    target_adt: target_adt.clone(),
                                    op: LedgerOp::CellRead,
                                    args: Vec::new(),
                                },
                                ty: (**cell_ty).clone(),
                                span: self.units.ast().node_span(recv),
                            };
                            return self.check_contract_call(
                                cid,
                                recv_expr,
                                &method_name,
                                method_span,
                                &arg_nodes,
                                span,
                                scope,
                            );
                        }
                        return self.check_ledger_call(
                            field_id,
                            key_path,
                            target_adt,
                            &method_name,
                            method_span,
                            &arg_nodes,
                            span,
                            scope,
                        );
                    }
                    let recv_expr = self.check_expr(recv, scope, None)?;
                    if let Type::Contract(cid) = *self.underlying_type(&recv_expr.ty) {
                        return self.check_contract_call(
                            cid,
                            recv_expr,
                            &method_name,
                            method_span,
                            &arg_nodes,
                            span,
                            scope,
                        );
                    }
                }

                // 3. Direct arrow invocation `((x) => ...)(arg)` or `() => { ... }()`.
                if self.units.ast().node_tag(call.callee) == NodeTag::ArrowExpr {
                    let mut arg_exprs = Vec::with_capacity(arg_nodes.len());
                    for &anode in &arg_nodes {
                        arg_exprs.push(self.check_expr(anode, scope, None)?);
                    }
                    return self.eval_higher_order_call(call.callee, arg_exprs, span, scope);
                }

                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    span,
                    "unsupported call target",
                ));
                None
            }
            NodeTag::EmitExpr => {
                let data = self.units.ast().node_data(node);
                let val = self.check_expr(NodeIndex(data.lhs), scope, None)?;
                let event_ty = val.ty.clone();
                let event_name = match self.underlying_type(&event_ty) {
                    Type::Struct(sid) => self.structs[sid.0 as usize].name.clone(),
                    _ => {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            val.span,
                            format!(
                                "`emit` expects a declared event struct, found `{}`",
                                self.format_type(&event_ty)
                            ),
                        ));
                        return None;
                    }
                };
                let Some(event_tag) = event_tag_of(&event_name) else {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        val.span,
                        format!("`{event_name}` is not a declared Midnight event type"),
                    ));
                    return None;
                };
                let Some(payload_len) = self.serialized_byte_len(&event_ty) else {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        val.span,
                        format!("event type `{event_name}` is not serializable"),
                    ));
                    return None;
                };
                Some(Expr {
                    kind: ExprKind::Emit {
                        event_name,
                        event_tag,
                        payload_len,
                        event_ty,
                        value: Box::new(val),
                    },
                    ty: Type::unit(),
                    span,
                })
            }
            _ => {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    span,
                    "unsupported expression",
                ));
                None
            }
        }
    }

    fn check_pad_call(&mut self, arg_nodes: &[NodeIndex], call_span: Span) -> Option<Expr> {
        if arg_nodes.len() != 2 {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                call_span,
                format!(
                    "`pad` expects 2 arguments (length, string), found {}",
                    arg_nodes.len()
                ),
            ));
            return None;
        }
        if self.units.ast().node_tag(arg_nodes[0]) != NodeTag::IntLitExpr {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                self.units.ast().node_span(arg_nodes[0]),
                "`pad` length must be an integer literal",
            ));
            return None;
        }
        let len: u32 = match compact_ast::parse_nat_u32(
            self.text(self.units.ast().node_main_token(arg_nodes[0])),
        ) {
            Some(n) => n,
            None => {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    self.units.ast().node_span(arg_nodes[0]),
                    "invalid `pad` length",
                ));
                return None;
            }
        };
        if self.units.ast().node_tag(arg_nodes[1]) != NodeTag::StringLitExpr {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                self.units.ast().node_span(arg_nodes[1]),
                "`pad` second argument must be a string literal",
            ));
            return None;
        }
        let raw_bytes = compact_ast::unescape_string_bytes(
            self.text(self.units.ast().node_main_token(arg_nodes[1])),
        );
        if raw_bytes.len() > len as usize {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                self.units.ast().node_span(arg_nodes[1]),
                format!(
                    "string of length {} exceeds `pad` target length {len}",
                    raw_bytes.len()
                ),
            ));
            return None;
        }
        let mut padded = vec![0u8; len as usize];
        padded[..raw_bytes.len()].copy_from_slice(&raw_bytes);
        Some(Expr {
            kind: ExprKind::BytesLit(padded),
            ty: Type::Bytes(len),
            span: call_span,
        })
    }

    fn eval_higher_order_call(
        &mut self,
        fn_node: NodeIndex,
        arg_exprs: Vec<Expr>,
        call_span: Span,
        scope: &HashMap<String, ValueBinding>,
    ) -> Option<Expr> {
        match self.units.ast().node_tag(fn_node) {
            NodeTag::IdentExpr => {
                let tok = self.units.ast().node_main_token(fn_node);
                let raw_name = self.text(tok).to_owned();
                let tok_span = self.units.ast().token_span(tok);
                let (name, alias_canon) = if !self.has_user_callable(&raw_name)
                    && self.is_deprecated_stdlib_alias(&raw_name)
                {
                    let (canon, prefixed_new) =
                        self.resolve_fixup_stdlib_alias(&raw_name, tok_span)?;
                    (prefixed_new, Some(canon))
                } else {
                    (raw_name.clone(), None)
                };
                let mut cids: Vec<CircuitId> = if alias_canon.is_some() {
                    Vec::new()
                } else {
                    self.scope.circuits.get(&name).cloned().unwrap_or_default()
                };
                let generic_gids: Vec<usize> = if let Some(ref canon) = alias_canon {
                    self.stdlib_exports
                        .as_ref()
                        .and_then(|s| s.generic_circuits.get(canon))
                        .cloned()
                        .unwrap_or_default()
                } else {
                    self.scope
                        .generic_circuits
                        .get(&name)
                        .cloned()
                        .unwrap_or_default()
                };
                for gid in generic_gids {
                    if self.generic_circuits[gid].gparams.is_empty()
                        && let Some(cid) = self.instantiate_generic_circuit(gid, &[], call_span)
                    {
                        cids.push(cid);
                    }
                }
                if cids.is_empty() {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        tok_span,
                        format!("unknown circuit `{raw_name}` passed to higher-order builtin"),
                    ));
                    return None;
                }
                let cid = cids
                    .iter()
                    .copied()
                    .find(|&c| self.circuit_sigs[c.0 as usize].params.len() == arg_exprs.len())
                    .unwrap_or(cids[0]);
                let expected_params: Vec<Type> = self.circuit_sigs[cid.0 as usize]
                    .params
                    .iter()
                    .map(|p| p.ty.clone())
                    .collect();
                let ret_type = self.circuit_sigs[cid.0 as usize].ret_type.clone();
                if arg_exprs.len() != expected_params.len() {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        format!(
                            "circuit `{name}` expects {} argument(s), found {}",
                            expected_params.len(),
                            arg_exprs.len()
                        ),
                    ));
                    return None;
                }
                let mut coerced = Vec::with_capacity(arg_exprs.len());
                for (mut arg, expected_ty) in arg_exprs.into_iter().zip(&expected_params) {
                    if !self.coerce_or_check(&mut arg, expected_ty) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            arg.span,
                            format!(
                                "argument type mismatch calling `{name}`: expected `{}`, found `{}`",
                                self.format_type(expected_ty),
                                self.format_type(&arg.ty)
                            ),
                        ));
                        return None;
                    }
                    coerced.push(arg);
                }
                Some(Expr {
                    kind: ExprKind::CircuitCall {
                        circuit: cid,
                        args: coerced,
                    },
                    ty: ret_type,
                    span: call_span,
                })
            }
            NodeTag::ArrowExpr => {
                let arrow = self.units.ast().arrow_expr(fn_node);
                let param_nodes: Vec<_> = self
                    .units
                    .ast()
                    .extra_nodes(arrow.params_start, arrow.params_end)
                    .collect();
                if param_nodes.len() != arg_exprs.len() {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        format!(
                            "arrow circuit expects {} argument(s), found {}",
                            param_nodes.len(),
                            arg_exprs.len()
                        ),
                    ));
                    return None;
                }
                let annotated_ret = match arrow.ret_type {
                    Some(rt) => Some(self.resolve_type(rt)?),
                    None => None,
                };
                let mut inner_scope = scope.clone();
                let mut stmts = Vec::with_capacity(param_nodes.len());
                for (pnode, mut arg) in param_nodes.into_iter().zip(arg_exprs) {
                    let p = self.units.ast().param(pnode);
                    let pname = self.text(p.name_token).to_owned();
                    let pty = if p.type_node.is_some() {
                        let expected_ty = self.resolve_type(p.type_node)?;
                        if !self.coerce_or_check(&mut arg, &expected_ty) {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                arg.span,
                                format!(
                                    "arrow parameter `{pname}` expects `{}`, found `{}`",
                                    self.format_type(&expected_ty),
                                    self.format_type(&arg.ty)
                                ),
                            ));
                            return None;
                        }
                        expected_ty
                    } else {
                        arg.ty.clone()
                    };
                    let local = self.alloc_local();
                    let pspan = self.units.ast().node_span(pnode);
                    inner_scope.insert(pname.clone(), ValueBinding::Local(local, pty.clone()));
                    stmts.push(Stmt::Const {
                        local,
                        name: pname,
                        ty: pty,
                        init: arg,
                        span: pspan,
                    });
                }

                if self.units.ast().node_tag(arrow.body) == NodeTag::Block {
                    let block_data = self.units.ast().node_data(arrow.body);
                    let stmt_nodes: Vec<_> = self
                        .units
                        .ast()
                        .extra_nodes(block_data.lhs, block_data.rhs)
                        .collect();
                    let mut body_stmts = Vec::new();
                    let mut ret_val: Option<Expr> = None;
                    let mut ok = true;
                    self.block_consts.push(HashSet::new());
                    for (i, snode) in stmt_nodes.iter().copied().enumerate() {
                        if self.units.ast().node_tag(snode) == NodeTag::ReturnStmt
                            && i + 1 == stmt_nodes.len()
                        {
                            let rdata = self.units.ast().node_data(snode);
                            if let Some(enode) = NodeIndex(rdata.lhs).into_option() {
                                let Some(mut expr) =
                                    self.check_expr(enode, &inner_scope, annotated_ret.as_ref())
                                else {
                                    ok = false;
                                    break;
                                };
                                if let Some(ref rt) = annotated_ret {
                                    if !self.coerce_or_check(&mut expr, rt) {
                                        self.diagnostics.push(CompactDiagnostic::error(
                                            self.units.file(),
                                            expr.span,
                                            format!(
                                                "arrow return type mismatch: expected `{}`, found `{}`",
                                                self.format_type(rt),
                                                self.format_type(&expr.ty)
                                            ),
                                        ));
                                        ok = false;
                                        break;
                                    }
                                    expr.ty = rt.clone();
                                }
                                ret_val = Some(expr);
                            }
                        } else {
                            let expected_stmt_ret =
                                annotated_ret.clone().unwrap_or_else(Type::unit);
                            self.check_stmt(
                                snode,
                                &mut inner_scope,
                                &expected_stmt_ret,
                                &mut body_stmts,
                            );
                        }
                    }
                    self.block_consts.pop();
                    if !ok {
                        return None;
                    }
                    stmts.extend(body_stmts);
                    let tail = ret_val.unwrap_or_else(|| Expr {
                        kind: ExprKind::Tuple(Vec::new()),
                        ty: Type::unit(),
                        span: call_span,
                    });
                    let ty = tail.ty.clone();
                    Some(Expr {
                        kind: ExprKind::Block {
                            stmts,
                            tail: Box::new(tail),
                        },
                        ty,
                        span: call_span,
                    })
                } else {
                    let mut tail =
                        self.check_expr(arrow.body, &inner_scope, annotated_ret.as_ref())?;
                    if let Some(ref rt) = annotated_ret {
                        if !self.coerce_or_check(&mut tail, rt) {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                tail.span,
                                format!(
                                    "arrow return type mismatch: expected `{}`, found `{}`",
                                    self.format_type(rt),
                                    self.format_type(&tail.ty)
                                ),
                            ));
                            return None;
                        }
                        tail.ty = rt.clone();
                    }
                    let ty = tail.ty.clone();
                    Some(Expr {
                        kind: ExprKind::Block {
                            stmts,
                            tail: Box::new(tail),
                        },
                        ty,
                        span: call_span,
                    })
                }
            }
            _ => {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    self.units.ast().node_span(fn_node),
                    "expected circuit name or arrow expression `(...) => ...`",
                ));
                None
            }
        }
    }

    fn extract_vector_arg(
        &mut self,
        node: NodeIndex,
        scope: &HashMap<String, ValueBinding>,
        builtin: &str,
    ) -> Option<(Expr, u32, Type)> {
        let mut expr = self.check_expr(node, scope, None)?;
        let u = self.underlying_type(&expr.ty).clone();
        match u {
            Type::Vector(len, elem) => Some((expr, len, (*elem).clone())),
            Type::Bytes(len) => Some((expr, len, Type::Uint(8))),
            Type::Tuple(elems) if elems.is_empty() => Some((expr, 0, Type::unit())),
            Type::Tuple(elems) if elems.iter().all(|t| *t == elems[0]) => {
                let len = elems.len() as u32;
                let elem = elems[0].clone();
                let vec_ty = Type::Vector(len, Box::new(elem.clone()));
                let _ = self.coerce_or_check(&mut expr, &vec_ty);
                Some((expr, len, elem))
            }
            other => {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    expr.span,
                    format!(
                        "`{builtin}` vector argument must have `Vector<N, T>` or `Bytes<N>` type, found `{}`",
                        self.format_type(&other)
                    ),
                ));
                None
            }
        }
    }

    fn check_map_call(
        &mut self,
        arg_nodes: &[NodeIndex],
        call_span: Span,
        scope: &HashMap<String, ValueBinding>,
    ) -> Option<Expr> {
        if arg_nodes.len() < 2 {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                call_span,
                "`map(f, v1, ...)` expects a function and at least one `Vector` argument",
            ));
            return None;
        }
        let fn_node = arg_nodes[0];
        let mut prelude = Vec::new();
        let mut vec_locals: Vec<(LocalId, Type, Type, Span)> = Vec::new();
        let mut expected_len: Option<u32> = None;

        for &vnode in &arg_nodes[1..] {
            let (vexpr, len, elem_ty) = self.extract_vector_arg(vnode, scope, "map")?;
            if let Some(prev) = expected_len {
                if len != prev {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        vexpr.span,
                        format!(
                            "`map` vector length mismatch: expected length {prev}, found {len}"
                        ),
                    ));
                    return None;
                }
            } else {
                expected_len = Some(len);
            }
            let tmp = self.alloc_local();
            let vty = vexpr.ty.clone();
            let vspan = vexpr.span;
            prelude.push(Stmt::Const {
                local: tmp,
                name: format!("__map_v_{}", tmp.0),
                ty: vty.clone(),
                init: vexpr,
                span: vspan,
            });
            vec_locals.push((tmp, vty, elem_ty, vspan));
        }

        let len = expected_len.unwrap_or(0);
        let mut results = Vec::with_capacity(len as usize);
        let mut out_elem_ty: Option<Type> = None;
        for i in 0..len {
            let call_args: Vec<Expr> = vec_locals
                .iter()
                .map(|(lid, vty, ety, vspan)| Expr {
                    kind: ExprKind::Index {
                        base: Box::new(Expr {
                            kind: ExprKind::LocalRef(*lid),
                            ty: vty.clone(),
                            span: *vspan,
                        }),
                        index: Box::new(Expr {
                            kind: ExprKind::IntLit(i as u128),
                            ty: Type::Uint(64),
                            span: *vspan,
                        }),
                    },
                    ty: ety.clone(),
                    span: *vspan,
                })
                .collect();
            let res = self.eval_higher_order_call(fn_node, call_args, call_span, scope)?;
            if let Some(ref prev_ty) = out_elem_ty {
                if res.ty != *prev_ty {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        res.span,
                        format!(
                            "`map` element type mismatch: expected `{}`, found `{}`",
                            self.format_type(prev_ty),
                            self.format_type(&res.ty)
                        ),
                    ));
                    return None;
                }
            } else {
                out_elem_ty = Some(res.ty.clone());
            }
            results.push(res);
        }

        let elem_ty = out_elem_ty.unwrap_or_else(Type::unit);
        let vec_ty = Type::Vector(len, Box::new(elem_ty));
        let tail = Expr {
            kind: ExprKind::Vector(results),
            ty: vec_ty.clone(),
            span: call_span,
        };
        Some(Expr {
            kind: ExprKind::Block {
                stmts: prelude,
                tail: Box::new(tail),
            },
            ty: vec_ty,
            span: call_span,
        })
    }

    fn check_fold_call(
        &mut self,
        arg_nodes: &[NodeIndex],
        call_span: Span,
        scope: &HashMap<String, ValueBinding>,
    ) -> Option<Expr> {
        if arg_nodes.len() < 3 {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                call_span,
                "`fold(f, init, v1, ...)` expects a function, an initial accumulator, and at least one `Vector`",
            ));
            return None;
        }
        let fn_node = arg_nodes[0];
        let expected_init_ty: Option<Type> = match self.units.ast().node_tag(fn_node) {
            NodeTag::IdentExpr => {
                let name = self
                    .text(self.units.ast().node_main_token(fn_node))
                    .to_owned();
                self.scope
                    .circuits
                    .get(&name)
                    .and_then(|cids| cids.first())
                    .and_then(|&cid| self.circuit_sigs[cid.0 as usize].params.first())
                    .map(|p| p.ty.clone())
            }
            NodeTag::ArrowExpr => {
                let arrow = self.units.ast().arrow_expr(fn_node);
                let first_param = self
                    .units
                    .ast()
                    .extra_nodes(arrow.params_start, arrow.params_end)
                    .next();
                first_param.and_then(|pnode| {
                    let p = self.units.ast().param(pnode);
                    if p.type_node.is_some() {
                        self.resolve_type(p.type_node)
                    } else {
                        None
                    }
                })
            }
            _ => None,
        };
        let mut init_expr = self.check_expr(arg_nodes[1], scope, expected_init_ty.as_ref())?;
        if let Some(ref exp_ty) = expected_init_ty
            && self.coerce_or_check(&mut init_expr, exp_ty)
        {
            init_expr.ty = exp_ty.clone();
        }
        let mut prelude = Vec::new();
        let mut acc_local = self.alloc_local();
        let mut acc_ty = init_expr.ty.clone();
        let init_span = init_expr.span;
        prelude.push(Stmt::Const {
            local: acc_local,
            name: format!("__fold_acc_{}", acc_local.0),
            ty: acc_ty.clone(),
            init: init_expr,
            span: init_span,
        });

        let mut vec_locals: Vec<(LocalId, Type, Type, Span)> = Vec::new();
        let mut expected_len: Option<u32> = None;
        for &vnode in &arg_nodes[2..] {
            let (vexpr, len, elem_ty) = self.extract_vector_arg(vnode, scope, "fold")?;
            if let Some(prev) = expected_len {
                if len != prev {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        vexpr.span,
                        format!(
                            "`fold` vector length mismatch: expected length {prev}, found {len}"
                        ),
                    ));
                    return None;
                }
            } else {
                expected_len = Some(len);
            }
            let tmp = self.alloc_local();
            let vty = vexpr.ty.clone();
            let vspan = vexpr.span;
            prelude.push(Stmt::Const {
                local: tmp,
                name: format!("__fold_v_{}", tmp.0),
                ty: vty.clone(),
                init: vexpr,
                span: vspan,
            });
            vec_locals.push((tmp, vty, elem_ty, vspan));
        }

        let len = expected_len.unwrap_or(0);
        for i in 0..len {
            let mut call_args = Vec::with_capacity(1 + vec_locals.len());
            call_args.push(Expr {
                kind: ExprKind::LocalRef(acc_local),
                ty: acc_ty.clone(),
                span: call_span,
            });
            for (lid, vty, ety, vspan) in &vec_locals {
                call_args.push(Expr {
                    kind: ExprKind::Index {
                        base: Box::new(Expr {
                            kind: ExprKind::LocalRef(*lid),
                            ty: vty.clone(),
                            span: *vspan,
                        }),
                        index: Box::new(Expr {
                            kind: ExprKind::IntLit(i as u128),
                            ty: Type::Uint(64),
                            span: *vspan,
                        }),
                    },
                    ty: ety.clone(),
                    span: *vspan,
                });
            }
            let step = self.eval_higher_order_call(fn_node, call_args, call_span, scope)?;
            acc_ty = step.ty.clone();
            acc_local = self.alloc_local();
            prelude.push(Stmt::Const {
                local: acc_local,
                name: format!("__fold_acc_{}", acc_local.0),
                ty: acc_ty.clone(),
                init: step,
                span: call_span,
            });
        }

        let tail = Expr {
            kind: ExprKind::LocalRef(acc_local),
            ty: acc_ty.clone(),
            span: call_span,
        };
        Some(Expr {
            kind: ExprKind::Block {
                stmts: prelude,
                tail: Box::new(tail),
            },
            ty: acc_ty,
            span: call_span,
        })
    }

    fn check_generic_builtin(
        &mut self,
        name: &str,
        name_span: Span,
        targ_nodes: &[NodeIndex],
        arg_nodes: &[NodeIndex],
        call_span: Span,
        scope: &HashMap<String, ValueBinding>,
    ) -> Option<Expr> {
        match name {
            "some" => {
                if targ_nodes.len() != 1 || arg_nodes.len() != 1 {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        "`some<T>(value)` expects 1 type argument and 1 value argument",
                    ));
                    return None;
                }
                let ty = self.resolve_type(targ_nodes[0])?;
                let mut val = self.check_expr(arg_nodes[0], scope, Some(&ty))?;
                if !self.coerce_or_check(&mut val, &ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        val.span,
                        format!(
                            "`some` argument mismatch: expected `{}`, found `{}`",
                            self.format_type(&ty),
                            self.format_type(&val.ty)
                        ),
                    ));
                    return None;
                }
                Some(Expr {
                    kind: ExprKind::MaybeSome(Box::new(val)),
                    ty: Type::Maybe(Box::new(ty)),
                    span: call_span,
                })
            }
            "none" => {
                if targ_nodes.len() != 1 || !arg_nodes.is_empty() {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        "`none<T>()` expects 1 type argument and 0 value arguments",
                    ));
                    return None;
                }
                let ty = self.resolve_type(targ_nodes[0])?;
                Some(Expr {
                    kind: ExprKind::MaybeNone(ty.clone()),
                    ty: Type::Maybe(Box::new(ty)),
                    span: call_span,
                })
            }
            "left" => {
                if targ_nodes.len() != 2 || arg_nodes.len() != 1 {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        "`left<A, B>(value)` expects 2 type arguments and 1 value argument",
                    ));
                    return None;
                }
                let left_ty = self.resolve_type(targ_nodes[0])?;
                let right_ty = self.resolve_type(targ_nodes[1])?;
                let mut val = self.check_expr(arg_nodes[0], scope, Some(&left_ty))?;
                if !self.coerce_or_check(&mut val, &left_ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        val.span,
                        format!(
                            "`left` argument mismatch: expected `{}`, found `{}`",
                            self.format_type(&left_ty),
                            self.format_type(&val.ty)
                        ),
                    ));
                    return None;
                }
                Some(Expr {
                    kind: ExprKind::StructLit {
                        fields: vec![
                            (
                                "is_left".to_owned(),
                                Expr {
                                    kind: ExprKind::BoolLit(true),
                                    ty: Type::Boolean,
                                    span: call_span,
                                },
                            ),
                            ("left".to_owned(), val),
                            (
                                "right".to_owned(),
                                Expr {
                                    kind: ExprKind::Default(right_ty.clone()),
                                    ty: right_ty.clone(),
                                    span: call_span,
                                },
                            ),
                        ],
                    },
                    ty: Type::Either(Box::new(left_ty), Box::new(right_ty)),
                    span: call_span,
                })
            }
            "right" => {
                if targ_nodes.len() != 2 || arg_nodes.len() != 1 {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        "`right<A, B>(value)` expects 2 type arguments and 1 value argument",
                    ));
                    return None;
                }
                let left_ty = self.resolve_type(targ_nodes[0])?;
                let right_ty = self.resolve_type(targ_nodes[1])?;
                let mut val = self.check_expr(arg_nodes[0], scope, Some(&right_ty))?;
                if !self.coerce_or_check(&mut val, &right_ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        val.span,
                        format!(
                            "`right` argument mismatch: expected `{}`, found `{}`",
                            self.format_type(&right_ty),
                            self.format_type(&val.ty)
                        ),
                    ));
                    return None;
                }
                Some(Expr {
                    kind: ExprKind::StructLit {
                        fields: vec![
                            (
                                "is_left".to_owned(),
                                Expr {
                                    kind: ExprKind::BoolLit(false),
                                    ty: Type::Boolean,
                                    span: call_span,
                                },
                            ),
                            (
                                "left".to_owned(),
                                Expr {
                                    kind: ExprKind::Default(left_ty.clone()),
                                    ty: left_ty.clone(),
                                    span: call_span,
                                },
                            ),
                            ("right".to_owned(), val),
                        ],
                    },
                    ty: Type::Either(Box::new(left_ty), Box::new(right_ty)),
                    span: call_span,
                })
            }
            "persistentHash" => {
                if targ_nodes.len() != 1 || arg_nodes.len() != 1 {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        "`persistentHash<T>(value)` expects 1 type argument and 1 value argument",
                    ));
                    return None;
                }
                let input_ty = self.resolve_type(targ_nodes[0])?;
                let mut arg = self.check_expr(arg_nodes[0], scope, Some(&input_ty))?;
                if !self.coerce_or_check(&mut arg, &input_ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        arg.span,
                        format!(
                            "`persistentHash` argument mismatch: expected `{}`, found `{}`",
                            self.format_type(&input_ty),
                            self.format_type(&arg.ty)
                        ),
                    ));
                    return None;
                }
                Some(Expr {
                    kind: ExprKind::PersistentHash {
                        input_ty,
                        arg: Box::new(arg),
                    },
                    ty: Type::Bytes(32),
                    span: call_span,
                })
            }
            "keccak256" => {
                if targ_nodes.len() != 1 || arg_nodes.len() != 1 {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        "`keccak256<T>(value)` expects 1 type argument and 1 value argument",
                    ));
                    return None;
                }
                let input_ty = self.resolve_type(targ_nodes[0])?;
                let mut arg = self.check_expr(arg_nodes[0], scope, Some(&input_ty))?;
                if !self.coerce_or_check(&mut arg, &input_ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        arg.span,
                        format!(
                            "`keccak256` argument mismatch: expected `{}`, found `{}`",
                            self.format_type(&input_ty),
                            self.format_type(&arg.ty)
                        ),
                    ));
                    return None;
                }
                Some(Expr {
                    kind: ExprKind::Keccak256 {
                        input_ty,
                        arg: Box::new(arg),
                    },
                    ty: Type::Bytes(32),
                    span: call_span,
                })
            }
            "sha512" => {
                if targ_nodes.len() != 1 || arg_nodes.len() != 1 {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        "`sha512<T>(value)` expects 1 type argument and 1 value argument",
                    ));
                    return None;
                }
                let input_ty = self.resolve_type(targ_nodes[0])?;
                let mut arg = self.check_expr(arg_nodes[0], scope, Some(&input_ty))?;
                if !self.coerce_or_check(&mut arg, &input_ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        arg.span,
                        format!(
                            "`sha512` argument mismatch: expected `{}`, found `{}`",
                            self.format_type(&input_ty),
                            self.format_type(&arg.ty)
                        ),
                    ));
                    return None;
                }
                Some(Expr {
                    kind: ExprKind::Sha512 {
                        input_ty,
                        arg: Box::new(arg),
                    },
                    ty: Type::Bytes(64),
                    span: call_span,
                })
            }
            "hashToCurve" => {
                if targ_nodes.len() != 1 || arg_nodes.len() != 1 {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        "`hashToCurve<T>(value)` expects 1 type argument and 1 value argument",
                    ));
                    return None;
                }
                let input_ty = self.resolve_type(targ_nodes[0])?;
                let mut arg = self.check_expr(arg_nodes[0], scope, Some(&input_ty))?;
                if !self.coerce_or_check(&mut arg, &input_ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        arg.span,
                        format!(
                            "`hashToCurve` argument mismatch: expected `{}`, found `{}`",
                            self.format_type(&input_ty),
                            self.format_type(&arg.ty)
                        ),
                    ));
                    return None;
                }
                Some(Expr {
                    kind: ExprKind::HashToCurve {
                        input_ty,
                        arg: Box::new(arg),
                    },
                    ty: Type::CurvePoint(CurveKind::Jubjub),
                    span: call_span,
                })
            }
            "serialize" => {
                if targ_nodes.len() != 2 || arg_nodes.len() != 1 {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        "`serialize<N, T>(value)` expects 2 type arguments and 1 value argument",
                    ));
                    return None;
                }
                let len = self.expect_type_nat(targ_nodes, 0, "serialize", call_span)?;
                let input_ty = self.resolve_type(targ_nodes[1])?;
                let Some(actual_len) = self.serialized_byte_len(&input_ty) else {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        format!("type `{}` is not serializable", self.format_type(&input_ty)),
                    ));
                    return None;
                };
                if actual_len > len {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        format!(
                            "actual serialized size {actual_len} exceeds specified length {len} for `{}`",
                            self.format_type(&input_ty)
                        ),
                    ));
                    return None;
                }
                let mut val = self.check_expr(arg_nodes[0], scope, Some(&input_ty))?;
                if !self.coerce_or_check(&mut val, &input_ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        val.span,
                        format!(
                            "`serialize` argument mismatch: expected `{}`, found `{}`",
                            self.format_type(&input_ty),
                            self.format_type(&val.ty)
                        ),
                    ));
                    return None;
                }
                Some(Expr {
                    kind: ExprKind::Serialize {
                        len,
                        input_ty,
                        value: Box::new(val),
                    },
                    ty: Type::Bytes(len),
                    span: call_span,
                })
            }
            "deserialize" => {
                if targ_nodes.len() != 2 || arg_nodes.len() != 1 {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        "`deserialize<N, T>(bytes)` expects 2 type arguments and 1 value argument",
                    ));
                    return None;
                }
                let len = self.expect_type_nat(targ_nodes, 0, "deserialize", call_span)?;
                let target_ty = self.resolve_type(targ_nodes[1])?;
                let Some(actual_len) = self.serialized_byte_len(&target_ty) else {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        format!(
                            "type `{}` is not deserializable",
                            self.format_type(&target_ty)
                        ),
                    ));
                    return None;
                };
                if actual_len > len {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        format!(
                            "actual serialized size {actual_len} exceeds specified length {len} for `{}`",
                            self.format_type(&target_ty)
                        ),
                    ));
                    return None;
                }
                let expected_bytes = Type::Bytes(len);
                let mut bytes = self.check_expr(arg_nodes[0], scope, Some(&expected_bytes))?;
                if !self.coerce_or_check(&mut bytes, &expected_bytes) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        bytes.span,
                        format!(
                            "`deserialize` expects `Bytes<{len}>`, found `{}`",
                            self.format_type(&bytes.ty)
                        ),
                    ));
                    return None;
                }
                Some(Expr {
                    kind: ExprKind::Deserialize {
                        len,
                        target_ty: target_ty.clone(),
                        bytes: Box::new(bytes),
                    },
                    ty: target_ty,
                    span: call_span,
                })
            }
            "transientHash" => {
                if targ_nodes.len() != 1 || arg_nodes.len() != 1 {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        "`transientHash<T>(value)` expects 1 type argument and 1 value argument",
                    ));
                    return None;
                }
                let input_ty = self.resolve_type(targ_nodes[0])?;
                let mut arg = self.check_expr(arg_nodes[0], scope, Some(&input_ty))?;
                if !self.coerce_or_check(&mut arg, &input_ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        arg.span,
                        format!(
                            "`transientHash` argument mismatch: expected `{}`, found `{}`",
                            self.format_type(&input_ty),
                            self.format_type(&arg.ty)
                        ),
                    ));
                    return None;
                }
                Some(Expr {
                    kind: ExprKind::TransientHash {
                        input_ty,
                        arg: Box::new(arg),
                    },
                    ty: Type::Field,
                    span: call_span,
                })
            }
            "persistentCommit" => {
                if targ_nodes.len() != 1 || arg_nodes.len() != 2 {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        "`persistentCommit<T>(value, rand)` expects 1 type argument and 2 value arguments",
                    ));
                    return None;
                }
                let input_ty = self.resolve_type(targ_nodes[0])?;
                let mut value = self.check_expr(arg_nodes[0], scope, Some(&input_ty))?;
                if !self.coerce_or_check(&mut value, &input_ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        value.span,
                        format!(
                            "`persistentCommit` value mismatch: expected `{}`, found `{}`",
                            self.format_type(&input_ty),
                            self.format_type(&value.ty)
                        ),
                    ));
                    return None;
                }
                let rand_ty = Type::Bytes(32);
                let mut rand = self.check_expr(arg_nodes[1], scope, Some(&rand_ty))?;
                if !self.coerce_or_check(&mut rand, &rand_ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        rand.span,
                        format!(
                            "`persistentCommit` randomness must be `Bytes<32>`, found `{}`",
                            self.format_type(&rand.ty)
                        ),
                    ));
                    return None;
                }
                Some(Expr {
                    kind: ExprKind::PersistentCommit {
                        input_ty,
                        value: Box::new(value),
                        rand: Box::new(rand),
                    },
                    ty: Type::Bytes(32),
                    span: call_span,
                })
            }
            "transientCommit" => {
                if targ_nodes.len() != 1 || arg_nodes.len() != 2 {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        "`transientCommit<T>(value, rand)` expects 1 type argument and 2 value arguments",
                    ));
                    return None;
                }
                let input_ty = self.resolve_type(targ_nodes[0])?;
                let mut value = self.check_expr(arg_nodes[0], scope, Some(&input_ty))?;
                if !self.coerce_or_check(&mut value, &input_ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        value.span,
                        format!(
                            "`transientCommit` value mismatch: expected `{}`, found `{}`",
                            self.format_type(&input_ty),
                            self.format_type(&value.ty)
                        ),
                    ));
                    return None;
                }
                let rand_ty = Type::Field;
                let mut rand = self.check_expr(arg_nodes[1], scope, Some(&rand_ty))?;
                if !self.coerce_or_check(&mut rand, &rand_ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        rand.span,
                        format!(
                            "`transientCommit` randomness must be `Field`, found `{}`",
                            self.format_type(&rand.ty)
                        ),
                    ));
                    return None;
                }
                Some(Expr {
                    kind: ExprKind::TransientCommit {
                        input_ty,
                        value: Box::new(value),
                        rand: Box::new(rand),
                    },
                    ty: Type::Field,
                    span: call_span,
                })
            }
            "merkleTreePathRoot" => {
                if targ_nodes.len() != 2 || arg_nodes.len() != 1 {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        "`merkleTreePathRoot<N, T>(path)` expects 2 type arguments and 1 value argument",
                    ));
                    return None;
                }
                let depth = self.expect_type_nat(targ_nodes, 0, "merkleTreePathRoot", call_span)?;
                let leaf_ty = self.resolve_type(targ_nodes[1])?;
                let expected_path_ty = Type::MerkleTreePath(depth, Box::new(leaf_ty.clone()));
                let mut path = self.check_expr(arg_nodes[0], scope, Some(&expected_path_ty))?;
                if !self.coerce_or_check(&mut path, &expected_path_ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        path.span,
                        format!(
                            "`merkleTreePathRoot` argument mismatch: expected `{}`, found `{}`",
                            self.format_type(&expected_path_ty),
                            self.format_type(&path.ty)
                        ),
                    ));
                    return None;
                }
                Some(Expr {
                    kind: ExprKind::MerkleTreePathRoot {
                        depth,
                        leaf_ty,
                        path: Box::new(path),
                    },
                    ty: Type::MerkleTreeDigest,
                    span: call_span,
                })
            }
            "slice" => {
                if targ_nodes.len() != 1 || arg_nodes.len() != 2 {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        "`slice<N>(value, start)` expects 1 size argument and 2 value arguments",
                    ));
                    return None;
                }
                let len = self.expect_type_nat(targ_nodes, 0, "slice", call_span)?;
                let base = self.check_expr(arg_nodes[0], scope, None)?;
                let start_expr = self.check_expr(arg_nodes[1], scope, Some(&Type::Uint(64)))?;
                let Some(start_u128) = self.eval_const_u128_in_scope(&start_expr) else {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        start_expr.span,
                        "`slice` start index must be a compile-time integer constant",
                    ));
                    return None;
                };
                let start = start_u128 as u32;
                let base_u = self.underlying_type(&base.ty).clone();
                let res_ty = match base_u {
                    Type::Vector(vlen, elem) => {
                        if start.saturating_add(len) > vlen {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                call_span,
                                format!(
                                    "`slice<{len}>` at offset {start} exceeds `Vector<{vlen}, ...>` length"
                                ),
                            ));
                            return None;
                        }
                        Type::Vector(len, elem)
                    }
                    Type::Tuple(elems) => {
                        let is_homogeneous =
                            elems.is_empty() || elems.iter().all(|e| *e == elems[0]);
                        let is_literal_start =
                            self.units.ast().node_tag(arg_nodes[1]) == NodeTag::IntLitExpr;
                        if !is_homogeneous && !is_literal_start {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                base.span,
                                "`slice` on a heterogeneous tuple requires a literal start index",
                            ));
                            return None;
                        }
                        if (start as usize).saturating_add(len as usize) > elems.len() {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                call_span,
                                format!(
                                    "`slice<{len}>` at offset {start} exceeds tuple length {}",
                                    elems.len()
                                ),
                            ));
                            return None;
                        }
                        Type::Tuple(elems[start as usize..(start + len) as usize].to_vec())
                    }
                    Type::Bytes(blen) => {
                        if start.saturating_add(len) > blen {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                call_span,
                                format!(
                                    "`slice<{len}>` at offset {start} exceeds `Bytes<{blen}>` length"
                                ),
                            ));
                            return None;
                        }
                        Type::Bytes(len)
                    }
                    other => {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            base.span,
                            format!(
                                "`slice` expects `Vector`, tuple, or `Bytes`, found `{}`",
                                self.format_type(&other)
                            ),
                        ));
                        return None;
                    }
                };
                Some(Expr {
                    kind: ExprKind::Slice {
                        base: Box::new(base),
                        start,
                        len,
                    },
                    ty: res_ty,
                    span: call_span,
                })
            }
            other => {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    name_span,
                    format!("unknown generic circuit `{other}`"),
                ));
                None
            }
        }
    }

    fn check_witness_call(
        &mut self,
        wid: WitnessId,
        arg_nodes: &[NodeIndex],
        call_span: Span,
        scope: &HashMap<String, ValueBinding>,
    ) -> Option<Expr> {
        let wname = self.witnesses[wid.0 as usize].name.clone();
        let expected_params: Vec<Type> = self.witnesses[wid.0 as usize]
            .params
            .iter()
            .map(|p| p.ty.clone())
            .collect();
        let ret_type = self.witnesses[wid.0 as usize].ret_type.clone();

        if arg_nodes.len() != expected_params.len() {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                call_span,
                format!(
                    "witness `{wname}` expects {} argument(s), found {}",
                    expected_params.len(),
                    arg_nodes.len()
                ),
            ));
            return None;
        }

        let mut args = Vec::with_capacity(arg_nodes.len());
        for (&anode, expected_ty) in arg_nodes.iter().zip(&expected_params) {
            let mut arg = self.check_expr(anode, scope, Some(expected_ty))?;
            if !self.coerce_or_check(&mut arg, expected_ty) {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    arg.span,
                    format!(
                        "argument type mismatch calling witness `{wname}`: expected `{}`, found `{}`",
                        self.format_type(expected_ty),
                        self.format_type(&arg.ty)
                    ),
                ));
                return None;
            }
            args.push(arg);
        }

        Some(Expr {
            kind: ExprKind::WitnessCall { witness: wid, args },
            ty: ret_type,
            span: call_span,
        })
    }

    fn is_nat_type_arg(&self, node: NodeIndex) -> bool {
        match self.units.ast().node_tag(node) {
            NodeTag::TypeNat => true,
            NodeTag::TypeNamed => {
                let name = self.text(self.units.ast().node_main_token(node));
                self.scope.generics.nats.contains_key(name)
            }
            _ => false,
        }
    }

    fn resolve_generic_circuit_overload(
        &mut self,
        callee_name: &str,
        gids: &[usize],
        targ_nodes: &[NodeIndex],
        arg_nodes: &[NodeIndex],
        call_span: Span,
        scope: &HashMap<String, ValueBinding>,
    ) -> Option<Expr> {
        let matching_gids: Vec<usize> = gids
            .iter()
            .copied()
            .filter(|&gid| {
                let gparams = &self.generic_circuits[gid].gparams;
                if gparams.len() != targ_nodes.len() {
                    return false;
                }
                gparams
                    .iter()
                    .zip(targ_nodes.iter())
                    .all(|(gp, &arg)| gp.is_nat == self.is_nat_type_arg(arg))
            })
            .collect();
        if matching_gids.is_empty() {
            if gids.len() == 1 {
                let cid = self.instantiate_generic_circuit(gids[0], targ_nodes, call_span)?;
                return self.check_circuit_call(cid, arg_nodes, call_span, scope);
            }
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                call_span,
                format!("no overload of generic circuit `{callee_name}` matches the provided generic arguments"),
            ));
            return None;
        }
        if matching_gids.len() == 1 {
            let cid = self.instantiate_generic_circuit(matching_gids[0], targ_nodes, call_span)?;
            return self.check_circuit_call(cid, arg_nodes, call_span, scope);
        }
        let mut cids = Vec::with_capacity(matching_gids.len());
        for gid in matching_gids {
            if let Some(cid) = self.instantiate_generic_circuit(gid, targ_nodes, call_span) {
                cids.push(cid);
            }
        }
        if cids.is_empty() {
            return None;
        }
        self.resolve_circuit_overload(callee_name, &cids, arg_nodes, call_span, scope)
    }

    fn resolve_circuit_overload(
        &mut self,
        callee_name: &str,
        candidates: &[CircuitId],
        arg_nodes: &[NodeIndex],
        call_span: Span,
        scope: &HashMap<String, ValueBinding>,
    ) -> Option<Expr> {
        if candidates.len() == 1 {
            return self.check_circuit_call(candidates[0], arg_nodes, call_span, scope);
        }
        let arity_matches: Vec<CircuitId> = candidates
            .iter()
            .copied()
            .filter(|&cid| self.circuit_sigs[cid.0 as usize].params.len() == arg_nodes.len())
            .collect();
        if arity_matches.is_empty() {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                call_span,
                format!(
                    "no overload of circuit `{callee_name}` takes {} argument(s)",
                    arg_nodes.len()
                ),
            ));
            return None;
        }
        // Deduplicate identical circuit instances (e.g. from importing the same module twice).
        let mut unique_arity: Vec<CircuitId> = Vec::with_capacity(arity_matches.len());
        for cid in arity_matches {
            let s = &self.circuit_sigs[cid.0 as usize];
            let dup = unique_arity.iter().any(|&prev| {
                let p = &self.circuit_sigs[prev.0 as usize];
                p.unit == s.unit
                    && p.body_node == s.body_node
                    && p.ret_type == s.ret_type
                    && p.scope.generics.types == s.scope.generics.types
                    && p.scope.generics.nats == s.scope.generics.nats
                    && p.params.len() == s.params.len()
                    && p.params.iter().zip(&s.params).all(|(a, b)| a.ty == b.ty)
            });
            if !dup {
                unique_arity.push(cid);
            }
        }
        let arity_matches = unique_arity;
        if arity_matches.len() == 1 {
            return self.check_circuit_call(arity_matches[0], arg_nodes, call_span, scope);
        }

        // Evaluate arguments once without forcing a single overload's expected type.
        let mut checked_args = Vec::with_capacity(arg_nodes.len());
        for &anode in arg_nodes {
            checked_args.push(self.check_expr(anode, scope, None)?);
        }

        let mut exact_matches = Vec::new();
        let mut widening_matches = Vec::new();
        for &cid in &arity_matches {
            let expected_params: Vec<Type> = self.circuit_sigs[cid.0 as usize]
                .params
                .iter()
                .map(|p| p.ty.clone())
                .collect();
            let is_exact = checked_args
                .iter()
                .zip(&expected_params)
                .all(|(a, exp)| a.ty == *exp);
            if is_exact {
                exact_matches.push(cid);
                continue;
            }
            let mut trial = checked_args.clone();
            let is_widening = trial
                .iter_mut()
                .zip(&expected_params)
                .all(|(a, exp)| self.coerce_or_check(a, exp));
            if is_widening {
                widening_matches.push((cid, trial));
            }
        }

        if exact_matches.len() == 1 {
            let cid = exact_matches[0];
            let ret_type = self.circuit_sigs[cid.0 as usize].ret_type.clone();
            return Some(Expr {
                kind: ExprKind::CircuitCall {
                    circuit: cid,
                    args: checked_args,
                },
                ty: ret_type,
                span: call_span,
            });
        }
        if exact_matches.len() > 1 {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                call_span,
                format!("ambiguous call to overloaded circuit `{callee_name}`"),
            ));
            return None;
        }
        if widening_matches.len() == 1 {
            let (cid, coerced_args) = widening_matches.into_iter().next().unwrap();
            let ret_type = self.circuit_sigs[cid.0 as usize].ret_type.clone();
            return Some(Expr {
                kind: ExprKind::CircuitCall {
                    circuit: cid,
                    args: coerced_args,
                },
                ty: ret_type,
                span: call_span,
            });
        }
        if widening_matches.len() > 1 {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                call_span,
                format!("ambiguous call to overloaded circuit `{callee_name}` (multiple widening matches)"),
            ));
            return None;
        }
        self.diagnostics.push(CompactDiagnostic::error(
            self.units.file(),
            call_span,
            format!("no overload of circuit `{callee_name}` matches the argument types"),
        ));
        None
    }

    fn check_circuit_call(
        &mut self,
        cid: CircuitId,
        arg_nodes: &[NodeIndex],
        call_span: Span,
        scope: &HashMap<String, ValueBinding>,
    ) -> Option<Expr> {
        let cname = self.circuit_sigs[cid.0 as usize].name.clone();
        let expected_params: Vec<Type> = self.circuit_sigs[cid.0 as usize]
            .params
            .iter()
            .map(|p| p.ty.clone())
            .collect();
        let ret_type = self.circuit_sigs[cid.0 as usize].ret_type.clone();

        if arg_nodes.len() != expected_params.len() {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                call_span,
                format!(
                    "circuit `{cname}` expects {} argument(s), found {}",
                    expected_params.len(),
                    arg_nodes.len()
                ),
            ));
            return None;
        }

        let mut args = Vec::with_capacity(arg_nodes.len());
        for (&anode, expected_ty) in arg_nodes.iter().zip(&expected_params) {
            let mut arg = self.check_expr(anode, scope, Some(expected_ty))?;
            if !self.coerce_or_check(&mut arg, expected_ty) {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    arg.span,
                    format!(
                        "argument type mismatch calling `{cname}`: expected `{}`, found `{}`",
                        self.format_type(expected_ty),
                        self.format_type(&arg.ty)
                    ),
                ));
                return None;
            }
            args.push(arg);
        }

        Some(Expr {
            kind: ExprKind::CircuitCall { circuit: cid, args },
            ty: ret_type,
            span: call_span,
        })
    }

    fn try_extract_ledger_chain(
        &mut self,
        node: NodeIndex,
        scope: &HashMap<String, ValueBinding>,
    ) -> Option<(LedgerFieldId, Vec<Expr>, LedgerAdt)> {
        match self.units.ast().node_tag(node) {
            NodeTag::IdentExpr => {
                let name = self.text(self.units.ast().node_main_token(node)).to_owned();
                if let Some(&field_id) = self.scope.ledger_fields.get(&name) {
                    return Some((
                        field_id,
                        Vec::new(),
                        self.ledger_fields[field_id.0 as usize].adt.clone(),
                    ));
                }
                if name == "kernel" && self.scope.has_stdlib {
                    let field_id = self.ensure_kernel_field();
                    return Some((field_id, Vec::new(), LedgerAdt::Kernel));
                }
                None
            }
            NodeTag::CallExpr => {
                let call = self.units.ast().call_expr(node);
                if self.units.ast().node_tag(call.callee) != NodeTag::MemberExpr {
                    return None;
                }
                let mdata = self.units.ast().node_data(call.callee);
                let inner_recv = NodeIndex(mdata.lhs);
                let method_name = self.text(TokenIndex(mdata.rhs));
                if method_name != "lookup" {
                    return None;
                }
                let (field_id, mut key_path, outer_adt) =
                    self.try_extract_ledger_chain(inner_recv, scope)?;
                let LedgerAdt::Map { key, value } = outer_adt else {
                    return None;
                };
                if value.is_cell() {
                    return None;
                }
                let arg_nodes: Vec<_> = self
                    .units
                    .ast()
                    .extra_nodes(call.args_start, call.args_end)
                    .collect();
                if arg_nodes.len() != 1 {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        self.units.ast().node_span(node),
                        "`Map.lookup` takes 1 argument",
                    ));
                    return None;
                }
                let mut key_expr = self.check_expr(arg_nodes[0], scope, Some(&key))?;
                if !self.coerce_or_check(&mut key_expr, &key) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        key_expr.span,
                        format!(
                            "`Map.lookup` key mismatch: expected `{}`, found `{}`",
                            self.format_type(&key),
                            self.format_type(&key_expr.ty)
                        ),
                    ));
                    return None;
                }
                key_path.push(key_expr);
                Some((field_id, key_path, *value))
            }
            _ => None,
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn check_ledger_call(
        &mut self,
        field_id: LedgerFieldId,
        key_path: Vec<Expr>,
        target_adt: LedgerAdt,
        method_name: &str,
        method_span: Span,
        arg_nodes: &[NodeIndex],
        call_span: Span,
        scope: &HashMap<String, ValueBinding>,
    ) -> Option<Expr> {
        let method_name = self.resolve_ledger_op_name(method_name, method_span)?;
        let make_call = |op: LedgerOp, args: Vec<Expr>, ty: Type, target_adt: LedgerAdt| {
            Some(Expr {
                kind: ExprKind::LedgerCall {
                    field: field_id,
                    key_path,
                    target_adt,
                    op,
                    args,
                },
                ty,
                span: call_span,
            })
        };

        match target_adt.clone() {
            LedgerAdt::Counter => {
                let (op, expected_args, ret_ty) = match method_name {
                    "increment" => (LedgerOp::CounterIncrement, 1usize, Type::unit()),
                    "decrement" => (LedgerOp::CounterDecrement, 1usize, Type::unit()),
                    "read" => (LedgerOp::CounterRead, 0usize, Type::Uint(64)),
                    "lessThan" => (LedgerOp::CounterLessThan, 1usize, Type::Boolean),
                    "resetToDefault" => (LedgerOp::CounterResetToDefault, 0usize, Type::unit()),
                    other => {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            method_span,
                            format!("`Counter` has no method `{other}`"),
                        ));
                        return None;
                    }
                };
                if arg_nodes.len() != expected_args {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        format!(
                            "`Counter.{method_name}` expects {expected_args} argument(s), found {}",
                            arg_nodes.len()
                        ),
                    ));
                    return None;
                }
                let expected_arg_ty = if op == LedgerOp::CounterLessThan {
                    Type::Uint(64)
                } else {
                    Type::Uint(16)
                };
                let mut args = Vec::with_capacity(arg_nodes.len());
                for &anode in arg_nodes {
                    let mut arg = self.check_expr(anode, scope, Some(&expected_arg_ty))?;
                    if matches!(op, LedgerOp::CounterIncrement | LedgerOp::CounterDecrement)
                        && let Some(v) = eval_const_u128(&arg)
                    {
                        if v > u16::MAX as u128 {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                arg.span,
                                format!(
                                    "`Counter.{method_name}` expects a `Uint<16>` argument (0..=65535), found {v}"
                                ),
                            ));
                            return None;
                        }
                        arg.ty = Type::Uint(16);
                    }
                    args.push(arg);
                }
                make_call(op, args, ret_ty, target_adt)
            }
            LedgerAdt::Kernel => {
                let token_type =
                    || Type::Either(Box::new(Type::Bytes(32)), Box::new(Type::Bytes(32)));
                let (op, expected_tys, ret_ty): (LedgerOp, Vec<Type>, Type) = match method_name {
                    "self" => (
                        LedgerOp::KernelSelf,
                        vec![],
                        self.resolve_stdlib_struct("ContractAddress", call_span)?,
                    ),
                    "caller" => {
                        let ca = self.resolve_stdlib_struct("ContractAddress", call_span)?;
                        let ua = self.resolve_stdlib_struct("UserAddress", call_span)?;
                        let pub_addr = Type::Either(Box::new(ca), Box::new(ua));
                        (
                            LedgerOp::KernelCaller,
                            vec![],
                            Type::Maybe(Box::new(pub_addr)),
                        )
                    }
                    "checkpoint" => (LedgerOp::KernelCheckpoint, vec![], Type::unit()),
                    "claimZswapNullifier" => (
                        LedgerOp::KernelClaimZswapNullifier,
                        vec![Type::Bytes(32)],
                        Type::unit(),
                    ),
                    "claimZswapCoinSpend" => (
                        LedgerOp::KernelClaimZswapCoinSpend,
                        vec![Type::Bytes(32)],
                        Type::unit(),
                    ),
                    "claimZswapCoinReceive" => (
                        LedgerOp::KernelClaimZswapCoinReceive,
                        vec![Type::Bytes(32)],
                        Type::unit(),
                    ),
                    "claimContractCall" => (
                        LedgerOp::KernelClaimContractCall,
                        vec![Type::Bytes(32), Type::Bytes(32), Type::Field],
                        Type::unit(),
                    ),
                    "mintShielded" => (
                        LedgerOp::KernelMintShielded,
                        vec![Type::Bytes(32), Type::Uint(64)],
                        Type::unit(),
                    ),
                    "mintUnshielded" => (
                        LedgerOp::KernelMintUnshielded,
                        vec![Type::Bytes(32), Type::Uint(64)],
                        Type::unit(),
                    ),
                    "claimUnshieldedCoinSpend" => {
                        let ca = self.resolve_stdlib_struct("ContractAddress", call_span)?;
                        let ua = self.resolve_stdlib_struct("UserAddress", call_span)?;
                        let pub_addr = Type::Either(Box::new(ca), Box::new(ua));
                        (
                            LedgerOp::KernelClaimUnshieldedCoinSpend,
                            vec![token_type(), pub_addr, Type::Uint(128)],
                            Type::unit(),
                        )
                    }
                    "incUnshieldedOutputs" => (
                        LedgerOp::KernelIncUnshieldedOutputs,
                        vec![token_type(), Type::Uint(128)],
                        Type::unit(),
                    ),
                    "incUnshieldedInputs" => (
                        LedgerOp::KernelIncUnshieldedInputs,
                        vec![token_type(), Type::Uint(128)],
                        Type::unit(),
                    ),
                    "balance" => (LedgerOp::KernelBalance, vec![token_type()], Type::Uint(128)),
                    "balanceLessThan" => (
                        LedgerOp::KernelBalanceLessThan,
                        vec![token_type(), Type::Uint(128)],
                        Type::Boolean,
                    ),
                    "balanceGreaterThan" => (
                        LedgerOp::KernelBalanceGreaterThan,
                        vec![token_type(), Type::Uint(128)],
                        Type::Boolean,
                    ),
                    "blockTimeLessThan" => (
                        LedgerOp::KernelBlockTimeLessThan,
                        vec![Type::Uint(64)],
                        Type::Boolean,
                    ),
                    "blockTimeGreaterThan" => (
                        LedgerOp::KernelBlockTimeGreaterThan,
                        vec![Type::Uint(64)],
                        Type::Boolean,
                    ),
                    other => {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            method_span,
                            format!("`Kernel` has no method `{other}`"),
                        ));
                        return None;
                    }
                };
                if arg_nodes.len() != expected_tys.len() {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        call_span,
                        format!(
                            "`Kernel.{method_name}` expects {} argument(s), found {}",
                            expected_tys.len(),
                            arg_nodes.len()
                        ),
                    ));
                    return None;
                }
                let mut args = Vec::with_capacity(arg_nodes.len());
                for (&anode, expected_ty) in arg_nodes.iter().zip(&expected_tys) {
                    let mut arg = self.check_expr(anode, scope, Some(expected_ty))?;
                    if !self.coerce_or_check(&mut arg, expected_ty) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            arg.span,
                            format!(
                                "`Kernel.{method_name}` argument mismatch: expected `{}`, found `{}`",
                                self.format_type(expected_ty),
                                self.format_type(&arg.ty)
                            ),
                        ));
                        return None;
                    }
                    args.push(arg);
                }
                make_call(op, args, ret_ty, target_adt)
            }
            LedgerAdt::Cell(value_type) => match method_name {
                "read" => {
                    if !arg_nodes.is_empty() {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            call_span,
                            "`Cell.read` takes 0 arguments",
                        ));
                        return None;
                    }
                    make_call(LedgerOp::CellRead, Vec::new(), *value_type, target_adt)
                }
                "write" => {
                    if arg_nodes.len() != 1 {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            call_span,
                            "`Cell.write` takes 1 argument",
                        ));
                        return None;
                    }
                    let mut val = self.check_expr(arg_nodes[0], scope, Some(&value_type))?;
                    if !self.coerce_or_check(&mut val, &value_type) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            val.span,
                            format!(
                                "`Cell.write` expects `{}`, found `{}`",
                                self.format_type(&value_type),
                                self.format_type(&val.ty)
                            ),
                        ));
                        return None;
                    }
                    make_call(LedgerOp::CellWrite, vec![val], Type::unit(), target_adt)
                }
                "writeCoin" => {
                    if arg_nodes.len() != 2 {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            call_span,
                            "`Cell.writeCoin` takes 2 arguments (coin, recipient)",
                        ));
                        return None;
                    }
                    let coin_ty = self.resolve_stdlib_struct("ShieldedCoinInfo", call_span)?;
                    let pk_ty = self.resolve_stdlib_struct("ZswapCoinPublicKey", call_span)?;
                    let ca_ty = self.resolve_stdlib_struct("ContractAddress", call_span)?;
                    let recip_ty = Type::Either(Box::new(pk_ty), Box::new(ca_ty));
                    let mut coin = self.check_expr(arg_nodes[0], scope, Some(&coin_ty))?;
                    if !self.coerce_or_check(&mut coin, &coin_ty) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            coin.span,
                            format!(
                                "`Cell.writeCoin` expects `ShieldedCoinInfo`, found `{}`",
                                self.format_type(&coin.ty)
                            ),
                        ));
                        return None;
                    }
                    let mut recip = self.check_expr(arg_nodes[1], scope, Some(&recip_ty))?;
                    if !self.coerce_or_check(&mut recip, &recip_ty) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            recip.span,
                            format!(
                                "`Cell.writeCoin` expects recipient `Either<ZswapCoinPublicKey, ContractAddress>`, found `{}`",
                                self.format_type(&recip.ty)
                            ),
                        ));
                        return None;
                    }
                    make_call(
                        LedgerOp::CellWriteCoin,
                        vec![coin, recip],
                        Type::unit(),
                        target_adt,
                    )
                }
                "resetToDefault" => {
                    if !arg_nodes.is_empty() {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            call_span,
                            "`Cell.resetToDefault` takes 0 arguments",
                        ));
                        return None;
                    }
                    make_call(
                        LedgerOp::CellResetToDefault,
                        Vec::new(),
                        Type::unit(),
                        target_adt,
                    )
                }
                other => {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        method_span,
                        format!("`Cell` has no method `{other}`"),
                    ));
                    None
                }
            },
            LedgerAdt::Set(value_type) => match method_name {
                "isEmpty" | "size" | "resetToDefault" => {
                    let (op, ret_ty) = match method_name {
                        "isEmpty" => (LedgerOp::SetIsEmpty, Type::Boolean),
                        "size" => (LedgerOp::SetSize, Type::Uint(64)),
                        _ => (LedgerOp::SetResetToDefault, Type::unit()),
                    };
                    if !arg_nodes.is_empty() {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            call_span,
                            format!("`Set.{method_name}` takes 0 arguments"),
                        ));
                        return None;
                    }
                    make_call(op, Vec::new(), ret_ty, target_adt)
                }
                "member" | "insert" | "remove" => {
                    let (op, ret_ty) = match method_name {
                        "member" => (LedgerOp::SetMember, Type::Boolean),
                        "insert" => (LedgerOp::SetInsert, Type::unit()),
                        _ => (LedgerOp::SetRemove, Type::unit()),
                    };
                    if arg_nodes.len() != 1 {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            call_span,
                            format!("`Set.{method_name}` takes 1 argument"),
                        ));
                        return None;
                    }
                    let mut elem = self.check_expr(arg_nodes[0], scope, Some(&value_type))?;
                    if !self.coerce_or_check(&mut elem, &value_type) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            elem.span,
                            format!(
                                "`Set.{method_name}` expects `{}`, found `{}`",
                                self.format_type(&value_type),
                                self.format_type(&elem.ty)
                            ),
                        ));
                        return None;
                    }
                    make_call(op, vec![elem], ret_ty, target_adt)
                }
                "insertCoin" => {
                    if arg_nodes.len() != 2 {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            call_span,
                            "`Set.insertCoin` takes 2 arguments (coin, recipient)",
                        ));
                        return None;
                    }
                    let coin_ty = self.resolve_stdlib_struct("ShieldedCoinInfo", call_span)?;
                    let pk_ty = self.resolve_stdlib_struct("ZswapCoinPublicKey", call_span)?;
                    let ca_ty = self.resolve_stdlib_struct("ContractAddress", call_span)?;
                    let recip_ty = Type::Either(Box::new(pk_ty), Box::new(ca_ty));
                    let mut coin = self.check_expr(arg_nodes[0], scope, Some(&coin_ty))?;
                    if !self.coerce_or_check(&mut coin, &coin_ty) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            coin.span,
                            format!(
                                "`Set.insertCoin` expects `ShieldedCoinInfo`, found `{}`",
                                self.format_type(&coin.ty)
                            ),
                        ));
                        return None;
                    }
                    let mut recip = self.check_expr(arg_nodes[1], scope, Some(&recip_ty))?;
                    if !self.coerce_or_check(&mut recip, &recip_ty) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            recip.span,
                            format!(
                                "`Set.insertCoin` expects recipient `Either<ZswapCoinPublicKey, ContractAddress>`, found `{}`",
                                self.format_type(&recip.ty)
                            ),
                        ));
                        return None;
                    }
                    make_call(
                        LedgerOp::SetInsertCoin,
                        vec![coin, recip],
                        Type::unit(),
                        target_adt,
                    )
                }
                other => {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        method_span,
                        format!("`Set` has no method `{other}`"),
                    ));
                    None
                }
            },
            LedgerAdt::List(value_type) => match method_name {
                "isEmpty" | "length" | "head" | "popFront" | "resetToDefault" => {
                    let (op, ret_ty) = match method_name {
                        "isEmpty" => (LedgerOp::ListIsEmpty, Type::Boolean),
                        "length" => (LedgerOp::ListLength, Type::Uint(64)),
                        "head" => (LedgerOp::ListHead, Type::Maybe(value_type)),
                        "popFront" => (LedgerOp::ListPopFront, Type::unit()),
                        _ => (LedgerOp::ListResetToDefault, Type::unit()),
                    };
                    if !arg_nodes.is_empty() {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            call_span,
                            format!("`List.{method_name}` takes 0 arguments"),
                        ));
                        return None;
                    }
                    make_call(op, Vec::new(), ret_ty, target_adt)
                }
                "pushFront" => {
                    if arg_nodes.len() != 1 {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            call_span,
                            "`List.pushFront` takes 1 argument",
                        ));
                        return None;
                    }
                    let mut elem = self.check_expr(arg_nodes[0], scope, Some(&value_type))?;
                    if !self.coerce_or_check(&mut elem, &value_type) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            elem.span,
                            format!(
                                "`List.pushFront` expects `{}`, found `{}`",
                                self.format_type(&value_type),
                                self.format_type(&elem.ty)
                            ),
                        ));
                        return None;
                    }
                    make_call(
                        LedgerOp::ListPushFront,
                        vec![elem],
                        Type::unit(),
                        target_adt,
                    )
                }
                "pushFrontCoin" => {
                    if arg_nodes.len() != 2 {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            call_span,
                            "`List.pushFrontCoin` takes 2 arguments (coin, recipient)",
                        ));
                        return None;
                    }
                    let coin_ty = self.resolve_stdlib_struct("ShieldedCoinInfo", call_span)?;
                    let pk_ty = self.resolve_stdlib_struct("ZswapCoinPublicKey", call_span)?;
                    let ca_ty = self.resolve_stdlib_struct("ContractAddress", call_span)?;
                    let recip_ty = Type::Either(Box::new(pk_ty), Box::new(ca_ty));
                    let mut coin = self.check_expr(arg_nodes[0], scope, Some(&coin_ty))?;
                    if !self.coerce_or_check(&mut coin, &coin_ty) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            coin.span,
                            format!(
                                "`List.pushFrontCoin` expects `ShieldedCoinInfo`, found `{}`",
                                self.format_type(&coin.ty)
                            ),
                        ));
                        return None;
                    }
                    let mut recip = self.check_expr(arg_nodes[1], scope, Some(&recip_ty))?;
                    if !self.coerce_or_check(&mut recip, &recip_ty) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            recip.span,
                            format!(
                                "`List.pushFrontCoin` expects recipient `Either<ZswapCoinPublicKey, ContractAddress>`, found `{}`",
                                self.format_type(&recip.ty)
                            ),
                        ));
                        return None;
                    }
                    make_call(
                        LedgerOp::ListPushFrontCoin,
                        vec![coin, recip],
                        Type::unit(),
                        target_adt,
                    )
                }
                other => {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        method_span,
                        format!("`List` has no method `{other}`"),
                    ));
                    None
                }
            },
            LedgerAdt::Map { key, value } => match method_name {
                "isEmpty" | "size" | "resetToDefault" => {
                    let (op, ret_ty) = match method_name {
                        "isEmpty" => (LedgerOp::MapIsEmpty, Type::Boolean),
                        "size" => (LedgerOp::MapSize, Type::Uint(64)),
                        _ => (LedgerOp::MapResetToDefault, Type::unit()),
                    };
                    if !arg_nodes.is_empty() {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            call_span,
                            format!("`Map.{method_name}` takes 0 arguments"),
                        ));
                        return None;
                    }
                    make_call(op, Vec::new(), ret_ty, target_adt)
                }
                "member" | "remove" | "insertDefault" => {
                    let (op, ret_ty) = match method_name {
                        "member" => (LedgerOp::MapMember, Type::Boolean),
                        "remove" => (LedgerOp::MapRemove, Type::unit()),
                        _ => (LedgerOp::MapInsertDefault, Type::unit()),
                    };
                    if arg_nodes.len() != 1 {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            call_span,
                            format!("`Map.{method_name}` takes 1 argument"),
                        ));
                        return None;
                    }
                    let mut k = self.check_expr(arg_nodes[0], scope, Some(&key))?;
                    if !self.coerce_or_check(&mut k, &key) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            k.span,
                            format!(
                                "`Map.{method_name}` expects key `{}`, found `{}`",
                                self.format_type(&key),
                                self.format_type(&k.ty)
                            ),
                        ));
                        return None;
                    }
                    make_call(op, vec![k], ret_ty, target_adt)
                }
                "lookup" => {
                    if arg_nodes.len() != 1 {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            call_span,
                            "`Map.lookup` takes 1 argument",
                        ));
                        return None;
                    }
                    let Some(val_ty) = value.cell_type().cloned() else {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            call_span,
                            format!(
                                "`Map.lookup` returns nested ADT `{}`; call a method on it directly",
                                value.name()
                            ),
                        ));
                        return None;
                    };
                    let mut k = self.check_expr(arg_nodes[0], scope, Some(&key))?;
                    if !self.coerce_or_check(&mut k, &key) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            k.span,
                            format!(
                                "`Map.lookup` expects key `{}`, found `{}`",
                                self.format_type(&key),
                                self.format_type(&k.ty)
                            ),
                        ));
                        return None;
                    }
                    make_call(LedgerOp::MapLookup, vec![k], val_ty, target_adt)
                }
                "insert" => {
                    if arg_nodes.len() != 2 {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            call_span,
                            "`Map.insert` takes 2 arguments (key, value)",
                        ));
                        return None;
                    }
                    let mut k = self.check_expr(arg_nodes[0], scope, Some(&key))?;
                    if !self.coerce_or_check(&mut k, &key) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            k.span,
                            format!(
                                "`Map.insert` expects key `{}`, found `{}`",
                                self.format_type(&key),
                                self.format_type(&k.ty)
                            ),
                        ));
                        return None;
                    }
                    let v = if let Some(val_ty) = value.cell_type() {
                        let mut val = self.check_expr(arg_nodes[1], scope, Some(val_ty))?;
                        if !self.coerce_or_check(&mut val, val_ty) {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                val.span,
                                format!(
                                    "`Map.insert` expects value `{}`, found `{}`",
                                    self.format_type(val_ty),
                                    self.format_type(&val.ty)
                                ),
                            ));
                            return None;
                        }
                        val
                    } else {
                        let mut default_node = arg_nodes[1];
                        while self.units.ast().node_tag(default_node) == NodeTag::DiscloseExpr {
                            default_node = NodeIndex(self.units.ast().node_data(default_node).lhs);
                        }
                        if self.units.ast().node_tag(default_node) == NodeTag::DefaultExpr {
                            let inner_ty = NodeIndex(self.units.ast().node_data(default_node).lhs);
                            let default_adt = self.resolve_ledger_adt(inner_ty)?;
                            if default_adt != *value {
                                self.diagnostics.push(CompactDiagnostic::error(
                                    self.units.file(),
                                    self.units.ast().node_span(arg_nodes[1]),
                                    format!(
                                        "`Map.insert` expects default value for `{}`, found `{}`",
                                        value.name(),
                                        default_adt.name()
                                    ),
                                ));
                                return None;
                            }
                            Expr {
                                kind: ExprKind::DefaultAdt(default_adt),
                                ty: Type::unit(),
                                span: self.units.ast().node_span(arg_nodes[1]),
                            }
                        } else {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                self.units.ast().node_span(arg_nodes[1]),
                                format!(
                                    "`Map.insert` for nested ADT `{}` requires `default<...>`",
                                    value.name()
                                ),
                            ));
                            return None;
                        }
                    };
                    make_call(LedgerOp::MapInsert, vec![k, v], Type::unit(), target_adt)
                }
                "insertCoin" => {
                    if arg_nodes.len() != 3 {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            call_span,
                            "`Map.insertCoin` takes 3 arguments (key, coin, recipient)",
                        ));
                        return None;
                    }
                    let mut k = self.check_expr(arg_nodes[0], scope, Some(&key))?;
                    if !self.coerce_or_check(&mut k, &key) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            k.span,
                            format!(
                                "`Map.insertCoin` expects key `{}`, found `{}`",
                                self.format_type(&key),
                                self.format_type(&k.ty)
                            ),
                        ));
                        return None;
                    }
                    let coin_ty = self.resolve_stdlib_struct("ShieldedCoinInfo", call_span)?;
                    let pk_ty = self.resolve_stdlib_struct("ZswapCoinPublicKey", call_span)?;
                    let ca_ty = self.resolve_stdlib_struct("ContractAddress", call_span)?;
                    let recip_ty = Type::Either(Box::new(pk_ty), Box::new(ca_ty));
                    let mut coin = self.check_expr(arg_nodes[1], scope, Some(&coin_ty))?;
                    if !self.coerce_or_check(&mut coin, &coin_ty) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            coin.span,
                            format!(
                                "`Map.insertCoin` expects `ShieldedCoinInfo`, found `{}`",
                                self.format_type(&coin.ty)
                            ),
                        ));
                        return None;
                    }
                    let mut recip = self.check_expr(arg_nodes[2], scope, Some(&recip_ty))?;
                    if !self.coerce_or_check(&mut recip, &recip_ty) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            recip.span,
                            format!(
                                "`Map.insertCoin` expects recipient `Either<ZswapCoinPublicKey, ContractAddress>`, found `{}`",
                                self.format_type(&recip.ty)
                            ),
                        ));
                        return None;
                    }
                    make_call(
                        LedgerOp::MapInsertCoin,
                        vec![k, coin, recip],
                        Type::unit(),
                        target_adt,
                    )
                }
                other => {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        method_span,
                        format!("`Map` has no method `{other}`"),
                    ));
                    None
                }
            },
            LedgerAdt::MerkleTree { value, .. } | LedgerAdt::HistoricMerkleTree { value, .. } => {
                let historic = matches!(target_adt, LedgerAdt::HistoricMerkleTree { .. });
                let adt_name = target_adt.name();
                match method_name {
                    "insert" => {
                        if arg_nodes.len() != 1 {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                call_span,
                                format!("`{adt_name}.insert` takes 1 argument"),
                            ));
                            return None;
                        }
                        let mut item = self.check_expr(arg_nodes[0], scope, Some(&value))?;
                        if !self.coerce_or_check(&mut item, &value) {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                item.span,
                                format!(
                                    "`{adt_name}.insert` expects `{}`, found `{}`",
                                    self.format_type(&value),
                                    self.format_type(&item.ty)
                                ),
                            ));
                            return None;
                        }
                        make_call(
                            if historic {
                                LedgerOp::HistoricMerkleTreeInsert
                            } else {
                                LedgerOp::MerkleTreeInsert
                            },
                            vec![item],
                            Type::unit(),
                            target_adt,
                        )
                    }
                    "isFull" => {
                        if !arg_nodes.is_empty() {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                call_span,
                                format!("`{adt_name}.isFull` takes 0 arguments"),
                            ));
                            return None;
                        }
                        make_call(
                            if historic {
                                LedgerOp::HistoricMerkleTreeIsFull
                            } else {
                                LedgerOp::MerkleTreeIsFull
                            },
                            Vec::new(),
                            Type::Boolean,
                            target_adt,
                        )
                    }
                    "checkRoot" => {
                        if arg_nodes.len() != 1 {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                call_span,
                                format!("`{adt_name}.checkRoot` takes 1 argument"),
                            ));
                            return None;
                        }
                        let mut rt =
                            self.check_expr(arg_nodes[0], scope, Some(&Type::MerkleTreeDigest))?;
                        if !self.coerce_or_check(&mut rt, &Type::MerkleTreeDigest) {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                rt.span,
                                format!(
                                    "`{adt_name}.checkRoot` expects `MerkleTreeDigest`, found `{}`",
                                    self.format_type(&rt.ty)
                                ),
                            ));
                            return None;
                        }
                        make_call(
                            if historic {
                                LedgerOp::HistoricMerkleTreeCheckRoot
                            } else {
                                LedgerOp::MerkleTreeCheckRoot
                            },
                            vec![rt],
                            Type::Boolean,
                            target_adt,
                        )
                    }
                    "insertHash" => {
                        if arg_nodes.len() != 1 {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                call_span,
                                format!("`{adt_name}.insertHash` takes 1 argument"),
                            ));
                            return None;
                        }
                        let mut h = self.check_expr(arg_nodes[0], scope, Some(&Type::Bytes(32)))?;
                        if !self.coerce_or_check(&mut h, &Type::Bytes(32)) {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                h.span,
                                format!(
                                    "`{adt_name}.insertHash` expects `Bytes<32>`, found `{}`",
                                    self.format_type(&h.ty)
                                ),
                            ));
                            return None;
                        }
                        make_call(
                            if historic {
                                LedgerOp::HistoricMerkleTreeInsertHash
                            } else {
                                LedgerOp::MerkleTreeInsertHash
                            },
                            vec![h],
                            Type::unit(),
                            target_adt,
                        )
                    }
                    "insertHashIndex" => {
                        if arg_nodes.len() != 2 {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                call_span,
                                format!("`{adt_name}.insertHashIndex` takes 2 arguments"),
                            ));
                            return None;
                        }
                        let mut h = self.check_expr(arg_nodes[0], scope, Some(&Type::Bytes(32)))?;
                        if !self.coerce_or_check(&mut h, &Type::Bytes(32)) {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                h.span,
                                format!(
                                    "`{adt_name}.insertHashIndex` expects `Bytes<32>`, found `{}`",
                                    self.format_type(&h.ty)
                                ),
                            ));
                            return None;
                        }
                        let mut idx =
                            self.check_expr(arg_nodes[1], scope, Some(&Type::Uint(64)))?;
                        if !self.coerce_or_check(&mut idx, &Type::Uint(64)) {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                idx.span,
                                format!(
                                    "`{adt_name}.insertHashIndex` expects index `Uint<64>`, found `{}`",
                                    self.format_type(&idx.ty)
                                ),
                            ));
                            return None;
                        }
                        make_call(
                            if historic {
                                LedgerOp::HistoricMerkleTreeInsertHashIndex
                            } else {
                                LedgerOp::MerkleTreeInsertHashIndex
                            },
                            vec![h, idx],
                            Type::unit(),
                            target_adt,
                        )
                    }
                    "insertIndex" => {
                        if arg_nodes.len() != 2 {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                call_span,
                                format!("`{adt_name}.insertIndex` takes 2 arguments"),
                            ));
                            return None;
                        }
                        let mut item = self.check_expr(arg_nodes[0], scope, Some(&value))?;
                        if !self.coerce_or_check(&mut item, &value) {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                item.span,
                                format!(
                                    "`{adt_name}.insertIndex` expects `{}`, found `{}`",
                                    self.format_type(&value),
                                    self.format_type(&item.ty)
                                ),
                            ));
                            return None;
                        }
                        let mut idx =
                            self.check_expr(arg_nodes[1], scope, Some(&Type::Uint(64)))?;
                        if !self.coerce_or_check(&mut idx, &Type::Uint(64)) {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                idx.span,
                                format!(
                                    "`{adt_name}.insertIndex` expects index `Uint<64>`, found `{}`",
                                    self.format_type(&idx.ty)
                                ),
                            ));
                            return None;
                        }
                        make_call(
                            if historic {
                                LedgerOp::HistoricMerkleTreeInsertIndex
                            } else {
                                LedgerOp::MerkleTreeInsertIndex
                            },
                            vec![item, idx],
                            Type::unit(),
                            target_adt,
                        )
                    }
                    "insertIndexDefault" => {
                        if arg_nodes.len() != 1 {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                call_span,
                                format!("`{adt_name}.insertIndexDefault` takes 1 argument"),
                            ));
                            return None;
                        }
                        let mut idx =
                            self.check_expr(arg_nodes[0], scope, Some(&Type::Uint(64)))?;
                        if !self.coerce_or_check(&mut idx, &Type::Uint(64)) {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                idx.span,
                                format!(
                                    "`{adt_name}.insertIndexDefault` expects index `Uint<64>`, found `{}`",
                                    self.format_type(&idx.ty)
                                ),
                            ));
                            return None;
                        }
                        make_call(
                            if historic {
                                LedgerOp::HistoricMerkleTreeInsertIndexDefault
                            } else {
                                LedgerOp::MerkleTreeInsertIndexDefault
                            },
                            vec![idx],
                            Type::unit(),
                            target_adt,
                        )
                    }
                    "resetHistory" if historic => {
                        if !arg_nodes.is_empty() {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                call_span,
                                "`HistoricMerkleTree.resetHistory` takes 0 arguments",
                            ));
                            return None;
                        }
                        make_call(
                            LedgerOp::HistoricMerkleTreeResetHistory,
                            Vec::new(),
                            Type::unit(),
                            target_adt,
                        )
                    }
                    "resetToDefault" => {
                        if !arg_nodes.is_empty() {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                call_span,
                                format!("`{adt_name}.resetToDefault` takes 0 arguments"),
                            ));
                            return None;
                        }
                        make_call(
                            if historic {
                                LedgerOp::HistoricMerkleTreeResetToDefault
                            } else {
                                LedgerOp::MerkleTreeResetToDefault
                            },
                            Vec::new(),
                            Type::unit(),
                            target_adt,
                        )
                    }
                    other => {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            method_span,
                            format!("`{adt_name}` has no method `{other}`"),
                        ));
                        None
                    }
                }
            }
        }
    }
    fn validate_declared_modules(&mut self, mod_ids: &[usize]) {
        // 1. Check each module (recursively for nested modules) for duplicate ledger fields and include cycles.
        fn check_module_body(analyzer: &mut Analyzer<'_>, unit: UnitId, decls: &[NodeIndex]) {
            let mut seen_ledgers: HashSet<String> = HashSet::new();
            let mut nested_mods: Vec<(UnitId, Vec<NodeIndex>)> = Vec::new();
            let mut include_specs: Vec<(String, Span)> = Vec::new();

            let prev = analyzer.units.switch(unit);
            for &d in decls {
                match analyzer.units.ast().node_tag(d) {
                    NodeTag::LedgerDecl => {
                        let ld = analyzer.units.ast().ledger_decl(d);
                        let name = analyzer.text(ld.name_token).to_owned();
                        let span = analyzer.units.ast().token_span(ld.name_token);
                        if !seen_ledgers.insert(name.clone()) {
                            analyzer.diagnostics.push(CompactDiagnostic::error(
                                analyzer.units.file(),
                                span,
                                format!("duplicate ledger field `{name}`"),
                            ));
                        }
                    }
                    NodeTag::ModuleDecl => {
                        let md = analyzer.units.ast().module_decl(d);
                        let body: Vec<_> = analyzer
                            .units
                            .ast()
                            .extra_nodes(md.decls_start, md.decls_end)
                            .collect();
                        nested_mods.push((unit, body));
                    }
                    NodeTag::IncludeDecl => {
                        let inc = analyzer.units.ast().include_decl(d);
                        let spec = unquote_string(analyzer.text(inc.path_token));
                        let span = analyzer.units.ast().token_span(inc.path_token);
                        include_specs.push((spec, span));
                    }
                    _ => {}
                }
            }
            let from_file = analyzer.units.file().clone();
            analyzer.units.switch(prev);

            for (spec, span) in include_specs {
                if analyzer.include_stack.contains(&spec) {
                    analyzer.diagnostics.push(CompactDiagnostic::error(
                        &from_file,
                        span,
                        format!("cyclic `include` of `{spec}`"),
                    ));
                    continue;
                }
                if let Ok((inc_file, inc_ast)) = analyzer.loader.load(&from_file, &spec) {
                    let inc_unit = analyzer.units.push_owned(inc_file, inc_ast);
                    let prev_u = analyzer.units.switch(inc_unit);
                    let inc_decls: Vec<_> = analyzer.units.ast().root_decls().collect();
                    analyzer.units.switch(prev_u);
                    analyzer.include_stack.push(spec);
                    check_module_body(analyzer, inc_unit, &inc_decls);
                    analyzer.include_stack.pop();
                }
            }
            for (nu, nd) in nested_mods {
                check_module_body(analyzer, nu, &nd);
            }
        }

        // 2. Build module import graph and detect self/mutual import cycles among declared modules.
        let mut name_to_mid: HashMap<String, usize> = HashMap::new();
        for &mid in mod_ids {
            name_to_mid.insert(self.modules[mid].name.clone(), mid);
        }
        let mut edges: HashMap<usize, Vec<(usize, Span)>> = HashMap::new();
        for &mid in mod_ids {
            let tmpl = self.modules[mid].clone();
            check_module_body(self, tmpl.unit, &tmpl.decls);
            let prev = self.units.switch(tmpl.unit);
            let mut inner_mod_names: HashSet<String> = HashSet::new();
            for &d in &tmpl.decls {
                if self.units.ast().node_tag(d) == NodeTag::ModuleDecl {
                    let md = self.units.ast().module_decl(d);
                    inner_mod_names.insert(self.text(md.name_token).to_owned());
                } else if self.units.ast().node_tag(d) == NodeTag::ImportDecl {
                    let imp = self.units.ast().import_decl(d);
                    if self.units.ast().token_tag(imp.name_token) == TokenTag::Ident {
                        let target = self.text(imp.name_token).to_owned();
                        if !inner_mod_names.contains(&target)
                            && let Some(&tmid) = name_to_mid.get(&target)
                        {
                            edges
                                .entry(mid)
                                .or_default()
                                .push((tmid, self.units.ast().token_span(imp.name_token)));
                        }
                    }
                }
            }
            self.units.switch(prev);
        }

        fn dfs_mod_cycle(
            u: usize,
            edges: &HashMap<usize, Vec<(usize, Span)>>,
            visiting: &mut HashSet<usize>,
            visited: &mut HashSet<usize>,
        ) -> Option<Span> {
            if visited.contains(&u) {
                return None;
            }
            visiting.insert(u);
            if let Some(neighbors) = edges.get(&u) {
                for &(v, span) in neighbors {
                    if visiting.contains(&v) {
                        return Some(span);
                    }
                    if let Some(s) = dfs_mod_cycle(v, edges, visiting, visited) {
                        return Some(s);
                    }
                }
            }
            visiting.remove(&u);
            visited.insert(u);
            None
        }

        let mut visiting = HashSet::new();
        let mut visited = HashSet::new();
        for &mid in mod_ids {
            if let Some(span) = dfs_mod_cycle(mid, &edges, &mut visiting, &mut visited) {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    span,
                    format!(
                        "cyclic module import involving `{}`",
                        self.modules[mid].name
                    ),
                ));
                break;
            }
        }
    }

    fn eval_const_u128_in_scope(&self, expr: &Expr) -> Option<u128> {
        match &expr.kind {
            ExprKind::IntLit(v) => Some(*v),
            ExprKind::BoolLit(b) => Some(u128::from(*b)),
            ExprKind::LocalRef(lid) => self.const_int_locals.get(lid).copied(),
            ExprKind::Cast { expr, .. } | ExprKind::Disclose(expr) => {
                self.eval_const_u128_in_scope(expr)
            }
            ExprKind::Binary { op, lhs, rhs } => {
                let a = self.eval_const_u128_in_scope(lhs)?;
                let b = self.eval_const_u128_in_scope(rhs)?;
                match op {
                    BinaryOp::Add => a.checked_add(b),
                    BinaryOp::Sub => a.checked_sub(b),
                    BinaryOp::Mul => a.checked_mul(b),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn is_loop_index_expr(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::LocalRef(lid) => {
                self.loop_index_locals.contains(lid) || self.const_int_locals.contains_key(lid)
            }
            ExprKind::IntLit(_) => true,
            ExprKind::Cast { expr, .. } | ExprKind::Disclose(expr) => self.is_loop_index_expr(expr),
            ExprKind::Binary { lhs, rhs, .. } => {
                self.is_loop_index_expr(lhs) && self.is_loop_index_expr(rhs)
            }
            _ => false,
        }
    }
}

fn mangle_name(prefix: Option<&str>, name: &str) -> String {
    match prefix {
        Some(p) => format!("{p}{name}"),
        None => name.to_owned(),
    }
}

fn eval_const_u128(expr: &Expr) -> Option<u128> {
    match &expr.kind {
        ExprKind::IntLit(v) => Some(*v),
        ExprKind::Cast { expr, .. } | ExprKind::Disclose(expr) => eval_const_u128(expr),
        ExprKind::Binary { op, lhs, rhs } => {
            let a = eval_const_u128(lhs)?;
            let b = eval_const_u128(rhs)?;
            match op {
                BinaryOp::Add => a.checked_add(b),
                BinaryOp::Sub => a.checked_sub(b),
                BinaryOp::Mul => a.checked_mul(b),
                _ => None,
            }
        }
        _ => None,
    }
}

fn unquote_string(raw: &str) -> String {
    String::from_utf8_lossy(&compact_ast::unescape_string_bytes(raw)).into_owned()
}

fn propagate_purity(
    file: &SourceFile,
    program: &mut Program,
    sigs: &[CircuitSig],
    diagnostics: &mut DiagnosticBag,
) {
    let n = program.circuits.len();
    let mut touches_ledger = vec![false; n];
    let mut calls_witness = vec![false; n];
    let mut direct_calls: Vec<Vec<CircuitId>> = vec![Vec::new(); n];

    for c in &program.circuits {
        let idx = c.id.0 as usize;
        let (l, w) = stmts_effects(&c.body, &mut direct_calls[idx]);
        touches_ledger[idx] = l;
        calls_witness[idx] = w;
    }

    let mut changed = true;
    while changed {
        changed = false;
        for idx in 0..n {
            for &callee in &direct_calls[idx] {
                let cidx = callee.0 as usize;
                if touches_ledger[cidx] && !touches_ledger[idx] {
                    touches_ledger[idx] = true;
                    changed = true;
                }
                if calls_witness[cidx] && !calls_witness[idx] {
                    calls_witness[idx] = true;
                    changed = true;
                }
            }
        }
    }

    for c in &mut program.circuits {
        let idx = c.id.0 as usize;
        c.pure = !touches_ledger[idx] && !calls_witness[idx];
        c.proof = c.exported && touches_ledger[idx];
        if sigs[idx].declared_pure && !c.pure {
            diagnostics.push(CompactDiagnostic::error(
                file,
                sigs[idx].name_span,
                format!(
                    "circuit `{}` is declared `pure` but accesses ledger or witness state",
                    c.name
                ),
            ));
        }
    }
}

fn stmts_effects(stmts: &[Stmt], calls: &mut Vec<CircuitId>) -> (bool, bool) {
    let (mut l, mut w) = (false, false);
    for stmt in stmts {
        let (sl, sw) = match stmt {
            Stmt::Const { init, .. } => expr_effects(init, calls),
            Stmt::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                let (cl, cw) = expr_effects(cond, calls);
                let (tl, tw) = stmts_effects(then_branch, calls);
                let (el, ew) = stmts_effects(else_branch, calls);
                (cl | tl | el, cw | tw | ew)
            }
            Stmt::ForRange { body, .. } => stmts_effects(body, calls),
            Stmt::ForEach { iter, body, .. } => {
                let (il, iw) = expr_effects(iter, calls);
                let (bl, bw) = stmts_effects(body, calls);
                (il | bl, iw | bw)
            }
            Stmt::Expr(e) => expr_effects(e, calls),
            Stmt::Return { value: Some(e), .. } => expr_effects(e, calls),
            Stmt::Return { value: None, .. } => (false, false),
        };
        l |= sl;
        w |= sw;
    }
    (l, w)
}

fn expr_effects(expr: &Expr, calls: &mut Vec<CircuitId>) -> (bool, bool) {
    match &expr.kind {
        ExprKind::LedgerCall { key_path, args, .. } => {
            let mut w = false;
            for k in key_path {
                w |= expr_effects(k, calls).1;
            }
            for a in args {
                w |= expr_effects(a, calls).1;
            }
            (true, w)
        }
        ExprKind::WitnessCall { args, .. } | ExprKind::NativeWitness { args, .. } => {
            let mut l = false;
            for a in args {
                l |= expr_effects(a, calls).0;
            }
            (l, true)
        }
        ExprKind::CircuitCall { circuit, args } => {
            calls.push(*circuit);
            let (mut l, mut w) = (false, false);
            for a in args {
                let (al, aw) = expr_effects(a, calls);
                l |= al;
                w |= aw;
            }
            (l, w)
        }
        ExprKind::ContractCall { receiver, args, .. } => {
            let mut w = expr_effects(receiver, calls).1;
            for a in args {
                w |= expr_effects(a, calls).1;
            }
            (true, w)
        }
        ExprKind::Emit { value, .. } => {
            let (_, w) = expr_effects(value, calls);
            (true, w)
        }
        ExprKind::Serialize { value, .. } => expr_effects(value, calls),
        ExprKind::Deserialize { bytes, .. } => expr_effects(bytes, calls),
        ExprKind::Tuple(elems) | ExprKind::Vector(elems) | ExprKind::BytesPack(elems) => {
            let (mut l, mut w) = (false, false);
            for e in elems {
                let (el, ew) = expr_effects(e, calls);
                l |= el;
                w |= ew;
            }
            (l, w)
        }
        ExprKind::Block { stmts, tail } => {
            let (l1, w1) = stmts_effects(stmts, calls);
            let (l2, w2) = expr_effects(tail, calls);
            (l1 | l2, w1 | w2)
        }
        ExprKind::Unary { operand, .. }
        | ExprKind::Cast { expr: operand, .. }
        | ExprKind::Assert { cond: operand, .. }
        | ExprKind::Disclose(operand)
        | ExprKind::PersistentHash { arg: operand, .. }
        | ExprKind::Keccak256 { arg: operand, .. }
        | ExprKind::Sha512 { arg: operand, .. }
        | ExprKind::TransientHash { arg: operand, .. }
        | ExprKind::DegradeToTransient(operand)
        | ExprKind::UpgradeFromTransient(operand)
        | ExprKind::FieldInv(operand)
        | ExprKind::EcNeg(operand)
        | ExprKind::EcMulGenerator(operand)
        | ExprKind::HashToCurve { arg: operand, .. }
        | ExprKind::PointCoord { point: operand, .. }
        | ExprKind::MerkleTreePathRoot { path: operand, .. }
        | ExprKind::FieldAccess { base: operand, .. }
        | ExprKind::Slice { base: operand, .. }
        | ExprKind::MaybeSome(operand) => expr_effects(operand, calls),
        ExprKind::EcAdd { lhs: a, rhs: b }
        | ExprKind::EcMul {
            point: a,
            scalar: b,
        }
        | ExprKind::ConstructJubjubPoint { x: a, y: b } => {
            let (l1, w1) = expr_effects(a, calls);
            let (l2, w2) = expr_effects(b, calls);
            (l1 | l2, w1 | w2)
        }
        ExprKind::PersistentCommit { value, rand, .. }
        | ExprKind::TransientCommit { value, rand, .. } => {
            let (l1, w1) = expr_effects(value, calls);
            let (l2, w2) = expr_effects(rand, calls);
            (l1 | l2, w1 | w2)
        }
        ExprKind::Index { base, index } => {
            let (l1, w1) = expr_effects(base, calls);
            let (l2, w2) = expr_effects(index, calls);
            (l1 | l2, w1 | w2)
        }
        ExprKind::StructLit { fields } => {
            let (mut l, mut w) = (false, false);
            for (_, e) in fields {
                let (el, ew) = expr_effects(e, calls);
                l |= el;
                w |= ew;
            }
            (l, w)
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            let (l1, w1) = expr_effects(lhs, calls);
            let (l2, w2) = expr_effects(rhs, calls);
            (l1 | l2, w1 | w2)
        }
        ExprKind::Ternary {
            cond,
            then_branch,
            else_branch,
        } => {
            let (l1, w1) = expr_effects(cond, calls);
            let (l2, w2) = expr_effects(then_branch, calls);
            let (l3, w3) = expr_effects(else_branch, calls);
            (l1 | l2 | l3, w1 | w2 | w3)
        }
        ExprKind::IntLit(_)
        | ExprKind::BoolLit(_)
        | ExprKind::BytesLit(_)
        | ExprKind::Default(_)
        | ExprKind::DefaultAdt(_)
        | ExprKind::ParamRef(_)
        | ExprKind::LocalRef(_)
        | ExprKind::EnumVariant { .. }
        | ExprKind::MaybeNone(_) => (false, false),
    }
}

fn is_builtin_type_name(name: &str) -> bool {
    matches!(
        name,
        "Field"
            | "Boolean"
            | "Uint"
            | "Bytes"
            | "Vector"
            | "Opaque"
            | "Counter"
            | "Set"
            | "List"
            | "Map"
            | "MerkleTree"
            | "HistoricMerkleTree"
            | "Kernel"
    )
}

fn is_stdlib_builtin_type(name: &str) -> bool {
    matches!(
        name,
        "Maybe"
            | "Either"
            | "MerkleTreeDigest"
            | "MerkleTreePathEntry"
            | "MerkleTreePath"
            | "JubjubScalar"
            | "JubjubPoint"
            | "Secp256k1Base"
            | "Secp256k1Scalar"
            | "Secp256k1Point"
            | "Secp256r1Base"
            | "Secp256r1Scalar"
            | "Secp256r1Point"
            | "Curve25519Base"
            | "Curve25519Scalar"
            | "Curve25519Point"
    )
}

fn is_stdlib_type_name(name: &str) -> bool {
    is_stdlib_builtin_type(name)
        || matches!(
            name,
            "ZswapCoinPublicKey"
                | "ContractAddress"
                | "UserAddress"
                | "ShieldedCoinInfo"
                | "QualifiedShieldedCoinInfo"
                | "ShieldedSendResult"
                | "CurvePoint"
                | "ShieldedSpend"
                | "ShieldedReceive"
                | "ShieldedMint"
                | "ShieldedBurn"
                | "UnshieldedSpend"
                | "UnshieldedReceive"
                | "UnshieldedMint"
                | "UnshieldedBurn"
                | "Paused"
                | "Unpaused"
                | "Misc"
        )
}

fn reject_sealed_mutations(file: &SourceFile, program: &Program, diagnostics: &mut DiagnosticBag) {
    fn walk_stmts(
        stmts: &[Stmt],
        program: &Program,
        visited_circuits: &mut HashSet<CircuitId>,
        file: &SourceFile,
        diagnostics: &mut DiagnosticBag,
    ) {
        for s in stmts {
            match s {
                Stmt::Const { init, .. } | Stmt::Expr(init) => {
                    walk_expr(init, program, visited_circuits, file, diagnostics);
                }
                Stmt::Return { value, .. } => {
                    if let Some(v) = value {
                        walk_expr(v, program, visited_circuits, file, diagnostics);
                    }
                }
                Stmt::If {
                    cond,
                    then_branch,
                    else_branch,
                    ..
                } => {
                    walk_expr(cond, program, visited_circuits, file, diagnostics);
                    walk_stmts(then_branch, program, visited_circuits, file, diagnostics);
                    walk_stmts(else_branch, program, visited_circuits, file, diagnostics);
                }
                Stmt::ForRange { body, .. } => {
                    walk_stmts(body, program, visited_circuits, file, diagnostics);
                }
                Stmt::ForEach { iter, body, .. } => {
                    walk_expr(iter, program, visited_circuits, file, diagnostics);
                    walk_stmts(body, program, visited_circuits, file, diagnostics);
                }
            }
        }
    }

    fn walk_expr(
        expr: &Expr,
        program: &Program,
        visited_circuits: &mut HashSet<CircuitId>,
        file: &SourceFile,
        diagnostics: &mut DiagnosticBag,
    ) {
        match &expr.kind {
            ExprKind::LedgerCall {
                field,
                key_path,
                op,
                args,
                ..
            } => {
                let lf = program.ledger_field(*field);
                if lf.sealed && op.is_mutating() {
                    diagnostics.push(CompactDiagnostic::error(
                        file,
                        expr.span,
                        format!(
                            "cannot mutate sealed ledger field `{}` outside `constructor`",
                            lf.name
                        ),
                    ));
                }
                for k in key_path {
                    walk_expr(k, program, visited_circuits, file, diagnostics);
                }
                for a in args {
                    walk_expr(a, program, visited_circuits, file, diagnostics);
                }
            }
            ExprKind::CircuitCall { circuit, args } => {
                for a in args {
                    walk_expr(a, program, visited_circuits, file, diagnostics);
                }
                if visited_circuits.insert(*circuit) {
                    let callee = program.circuit(*circuit);
                    walk_stmts(&callee.body, program, visited_circuits, file, diagnostics);
                }
            }
            ExprKind::WitnessCall { args, .. }
            | ExprKind::NativeWitness { args, .. }
            | ExprKind::Tuple(args)
            | ExprKind::Vector(args)
            | ExprKind::BytesPack(args) => {
                for a in args {
                    walk_expr(a, program, visited_circuits, file, diagnostics);
                }
            }
            ExprKind::ContractCall { receiver, args, .. } => {
                walk_expr(receiver, program, visited_circuits, file, diagnostics);
                for a in args {
                    walk_expr(a, program, visited_circuits, file, diagnostics);
                }
            }
            ExprKind::StructLit { fields } => {
                for (_, e) in fields {
                    walk_expr(e, program, visited_circuits, file, diagnostics);
                }
            }
            ExprKind::Block { stmts, tail } => {
                walk_stmts(stmts, program, visited_circuits, file, diagnostics);
                walk_expr(tail, program, visited_circuits, file, diagnostics);
            }
            ExprKind::Binary { lhs, rhs, .. }
            | ExprKind::Index {
                base: lhs,
                index: rhs,
            }
            | ExprKind::EcAdd { lhs, rhs }
            | ExprKind::EcMul {
                point: lhs,
                scalar: rhs,
            }
            | ExprKind::ConstructJubjubPoint { x: lhs, y: rhs }
            | ExprKind::PersistentCommit {
                value: lhs,
                rand: rhs,
                ..
            }
            | ExprKind::TransientCommit {
                value: lhs,
                rand: rhs,
                ..
            } => {
                walk_expr(lhs, program, visited_circuits, file, diagnostics);
                walk_expr(rhs, program, visited_circuits, file, diagnostics);
            }
            ExprKind::Ternary {
                cond,
                then_branch,
                else_branch,
            } => {
                walk_expr(cond, program, visited_circuits, file, diagnostics);
                walk_expr(then_branch, program, visited_circuits, file, diagnostics);
                walk_expr(else_branch, program, visited_circuits, file, diagnostics);
            }
            ExprKind::Unary { operand, .. }
            | ExprKind::Cast { expr: operand, .. }
            | ExprKind::Assert { cond: operand, .. }
            | ExprKind::Disclose(operand)
            | ExprKind::Emit { value: operand, .. }
            | ExprKind::Serialize { value: operand, .. }
            | ExprKind::Deserialize { bytes: operand, .. }
            | ExprKind::PersistentHash { arg: operand, .. }
            | ExprKind::Keccak256 { arg: operand, .. }
            | ExprKind::Sha512 { arg: operand, .. }
            | ExprKind::TransientHash { arg: operand, .. }
            | ExprKind::DegradeToTransient(operand)
            | ExprKind::UpgradeFromTransient(operand)
            | ExprKind::FieldInv(operand)
            | ExprKind::EcNeg(operand)
            | ExprKind::EcMulGenerator(operand)
            | ExprKind::HashToCurve { arg: operand, .. }
            | ExprKind::PointCoord { point: operand, .. }
            | ExprKind::MerkleTreePathRoot { path: operand, .. }
            | ExprKind::FieldAccess { base: operand, .. }
            | ExprKind::Slice { base: operand, .. }
            | ExprKind::MaybeSome(operand) => {
                walk_expr(operand, program, visited_circuits, file, diagnostics);
            }
            ExprKind::IntLit(_)
            | ExprKind::BoolLit(_)
            | ExprKind::BytesLit(_)
            | ExprKind::Default(_)
            | ExprKind::DefaultAdt(_)
            | ExprKind::ParamRef(_)
            | ExprKind::LocalRef(_)
            | ExprKind::EnumVariant { .. }
            | ExprKind::MaybeNone(_) => {}
        }
    }

    for circuit in &program.circuits {
        if !circuit.exported {
            continue;
        }
        let mut visited = HashSet::new();
        visited.insert(circuit.id);
        walk_stmts(&circuit.body, program, &mut visited, file, diagnostics);
    }
}

fn check_returns_and_reachability(
    file: &SourceFile,
    program: &Program,
    diagnostics: &mut DiagnosticBag,
) {
    fn check_stmts(
        stmts: &[Stmt],
        in_for: bool,
        file: &SourceFile,
        diagnostics: &mut DiagnosticBag,
    ) -> bool {
        let mut always_returns = false;
        for s in stmts {
            match s {
                Stmt::Return { span, .. } => {
                    if in_for {
                        diagnostics.push(CompactDiagnostic::error(
                            file,
                            *span,
                            "`return` statement is not allowed inside a `for` loop",
                        ));
                    }
                    always_returns = true;
                }
                Stmt::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    let t = check_stmts(then_branch, in_for, file, diagnostics);
                    let e = check_stmts(else_branch, in_for, file, diagnostics);
                    if t && e {
                        always_returns = true;
                    }
                }
                Stmt::ForRange { body, .. } | Stmt::ForEach { body, .. } => {
                    let _ = check_stmts(body, true, file, diagnostics);
                }
                Stmt::Const { .. } | Stmt::Expr(_) => {}
            }
        }
        always_returns
    }

    if let Some(ctor) = &program.constructor {
        let _ = check_stmts(&ctor.body, false, file, diagnostics);
    }
    for c in &program.circuits {
        let returns = check_stmts(&c.body, false, file, diagnostics);
        if c.ret_type != Type::unit() && !returns {
            diagnostics.push(CompactDiagnostic::error(
                file,
                c.span,
                format!("circuit `{}` may exit without returning a value", c.name),
            ));
        }
    }
}

fn reject_case_insensitive_duplicate_exports(
    file: &SourceFile,
    program: &Program,
    diagnostics: &mut DiagnosticBag,
) {
    let mut seen: HashMap<String, (String, Span)> = HashMap::new();
    for c in &program.circuits {
        if !c.exported {
            continue;
        }
        let lower = c.name.to_ascii_lowercase();
        if let Some((prev, _)) = seen.get(&lower) {
            if prev != &c.name {
                diagnostics.push(CompactDiagnostic::error(
                    file,
                    c.span,
                    format!(
                        "exported circuit name `{}` conflicts case-insensitively with `{prev}`",
                        c.name
                    ),
                ));
            }
        } else {
            seen.insert(lower, (c.name.clone(), c.span));
        }
    }
}

fn event_tag_of(name: &str) -> Option<u8> {
    match name {
        "ShieldedSpend" => Some(0),
        "ShieldedReceive" => Some(1),
        "ShieldedMint" => Some(2),
        "ShieldedBurn" => Some(3),
        "UnshieldedSpend" => Some(4),
        "UnshieldedReceive" => Some(5),
        "UnshieldedMint" => Some(6),
        "UnshieldedBurn" => Some(7),
        "Paused" => Some(8),
        "Unpaused" => Some(9),
        "Misc" => Some(10),
        _ => None,
    }
}

fn check_contract_implements(
    file: &SourceFile,
    program: &Program,
    implements: &[(Type, Span)],
    diagnostics: &mut DiagnosticBag,
) {
    for (ty, span) in implements {
        let Type::Contract(cid) = *program.underlying_type(ty) else {
            diagnostics.push(CompactDiagnostic::error(
                file,
                *span,
                format!(
                    "non-contract type `{}` in `contract implements` declaration",
                    program.format_type(ty)
                ),
            ));
            continue;
        };
        let decl = program.contract_decl(cid);
        for req in &decl.circuits {
            let Some(found) = program
                .circuits
                .iter()
                .find(|c| c.exported && c.name == req.name)
            else {
                diagnostics.push(CompactDiagnostic::error(
                    file,
                    *span,
                    format!(
                        "contract implements `{}` failure: this contract does not export a circuit named `{}`",
                        decl.name, req.name
                    ),
                ));
                continue;
            };
            if found.pure {
                diagnostics.push(CompactDiagnostic::error(
                    file,
                    *span,
                    format!(
                        "contract implements `{}` failure: exported circuit `{}` is pure, but circuits in a contract interface must have a proof",
                        decl.name, req.name
                    ),
                ));
            }
            if found.params.len() != req.params.len() {
                diagnostics.push(CompactDiagnostic::error(
                    file,
                    *span,
                    format!(
                        "contract implements `{}` failure: circuit `{}` takes {} argument(s) rather than {}",
                        decl.name,
                        req.name,
                        found.params.len(),
                        req.params.len()
                    ),
                ));
                continue;
            }
            for (i, (fp, rp)) in found.params.iter().zip(&req.params).enumerate() {
                if fp.ty != rp.ty {
                    diagnostics.push(CompactDiagnostic::error(
                        file,
                        *span,
                        format!(
                            "contract implements `{}` failure: argument {} of circuit `{}` has type `{}` rather than `{}`",
                            decl.name,
                            i + 1,
                            req.name,
                            program.format_type(&fp.ty),
                            program.format_type(&rp.ty)
                        ),
                    ));
                }
            }
            if found.ret_type != req.ret_type {
                diagnostics.push(CompactDiagnostic::error(
                    file,
                    *span,
                    format!(
                        "contract implements `{}` failure: circuit `{}` returns `{}` rather than `{}`",
                        decl.name,
                        req.name,
                        program.format_type(&found.ret_type),
                        program.format_type(&req.ret_type)
                    ),
                ));
            }
        }
    }
}

fn reject_constructor_forbidden_ops(
    file: &SourceFile,
    program: &Program,
    diagnostics: &mut DiagnosticBag,
) {
    fn visit_stmts(
        stmts: &[Stmt],
        program: &Program,
        file: &SourceFile,
        diagnostics: &mut DiagnosticBag,
        visited: &mut HashSet<CircuitId>,
    ) {
        for stmt in stmts {
            match stmt {
                Stmt::Const { init, .. } => visit_expr(init, program, file, diagnostics, visited),
                Stmt::If {
                    cond,
                    then_branch,
                    else_branch,
                    ..
                } => {
                    visit_expr(cond, program, file, diagnostics, visited);
                    visit_stmts(then_branch, program, file, diagnostics, visited);
                    visit_stmts(else_branch, program, file, diagnostics, visited);
                }
                Stmt::ForRange { body, .. } => {
                    visit_stmts(body, program, file, diagnostics, visited)
                }
                Stmt::ForEach { iter, body, .. } => {
                    visit_expr(iter, program, file, diagnostics, visited);
                    visit_stmts(body, program, file, diagnostics, visited);
                }
                Stmt::Expr(e) => visit_expr(e, program, file, diagnostics, visited),
                Stmt::Return { value: Some(e), .. } => {
                    visit_expr(e, program, file, diagnostics, visited)
                }
                Stmt::Return { value: None, .. } => {}
            }
        }
    }
    fn visit_expr(
        expr: &Expr,
        program: &Program,
        file: &SourceFile,
        diagnostics: &mut DiagnosticBag,
        visited: &mut HashSet<CircuitId>,
    ) {
        match &expr.kind {
            ExprKind::ContractCall {
                receiver,
                args,
                method,
                ..
            } => {
                diagnostics.push(CompactDiagnostic::error(
                    file,
                    expr.span,
                    format!("cross-contract call `{method}` is not permitted inside a constructor"),
                ));
                visit_expr(receiver, program, file, diagnostics, visited);
                for a in args {
                    visit_expr(a, program, file, diagnostics, visited);
                }
            }
            ExprKind::Emit {
                value, event_name, ..
            } => {
                diagnostics.push(CompactDiagnostic::error(
                    file,
                    expr.span,
                    format!("`emit({event_name})` is not permitted inside a constructor"),
                ));
                visit_expr(value, program, file, diagnostics, visited);
            }
            ExprKind::CircuitCall { circuit, args } => {
                for a in args {
                    visit_expr(a, program, file, diagnostics, visited);
                }
                if visited.insert(*circuit) {
                    visit_stmts(
                        &program.circuit(*circuit).body,
                        program,
                        file,
                        diagnostics,
                        visited,
                    );
                }
            }
            ExprKind::Tuple(es)
            | ExprKind::Vector(es)
            | ExprKind::BytesPack(es)
            | ExprKind::WitnessCall { args: es, .. }
            | ExprKind::NativeWitness { args: es, .. } => {
                for e in es {
                    visit_expr(e, program, file, diagnostics, visited);
                }
            }
            ExprKind::Block { stmts, tail } => {
                visit_stmts(stmts, program, file, diagnostics, visited);
                visit_expr(tail, program, file, diagnostics, visited);
            }
            ExprKind::StructLit { fields } => {
                for (_, e) in fields {
                    visit_expr(e, program, file, diagnostics, visited);
                }
            }
            ExprKind::LedgerCall { key_path, args, .. } => {
                for k in key_path {
                    visit_expr(k, program, file, diagnostics, visited);
                }
                for a in args {
                    visit_expr(a, program, file, diagnostics, visited);
                }
            }
            ExprKind::Unary { operand, .. }
            | ExprKind::Cast { expr: operand, .. }
            | ExprKind::Assert { cond: operand, .. }
            | ExprKind::Disclose(operand)
            | ExprKind::PersistentHash { arg: operand, .. }
            | ExprKind::Keccak256 { arg: operand, .. }
            | ExprKind::Sha512 { arg: operand, .. }
            | ExprKind::TransientHash { arg: operand, .. }
            | ExprKind::DegradeToTransient(operand)
            | ExprKind::UpgradeFromTransient(operand)
            | ExprKind::FieldInv(operand)
            | ExprKind::EcNeg(operand)
            | ExprKind::EcMulGenerator(operand)
            | ExprKind::HashToCurve { arg: operand, .. }
            | ExprKind::PointCoord { point: operand, .. }
            | ExprKind::Serialize { value: operand, .. }
            | ExprKind::Deserialize { bytes: operand, .. }
            | ExprKind::MerkleTreePathRoot { path: operand, .. }
            | ExprKind::FieldAccess { base: operand, .. }
            | ExprKind::Slice { base: operand, .. }
            | ExprKind::MaybeSome(operand) => {
                visit_expr(operand, program, file, diagnostics, visited)
            }
            ExprKind::PersistentCommit {
                value: a, rand: b, ..
            }
            | ExprKind::TransientCommit {
                value: a, rand: b, ..
            }
            | ExprKind::Index { base: a, index: b }
            | ExprKind::Binary { lhs: a, rhs: b, .. }
            | ExprKind::EcAdd { lhs: a, rhs: b }
            | ExprKind::EcMul {
                point: a,
                scalar: b,
            }
            | ExprKind::ConstructJubjubPoint { x: a, y: b } => {
                visit_expr(a, program, file, diagnostics, visited);
                visit_expr(b, program, file, diagnostics, visited);
            }
            ExprKind::Ternary {
                cond,
                then_branch,
                else_branch,
            } => {
                visit_expr(cond, program, file, diagnostics, visited);
                visit_expr(then_branch, program, file, diagnostics, visited);
                visit_expr(else_branch, program, file, diagnostics, visited);
            }
            ExprKind::IntLit(_)
            | ExprKind::BoolLit(_)
            | ExprKind::BytesLit(_)
            | ExprKind::Default(_)
            | ExprKind::DefaultAdt(_)
            | ExprKind::ParamRef(_)
            | ExprKind::LocalRef(_)
            | ExprKind::EnumVariant { .. }
            | ExprKind::MaybeNone(_) => {}
        }
    }

    if let Some(ctor) = &program.constructor {
        let mut visited = HashSet::new();
        visit_stmts(&ctor.body, program, file, diagnostics, &mut visited);
    }
}

#[cfg(test)]
mod tests {
    use compact_parser::parse;
    use compact_span::SourceMap;
    use compact_test_utils::assert_compact_snapshot;

    use super::check;

    fn check_and_dump(src: &str) -> String {
        let mut sm = SourceMap::new();
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(
            !parsed.diagnostics.has_errors(),
            "unexpected parse errors: {:?}",
            parsed.diagnostics
        );
        let checked = check(file, &parsed.ast);
        assert!(
            !checked.diagnostics.has_errors(),
            "unexpected sema errors: {:?}",
            checked.diagnostics
        );
        checked.program.dump()
    }

    #[test]
    fn check_counter_contract() {
        assert_compact_snapshot!(
            r#"
            import CompactStandardLibrary;

            export ledger round: Counter;

            export circuit increment(): [] {
              round.increment(1);
            }
            "#,
            check_and_dump
        );
    }

    #[test]
    fn check_cell_enum_and_helper() {
        assert_compact_snapshot!(
            r#"
            import CompactStandardLibrary;

            enum STATE { unset, set }

            export ledger value: Field;
            ledger state: STATE;

            circuit in_state(s: STATE): Boolean {
              return state == s;
            }

            export circuit set(v: Field): [] {
              assert(in_state(STATE.unset), "already set");
              value = disclose(v);
              state = STATE.set;
            }

            export circuit get(): Field {
              const is_set = in_state(STATE.set);
              return is_set ? value : 0 as Field;
            }
            "#,
            check_and_dump
        );
    }

    #[test]
    fn check_tiny_contract() {
        assert_compact_snapshot!(
            r#"
            export {Maybe}
            export {set, get, clear, public_key}

            import CompactStandardLibrary;

            enum STATE { unset, set }

            ledger authority: Bytes<32>;
            export ledger value: Field;
            ledger state: STATE;

            constructor(v: Field) {
              const sk = private$secret_key();
              authority = public_key(sk);
              value = disclose(v);
              state = STATE.set;
            }

            witness private$secret_key(): Bytes<32>;

            circuit in_state(s: STATE): Boolean {
              return state == s;
            }

            circuit set(v: Field): [] {
              assert(in_state(STATE.unset), "set: attempted to overwrite recorded value");
              const sk = private$secret_key();
              const apk = public_key(sk);
              authority = apk;
              value = disclose(v);
              state = STATE.set;
            }

            circuit get(): Maybe<Field> {
              return in_state(STATE.set) ? some<Field>(value) : none<Field>();
            }

            circuit clear(): [] {
              assert(in_state(STATE.set), "clear: no value is currently recorded");
              const sk = private$secret_key();
              const apk = public_key(sk);
              assert(apk == authority, "clear: attempted clear without proper authorization");
              authority = default<Bytes<32>>;
              value = default<Field>;
              state = STATE.unset;
            }

            circuit public_key(sk: Bytes<32>): Bytes<32> {
              return disclose(persistentHash<Vector<2, Bytes<32>>>([pad(32, "lares:tiny:pk:"), sk]));
            }
            "#,
            check_and_dump
        );
    }

    #[test]
    fn rejects_undisclosed_constructor_param_write() {
        let mut sm = SourceMap::new();
        let src = r#"
            export ledger value: Field;
            constructor(v: Field) {
              value = v;
            }
        "#;
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let checked = check(file, &parsed.ast);
        assert!(checked.diagnostics.has_errors());
        assert!(
            checked.diagnostics.diagnostics[0]
                .message
                .contains("disclose"),
            "expected witness disclosure error, got: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn rejects_undisclosed_witness_param_write() {
        let mut sm = SourceMap::new();
        let src = r#"
            export ledger value: Field;
            export circuit set(v: Field): [] {
              value = v;
            }
        "#;
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let checked = check(file, &parsed.ast);
        assert!(checked.diagnostics.has_errors());
        assert!(
            checked.diagnostics.diagnostics[0]
                .message
                .contains("disclose")
        );
    }

    #[test]
    fn rejects_undisclosed_witness_return_write() {
        let mut sm = SourceMap::new();
        let src = r#"
            export ledger authority: Bytes<32>;
            witness secret(): Bytes<32>;
            export circuit leak(): [] {
              authority = secret();
            }
        "#;
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let checked = check(file, &parsed.ast);
        assert!(checked.diagnostics.has_errors());
        assert!(
            checked.diagnostics.diagnostics[0]
                .message
                .contains("witness `secret`")
        );
    }

    #[test]
    fn rejects_out_of_range_counter_increment() {
        let mut sm = SourceMap::new();
        let src =
            "export ledger round: Counter; export circuit inc(): [] { round.increment(70000); }";
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        let checked = check(file, &parsed.ast);
        assert!(checked.diagnostics.has_errors());
        assert!(
            checked.diagnostics.diagnostics[0]
                .message
                .contains("Uint<16>")
        );
    }

    #[test]
    fn rejects_undisclosed_witness_in_if_guarding_ledger() {
        let mut sm = SourceMap::new();
        let src = r#"
            enum Vote { yes, no }
            ledger tally_yes: Counter;
            ledger tally_no: Counter;
            witness secret_vote(): Vote;
            export circuit reveal(): [] {
              const v = secret_vote();
              if (v == Vote.yes) {
                tally_yes.increment(1);
              } else {
                tally_no.increment(1);
              }
            }
        "#;
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let checked = check(file, &parsed.ast);
        assert!(checked.diagnostics.has_errors());
        assert!(
            checked.diagnostics.diagnostics[0]
                .message
                .contains("disclose"),
            "expected witness disclosure error, got: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn rejects_unsatisfied_pragma_version() {
        let mut sm = SourceMap::new();
        let src = "pragma language_version >= 99.0.0;";
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let checked = check(file, &parsed.ast);
        assert!(checked.diagnostics.has_errors());
        assert!(
            checked.diagnostics.diagnostics[0]
                .message
                .contains("language_version"),
            "expected pragma version error, got: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn rejects_new_type_without_cast() {
        let mut sm = SourceMap::new();
        let src = r#"
            new type Secret = Field;
            export circuit f(x: Secret): Field {
              return x;
            }
        "#;
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let checked = check(file, &parsed.ast);
        assert!(checked.diagnostics.has_errors());
        assert!(
            checked.diagnostics.diagnostics[0]
                .message
                .contains("type mismatch")
                || checked.diagnostics.diagnostics[0]
                    .message
                    .contains("Secret"),
            "expected nominal new type error, got: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn rejects_out_of_bounds_vector_index() {
        let mut sm = SourceMap::new();
        let src = r#"
            export circuit f(v: Vector<3, Field>): Field {
              return v[3];
            }
        "#;
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let checked = check(file, &parsed.ast);
        assert!(checked.diagnostics.has_errors());
        assert!(
            checked.diagnostics.diagnostics[0]
                .message
                .contains("out of bounds"),
            "expected out of bounds error, got: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn rejects_tuple_destructure_length_mismatch() {
        let mut sm = SourceMap::new();
        let src = r#"
            export circuit f(v: Vector<2, Field>): Field {
              const [a, b, c] = v;
              return a + b + c;
            }
        "#;
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let checked = check(file, &parsed.ast);
        assert!(checked.diagnostics.has_errors());
        assert!(
            checked.diagnostics.diagnostics[0]
                .message
                .contains("destructuring pattern"),
            "expected destructuring mismatch error, got: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn rejects_compound_assign_on_non_counter() {
        let mut sm = SourceMap::new();
        let src = r#"
            ledger x: Field;
            export circuit f(): [] {
              x += 1;
            }
        "#;
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let checked = check(file, &parsed.ast);
        assert!(checked.diagnostics.has_errors());
        assert!(
            checked.diagnostics.diagnostics[0]
                .message
                .contains("Counter"),
            "expected Counter compound assign error, got: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn accepts_undisclosed_witness_inside_commitments() {
        let mut sm = SourceMap::new();
        let src = r#"
            import CompactStandardLibrary;
            export ledger pc: Bytes<32>;
            export ledger tc: Field;
            witness secret(): Field;
            witness rand_bytes(): Bytes<32>;
            witness rand_field(): Field;
            export circuit commit(): [] {
              pc = persistentCommit<Field>(secret(), rand_bytes());
              tc = transientCommit<Field>(secret(), rand_field());
            }
        "#;
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let checked = check(file, &parsed.ast);
        assert!(
            !checked.diagnostics.has_errors(),
            "expected commitments to clear witness taint without disclose, got: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn rejects_undisclosed_witness_passed_to_mint_shielded() {
        let mut sm = SourceMap::new();
        let src = r#"
            import CompactStandardLibrary;
            export circuit bad_mint(sep: Bytes<32>, amt: Uint<64>, nonce: Bytes<32>): ShieldedCoinInfo {
              const recip = right<ZswapCoinPublicKey, ContractAddress>(kernel.self());
              return mintShieldedToken(sep, amt, disclose(nonce), recip);
            }
        "#;
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let checked = check(file, &parsed.ast);
        assert!(checked.diagnostics.has_errors());
        assert!(
            checked
                .diagnostics
                .diagnostics
                .iter()
                .any(|d| d.message.contains("disclose")),
            "expected witness disclosure error through stdlib mintShieldedToken, got: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn rejects_mismatched_curve_points_in_ec_add() {
        let mut sm = SourceMap::new();
        let src = r#"
            import CompactStandardLibrary;
            export circuit bad_add(a: JubjubPoint, b: Secp256k1Point): JubjubPoint {
              return ecAdd(a, b);
            }
        "#;
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let checked = check(file, &parsed.ast);
        assert!(checked.diagnostics.has_errors());
        assert!(
            checked
                .diagnostics
                .diagnostics
                .iter()
                .any(|d| d.message.contains("ecAdd") && d.message.contains("mismatch")),
            "expected curve mismatch error in ecAdd, got: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn rejects_arithmetic_on_curve_points() {
        let mut sm = SourceMap::new();
        let src = r#"
            import CompactStandardLibrary;
            export circuit bad_plus(a: Secp256k1Point, b: Secp256k1Point): Secp256k1Point {
              return a + b;
            }
        "#;
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let checked = check(file, &parsed.ast);
        assert!(checked.diagnostics.has_errors());
        assert!(
            checked
                .diagnostics
                .diagnostics
                .iter()
                .any(|d| d.message.contains("arithmetic operator")),
            "expected arithmetic operator rejection on curve points, got: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn rejects_contract_implements_signature_mismatch() {
        let mut sm = SourceMap::new();
        let src = r#"
            contract Foo {
              circuit add(x: Field): Field;
            }
            contract implements Foo;
            export ledger v: Field;
            export circuit add(x: Uint<64>): Field {
              v = disclose(x as Field);
              return v;
            }
        "#;
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let checked = check(file, &parsed.ast);
        assert!(checked.diagnostics.has_errors());
        assert!(
            checked
                .diagnostics
                .diagnostics
                .iter()
                .any(|d| d.message.contains("contract implements")),
            "expected contract implements error, got: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn rejects_contract_call_and_emit_inside_constructor() {
        let mut sm = SourceMap::new();
        let src = r#"
            import CompactStandardLibrary;
            contract Inner {
              circuit ping(): [];
            }
            constructor(i: Inner) {
              disclose(i).ping();
              emit(Paused {});
            }
        "#;
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let checked = check(file, &parsed.ast);
        assert!(checked.diagnostics.has_errors());
        let msgs: Vec<_> = checked
            .diagnostics
            .diagnostics
            .iter()
            .map(|d| d.message.as_str())
            .collect();
        assert!(
            msgs.iter().any(|m| m.contains("cross-contract call"))
                && msgs.iter().any(|m| m.contains("emit")),
            "expected constructor errors for contract call and emit, got: {msgs:?}"
        );
    }

    #[test]
    fn rejects_undisclosed_witness_in_contract_call_and_emit() {
        let mut sm = SourceMap::new();
        let src = r#"
            import CompactStandardLibrary;
            contract Inner {
              circuit send(n: Bytes<32>): [];
            }
            export ledger target: Inner;
            export circuit bad(n: Bytes<32>): [] {
              emit(ShieldedSpend { nullifier: n });
              target.send(n);
            }
        "#;
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let checked = check(file, &parsed.ast);
        assert!(checked.diagnostics.has_errors());
        assert!(
            checked.diagnostics.diagnostics.len() >= 2
                && checked
                    .diagnostics
                    .diagnostics
                    .iter()
                    .all(|d| d.message.contains("disclose")),
            "expected WPP errors for emit and contract call, got: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn circuit_overloading_and_disambiguation() {
        let mut sm = SourceMap::new();
        let src = r#"
            circuit f(x: Uint<8>): Field { return x as Field; }
            circuit f(x: Uint<16>): Field { return (x + 1) as Field; }
            circuit f(x: Field, y: Field): Field { return x + y; }
            circuit g<T>(x: T): T { return x; }
            circuit g<#N>(x: Bytes<N>): Bytes<N> { return x; }

            export circuit run(a: Uint<8>, b: Uint<16>, c: Bytes<4>): Field {
              const r1 = f(a);
              const r2 = f(b);
              const r3 = f(r1, r2);
              const s1 = g<Field>(r3);
              const s2 = g<4>(c);
              return s1 + (s2[0] as Field);
            }
        "#;
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors(), "{:?}", parsed.diagnostics);
        let checked = check(file, &parsed.ast);
        assert!(
            !checked.diagnostics.has_errors(),
            "unexpected errors: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn rejects_ambiguous_circuit_overload() {
        let mut sm = SourceMap::new();
        let src = r#"
            circuit h(x: Uint<16>, y: Uint<8>): Field { return (x + y) as Field; }
            circuit h(x: Uint<8>, y: Uint<16>): Field { return (x + y) as Field; }

            export circuit run(a: Uint<8>, b: Uint<8>): Field {
              return h(a, b);
            }
        "#;
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let checked = check(file, &parsed.ast);
        assert!(checked.diagnostics.has_errors());
        assert!(
            checked
                .diagnostics
                .diagnostics
                .iter()
                .any(|d| d.message.contains("ambiguous")),
            "expected ambiguous overload error, got: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn uint_ranges_radices_escapes_cast_precedence_and_bytes_ops() {
        let mut sm = SourceMap::new();
        let src = r#"
            import CompactStandardLibrary;

            struct Point { x: Uint<0..255>; y: Uint<0..100000>; }

            export ledger c: Counter;
            export ledger tree: HistoricMerkleTree<4, Bytes<32>>;

            export circuit exercise(b: Bytes<4>, h: Bytes<32>): [Uint<8>, Point] {
              const hex: Uint<8> = 0x10;
              const bin: Uint<8> = 0b0101;
              const oct: Uint<8> = 0o12;
              const cast_prec: Uint<16> = hex + bin as Uint<16>;
              const p = Point { hex, cast_prec + oct };
              const msg: Bytes<5> = "a\nb\x21\0";
              const spread_v: Vector<4, Uint<8>> = [...b];
              const doubled = map((x: Uint<8>) => x + 1, b);
              const total = fold((acc: Field, x: Uint<8>) => acc + (x as Field), 0 as Field, b);
              for (const byte of b) {
                assert(byte >= 0, "ok");
              }
              const current: Uint<64> = c;
              assert(current >= 0 && total == total && spread_v[0] >= 0 && doubled[0] >= 0 && msg[0] >= 0, "ok");
              tree.insertHash(disclose(h));
              tree.resetHistory();
              return [b[1], p];
            }
        "#;
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors(), "{:?}", parsed.diagnostics);
        let checked = check(file, &parsed.ast);
        assert!(
            !checked.diagnostics.has_errors(),
            "unexpected errors: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn rejects_static_safety_and_cycle_violations() {
        let cases: &[(&str, &str)] = &[
            (
                "sealed mutation outside constructor",
                r#"
                export sealed ledger owner: Field;
                constructor() { owner = 1; }
                export circuit bad(): [] { owner = 2; }
                "#,
            ),
            (
                "return inside for loop",
                r#"
                export circuit bad(): Field {
                  for (const i of 0..3) { return i as Field; }
                  return 0;
                }
                "#,
            ),
            (
                "unreachable statement after return",
                r#"
                export circuit bad(): Field {
                  return 1;
                  const dead = 2;
                }
                "#,
            ),
            (
                "missing return in non-unit circuit",
                r#"
                export circuit bad(x: Boolean): Field {
                  if (x) { return 1; }
                }
                "#,
            ),
            (
                "duplicate const in same block",
                r#"
                export circuit bad(): Field {
                  const x = 1;
                  const x = 2;
                  return x;
                }
                "#,
            ),
            (
                "cyclic new type",
                r#"
                new type A = B;
                new type B = A;
                export circuit bad(): [] {}
                "#,
            ),
            (
                "cyclic module import",
                r#"
                module A { import B; }
                module B { import A; }
                export circuit bad(): [] {}
                "#,
            ),
            (
                "case-insensitive duplicate exported circuit",
                r#"
                export circuit Foo(): [] {}
                export circuit foo(): [] {}
                "#,
            ),
            (
                "non-constant vector index",
                r#"
                export circuit bad(v: Vector<3, Field>, i: Uint<8>): Field {
                  return v[i];
                }
                "#,
            ),
        ];

        for (label, src) in cases {
            let mut sm = SourceMap::new();
            let id = sm.add_file("test.compact", *src);
            let file = sm.get(id);
            let parsed = parse(file);
            assert!(
                !parsed.diagnostics.has_errors(),
                "case `{label}` failed to parse: {:?}",
                parsed.diagnostics
            );
            let checked = check(file, &parsed.ast);
            assert!(
                checked.diagnostics.has_errors(),
                "case `{label}` unexpectedly succeeded without errors"
            );
        }
    }
}
