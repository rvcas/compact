mod pragma;
mod witness;

use std::collections::{HashMap, HashSet};

use compact_ast::{Ast, NodeIndex, NodeTag, TokenIndex, TokenTag};
use compact_diagnostics::{CompactDiagnostic, DiagnosticBag};
use compact_hir::{
    BinaryOp, Circuit, CircuitId, Constructor, EnumDecl, EnumId, Expr, ExprKind, LedgerAdt,
    LedgerField, LedgerFieldId, LedgerOp, LocalId, NewTypeDecl, NewTypeId, Param, ParamId, Program,
    Stmt, StructDecl, StructField, StructId, Type, UnaryOp, WitnessDecl, WitnessId,
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

/// Lower a single-file AST into a type-checked, witness-checked [`Program`].
pub fn check(file: &SourceFile, ast: &Ast) -> CheckResult {
    check_with_loader(file, ast, &NoopLoader)
}

/// Lower an AST (resolving `include "..."` and `import "..."` via `loader`) into a
/// type-checked, witness-checked [`Program`].
pub fn check_with_loader(file: &SourceFile, ast: &Ast, loader: &dyn ModuleLoader) -> CheckResult {
    let mut analyzer = Analyzer {
        units: UnitArena::new(file, ast),
        loader,
        diagnostics: DiagnosticBag::new(),
        include_stack: vec![file.name.clone()],
        scope: ScopeEnv::default(),
        enums: Vec::new(),
        structs: Vec::new(),
        new_types: Vec::new(),
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
        next_mod_instance: 0,
        next_local: 0,
    };
    analyzer.run();

    let mut program = Program {
        enums: analyzer.enums,
        structs: analyzer.structs,
        new_types: analyzer.new_types,
        ledger_fields: analyzer.ledger_fields,
        witnesses: analyzer.witnesses,
        constructor: analyzer.constructor,
        circuits: analyzer.circuits,
        exported_stdlib_types: analyzer.exported_stdlib_types,
    };

    witness::reject_recursive_circuits(file, &program, &mut analyzer.diagnostics);
    propagate_purity(
        file,
        &mut program,
        &analyzer.circuit_sigs,
        &mut analyzer.diagnostics,
    );
    if !analyzer.diagnostics.has_errors() {
        witness::check_witness_disclosure(file, &program, &mut analyzer.diagnostics);
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
}

#[derive(Debug, Clone, Default)]
struct GenericEnv {
    types: HashMap<String, Type>,
    nats: HashMap<String, u32>,
}

#[derive(Debug, Clone, Default)]
struct ScopeEnv {
    enums: HashMap<String, EnumId>,
    structs: HashMap<String, StructId>,
    generic_structs: HashMap<String, usize>,
    type_aliases: HashMap<String, usize>,
    new_types: HashMap<String, NewTypeId>,
    generic_new_types: HashMap<String, usize>,
    ledger_fields: HashMap<String, LedgerFieldId>,
    witnesses: HashMap<String, WitnessId>,
    circuits: HashMap<String, CircuitId>,
    generic_circuits: HashMap<String, usize>,
    modules: HashMap<String, usize>,
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
    ledger_fields: HashMap<String, LedgerFieldId>,
    witnesses: HashMap<String, WitnessId>,
    circuits: HashMap<String, CircuitId>,
    generic_circuits: HashMap<String, usize>,
    modules: HashMap<String, usize>,
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
    next_mod_instance: usize,
    next_local: u32,
}

impl<'a> Analyzer<'a> {
    fn alloc_local(&mut self) -> LocalId {
        let id = LocalId(self.next_local);
        self.next_local += 1;
        id
    }

    fn text(&self, tok: TokenIndex) -> &str {
        self.units.ast().token_text(tok, self.units.file().text())
    }

    fn underlying_type<'b>(&'b self, mut ty: &'b Type) -> &'b Type {
        while let Type::NewType(id) = ty {
            ty = &self.new_types[id.0 as usize].inner;
        }
        ty
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
            if let Some(inner) = self.resolve_type(td.target_type) {
                self.new_types[nid.0 as usize].inner = inner;
            }
            self.units.switch(prev);
        }
        for &(du, decl, sid) in &pending_structs {
            let prev = self.units.switch(du);
            self.populate_struct_fields(decl, sid);
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
                        self.scope.generic_circuits.insert(local_name.clone(), gid);
                        if c.exported {
                            exports.generic_circuits.insert(local_name, gid);
                        }
                        created_generic_circuits.push(gid);
                    } else if let Some((cname, cid, exported)) =
                        self.register_circuit_sig(du, decl, mangle_prefix, is_module_instance)
                    {
                        created_circuits.push(cid.0 as usize);
                        if exported {
                            exports.circuits.insert(cname, cid);
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
            if let Some(&cid) = self.scope.circuits.get(&name) {
                if is_module_instance {
                    exports.circuits.insert(name, cid);
                } else {
                    self.circuit_sigs[cid.0 as usize].exported = true;
                    self.circuit_sigs[cid.0 as usize].name = name;
                }
            } else if let Some(&gid) = self.scope.generic_circuits.get(&name) {
                if is_module_instance {
                    exports.generic_circuits.insert(name, gid);
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
                }
            } else if let Some(&nid) = self.scope.new_types.get(&name) {
                if is_module_instance {
                    exports.new_types.insert(name, nid);
                } else {
                    self.new_types[nid.0 as usize].exported = true;
                    self.new_types[nid.0 as usize].name = name;
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
            self.scope.has_stdlib = true;
            return;
        }

        // Resolve module template: either file import (`import "foo";`) or local module (`import M<...>;`).
        let template = if name_tag == TokenTag::String {
            let spec = unquote_string(&raw_name);
            let from_file = self.units.file().clone();
            match self.loader.load(&from_file, &spec) {
                Ok((mod_file, mod_ast)) => {
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
            for (k, v) in mod_exports.ledger_fields {
                self.scope.ledger_fields.insert(apply_prefix(&k), v);
            }
            for (k, v) in mod_exports.witnesses {
                self.scope.witnesses.insert(apply_prefix(&k), v);
            }
            for (k, v) in mod_exports.circuits {
                self.scope.circuits.insert(apply_prefix(&k), v);
            }
            for (k, v) in mod_exports.generic_circuits {
                self.scope.generic_circuits.insert(apply_prefix(&k), v);
            }
            for (k, v) in mod_exports.modules {
                self.scope.modules.insert(apply_prefix(&k), v);
            }
        } else {
            for (orig, alias, ispan) in selections {
                let target = apply_prefix(&alias);
                let mut found = false;
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
                if let Some(&v) = mod_exports.ledger_fields.get(&orig) {
                    self.scope.ledger_fields.insert(target.clone(), v);
                    found = true;
                }
                if let Some(&v) = mod_exports.witnesses.get(&orig) {
                    self.scope.witnesses.insert(target.clone(), v);
                    found = true;
                }
                if let Some(&v) = mod_exports.circuits.get(&orig) {
                    self.scope.circuits.insert(target.clone(), v);
                    found = true;
                }
                if let Some(&v) = mod_exports.generic_circuits.get(&orig) {
                    self.scope.generic_circuits.insert(target.clone(), v);
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
                let n = self.expect_type_nat(arg_nodes, i, owner, span)?;
                env.nats.insert(gp.name.clone(), n);
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
                let n = self.expect_type_nat(arg_nodes, i, owner, span)?;
                vals.push(GenericArgVal::Nat(n));
                env.nats.insert(gp.name.clone(), n);
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
        let mangled = format!("{}_{}", tmpl.name, self.format_generic_suffix(&vals));
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

        let prev_unit = self.units.switch(tmpl.unit);
        let prev_scope = std::mem::replace(&mut self.scope, inst_scope.clone());

        let params = self.resolve_params(tmpl.params_start, tmpl.params_end);
        let ret_type = self.resolve_type(tmpl.ret_type);

        self.scope = prev_scope;
        self.units.switch(prev_unit);

        let ret_type = ret_type?;
        let cid = CircuitId(self.circuit_sigs.len() as u32);
        let mangled = format!("{}_{}", tmpl.name, self.format_generic_suffix(&vals));
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

    fn resolve_ledger_adt(&mut self, node: NodeIndex) -> Option<LedgerAdt> {
        match self.units.ast().node_tag(node) {
            NodeTag::TypeNamed => {
                let name = self.text(self.units.ast().node_main_token(node)).to_owned();
                if name == "Counter" {
                    return Some(LedgerAdt::Counter);
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
        let path = vec![id.0];
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

        if self.scope.circuits.contains_key(&local_name) {
            self.diagnostics.push(CompactDiagnostic::error(
                self.units.file(),
                name_span,
                format!("duplicate circuit `{local_name}`"),
            ));
            return None;
        }

        let params = self.resolve_params(decl.params_start, decl.params_end);
        let ret_type = self.resolve_type(decl.ret_type)?;

        let id = CircuitId(self.circuit_sigs.len() as u32);
        self.scope.circuits.insert(local_name.clone(), id);
        self.circuit_sigs.push(CircuitSig {
            id,
            unit,
            scope: ScopeEnv::default(),
            name: mangle_name(mangle_prefix, &local_name),
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
                let name = self.text(tok).to_owned();
                if let Some(ty) = self.scope.generics.types.get(&name).cloned() {
                    return Some(ty);
                }
                match name.as_str() {
                    "Field" => Some(Type::Field),
                    "Boolean" => Some(Type::Boolean),
                    "MerkleTreeDigest" => Some(Type::MerkleTreeDigest),
                    "MerkleTreePathEntry" => Some(Type::MerkleTreePathEntry),
                    _ => {
                        if let Some(&eid) = self.scope.enums.get(&name) {
                            Some(Type::Enum(eid))
                        } else if let Some(&sid) = self.scope.structs.get(&name) {
                            Some(Type::Struct(sid))
                        } else if let Some(&nid) = self.scope.new_types.get(&name) {
                            Some(Type::NewType(nid))
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
                let name = self.text(tok).to_owned();
                let span = self.units.ast().node_span(node);
                let data = self.units.ast().node_data(node);
                let arg_nodes: Vec<_> = self.units.ast().extra_nodes(data.lhs, data.rhs).collect();
                match name.as_str() {
                    "Bytes" => {
                        let len = self.expect_type_nat(&arg_nodes, 0, "Bytes", span)?;
                        Some(Type::Bytes(len))
                    }
                    "Uint" => {
                        let bits = self.expect_type_nat(&arg_nodes, 0, "Uint", span)?;
                        Some(Type::Uint(bits))
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
                        let elem = self.resolve_type(arg_nodes[1])?;
                        Some(Type::Vector(len, Box::new(elem)))
                    }
                    "Maybe" => {
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
        match raw.parse::<u32>() {
            Ok(n) => Some(n),
            Err(_) => {
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
            Type::Opaque(ts_ty) => format!("Opaque<\"{ts_ty}\">"),
            Type::Vector(len, elem) => format!("Vector<{len}, {}>", self.format_type(elem)),
            Type::Tuple(elems) => {
                let inner: Vec<_> = elems.iter().map(|e| self.format_type(e)).collect();
                format!("[{}]", inner.join(", "))
            }
            Type::Enum(id) => self.enums[id.0 as usize].name.clone(),
            Type::Struct(id) => self.structs[id.0 as usize].name.clone(),
            Type::NewType(id) => self.new_types[id.0 as usize].name.clone(),
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

    fn check_constructor(&mut self, node: NodeIndex) {
        let decl = self.units.ast().constructor_decl(node);
        let params = self.resolve_params(decl.params_start, decl.params_end);
        let mut scope: HashMap<String, ValueBinding> = HashMap::new();
        for p in &params {
            scope.insert(p.name.clone(), ValueBinding::Param(p.id, p.ty.clone()));
        }
        self.next_local = 0;
        let block_data = self.units.ast().node_data(decl.body);
        let stmt_nodes: Vec<_> = self
            .units
            .ast()
            .extra_nodes(block_data.lhs, block_data.rhs)
            .collect();
        let ret_unit = Type::unit();
        let mut body = Vec::new();
        for snode in stmt_nodes {
            self.check_stmt(snode, &mut scope, &ret_unit, &mut body);
        }
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

        let block_data = self.units.ast().node_data(body_node);
        let stmt_nodes: Vec<_> = self
            .units
            .ast()
            .extra_nodes(block_data.lhs, block_data.rhs)
            .collect();

        let mut body = Vec::new();
        for snode in stmt_nodes {
            self.check_stmt(snode, &mut scope, &ret_type, &mut body);
        }

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

    fn check_stmt_list(
        &mut self,
        node: NodeIndex,
        scope: &HashMap<String, ValueBinding>,
        expected_ret: &Type,
    ) -> Vec<Stmt> {
        let mut inner_scope = scope.clone();
        let mut stmts = Vec::new();
        if self.units.ast().node_tag(node) == NodeTag::Block {
            let block_data = self.units.ast().node_data(node);
            let stmt_nodes: Vec<_> = self
                .units
                .ast()
                .extra_nodes(block_data.lhs, block_data.rhs)
                .collect();
            for snode in stmt_nodes {
                self.check_stmt(snode, &mut inner_scope, expected_ret, &mut stmts);
            }
        } else {
            self.check_stmt(node, &mut inner_scope, expected_ret, &mut stmts);
        }
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
                let local = self.alloc_local();
                let ty = val.ty.clone();
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
                        if tys.len() != elems.len() {
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
                        tys
                    }
                    Type::Vector(len, ety) => {
                        if len as usize != elems.len() {
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
                let Some(start) = eval_const_u128(&start_expr) else {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        start_expr.span,
                        "`for` range lower bound must be a compile-time integer constant",
                    ));
                    return;
                };
                let Some(end) = eval_const_u128(&end_expr) else {
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
                let (len, elem_ty) = match &iter.ty {
                    Type::Vector(len, elem) => (*len, (**elem).clone()),
                    Type::Tuple(elems)
                        if !elems.is_empty() && elems.iter().all(|t| *t == elems[0]) =>
                    {
                        (elems.len() as u32, elems[0].clone())
                    }
                    other => {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            iter.span,
                            format!(
                                "`for` loop iterable must be a `Vector`, found `{}`",
                                self.format_type(other)
                            ),
                        ));
                        return;
                    }
                };
                let local = self.alloc_local();
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

    fn coerce_or_check(&self, expr: &mut Expr, expected: &Type) -> bool {
        if expr.ty == *expected {
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
                ExprKind::Block { tail, .. } => {
                    if self.coerce_or_check(tail, expected) {
                        expr.ty = expected.clone();
                        return true;
                    }
                }
                _ => {}
            }
        }
        false
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
                let val: u128 = match raw.parse() {
                    Ok(v) => v,
                    Err(_) => {
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
                let bytes = unquote_string(self.text(tok)).into_bytes();
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
                let index = self.check_expr(idx_expr.index, scope, Some(&Type::Uint(64)))?;
                let base_underlying = self.underlying_type(&base.ty).clone();
                match base_underlying {
                    Type::Vector(len, elem) => {
                        if let Some(k) = eval_const_u128(&index) {
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
                        } else if !matches!(self.underlying_type(&index.ty), Type::Uint(_)) {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                index.span,
                                format!(
                                    "vector index must be a `Uint`, found `{}`",
                                    self.format_type(&index.ty)
                                ),
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
                    Type::Tuple(elems) => {
                        let Some(k) = eval_const_u128(&index) else {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                index.span,
                                "tuple index must be a compile-time integer constant",
                            ));
                            return None;
                        };
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
                    }
                    other => {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            span,
                            format!(
                                "cannot index into type `{}` (expected `Vector` or tuple)",
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
                    let sf = self.units.ast().struct_lit_field(fnode);
                    let fname = self.text(sf.name_token).to_owned();
                    let Some((_, expected_ty)) = expected_fields.iter().find(|(n, _)| *n == fname)
                    else {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.units.file(),
                            self.units.ast().token_span(sf.name_token),
                            format!("struct `{}` has no field `{fname}`", self.format_type(&ty)),
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
                    for enode in elem_nodes {
                        if self.units.ast().node_tag(enode) == NodeTag::SpreadExpr {
                            let sdata = self.units.ast().node_data(enode);
                            let inner = self.check_expr(NodeIndex(sdata.lhs), scope, None)?;
                            let inner_span = inner.span;
                            let inner_ty = inner.ty.clone();
                            let inner_u = self.underlying_type(&inner_ty).clone();
                            let spread_tys: Vec<Type> = match inner_u {
                                Type::Vector(k, ety) => vec![(*ety).clone(); k as usize],
                                Type::Tuple(etys) => etys,
                                other => {
                                    self.diagnostics.push(CompactDiagnostic::error(
                                        self.units.file(),
                                        inner_span,
                                        format!(
                                            "cannot spread type `{}` inside `[...]`; expected `Vector` or tuple",
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
                    let ty = Type::Tuple(tys);
                    return Some(Expr {
                        kind: ExprKind::Block {
                            stmts: prelude,
                            tail: Box::new(Expr {
                                kind: ExprKind::Tuple(flat),
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
                        if operand.ty != Type::Field {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.units.file(),
                                operand.span,
                                format!(
                                    "unary `-` expects `Field`, found `{}`",
                                    self.format_type(&operand.ty)
                                ),
                            ));
                            return None;
                        }
                        Some(Expr {
                            kind: ExprKind::Unary {
                                op: UnaryOp::Neg,
                                operand: Box::new(operand),
                            },
                            ty: Type::Field,
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
                    if let (Type::Uint(a), Type::Uint(b)) = (&lhs.ty, &rhs.ty) {
                        let widened = Type::Uint((*a).max(*b));
                        lhs.ty = widened.clone();
                        rhs.ty = widened;
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
                if matches!(
                    op,
                    BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge
                ) && !matches!(lhs.ty, Type::Uint(_))
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
                if cond.ty != Type::Boolean {
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
                let inner = self.check_expr(NodeIndex(data.lhs), scope, None)?;
                let src_u = self.underlying_type(&inner.ty);
                let dst_u = self.underlying_type(&target);
                let valid = inner.ty == target
                    || src_u == dst_u
                    || matches!(
                        (src_u, dst_u),
                        (Type::Uint(_), Type::Field)
                            | (Type::Uint(_), Type::Uint(_))
                            | (Type::Boolean, Type::Field)
                            | (Type::Enum(_), Type::Field)
                            | (Type::Field, Type::Field)
                    )
                    || matches!(
                        (src_u, dst_u),
                        (Type::Bytes(n), Type::Field) if *n <= 31
                    )
                    || matches!(
                        (src_u, dst_u),
                        (Type::Bytes(n), Type::Vector(m, elem))
                            if n == m && *self.underlying_type(elem) == Type::Uint(8)
                    )
                    || matches!(
                        (src_u, dst_u),
                        (Type::Vector(n, elem), Type::Bytes(m))
                            if n == m && *self.underlying_type(elem) == Type::Uint(8)
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
                    if let Some(&gid) = self.scope.generic_circuits.get(&callee_name) {
                        let cid = self.instantiate_generic_circuit(gid, &targ_nodes, span)?;
                        return self.check_circuit_call(cid, &arg_nodes, span, scope);
                    }
                    return self.check_generic_builtin(
                        &callee_name,
                        self.units.ast().token_span(callee_tok),
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
                    let callee_name = self.text(callee_tok).to_owned();
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
                        _ => {}
                    }
                    if let Some(&cid) = self.scope.circuits.get(&callee_name) {
                        return self.check_circuit_call(cid, &arg_nodes, span, scope);
                    }
                    if let Some(&wid) = self.scope.witnesses.get(&callee_name) {
                        return self.check_witness_call(wid, &arg_nodes, span, scope);
                    }
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        self.units.ast().token_span(callee_tok),
                        format!("unknown circuit or witness `{callee_name}`"),
                    ));
                    return None;
                }

                // 2. Ledger ADT method call (supporting arbitrary nested `map.lookup(k)...method(...)`).
                if self.units.ast().node_tag(call.callee) == NodeTag::MemberExpr {
                    let mdata = self.units.ast().node_data(call.callee);
                    let recv = NodeIndex(mdata.lhs);
                    let method_tok = TokenIndex(mdata.rhs);
                    if let Some((field_id, key_path, target_adt)) =
                        self.try_extract_ledger_chain(recv, scope)
                    {
                        let method_name = self.text(method_tok).to_owned();
                        return self.check_ledger_call(
                            field_id,
                            key_path,
                            target_adt,
                            &method_name,
                            self.units.ast().token_span(method_tok),
                            &arg_nodes,
                            span,
                            scope,
                        );
                    }
                }

                self.diagnostics.push(CompactDiagnostic::error(
                    self.units.file(),
                    span,
                    "unsupported call target",
                ));
                None
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
        let len: u32 = match self
            .text(self.units.ast().node_main_token(arg_nodes[0]))
            .parse()
        {
            Ok(n) => n,
            Err(_) => {
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
        let text = unquote_string(self.text(self.units.ast().node_main_token(arg_nodes[1])));
        let raw_bytes = text.as_bytes();
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
        padded[..raw_bytes.len()].copy_from_slice(raw_bytes);
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
                let name = self.text(tok).to_owned();
                let Some(&cid) = self.scope.circuits.get(&name) else {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.units.file(),
                        self.units.ast().token_span(tok),
                        format!("unknown circuit `{name}` passed to higher-order builtin"),
                    ));
                    return None;
                };
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
                    for (i, snode) in stmt_nodes.iter().copied().enumerate() {
                        if self.units.ast().node_tag(snode) == NodeTag::ReturnStmt
                            && i + 1 == stmt_nodes.len()
                        {
                            let rdata = self.units.ast().node_data(snode);
                            if let Some(enode) = NodeIndex(rdata.lhs).into_option() {
                                let mut expr =
                                    self.check_expr(enode, &inner_scope, annotated_ret.as_ref())?;
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
                                        return None;
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
            Type::Tuple(elems) if !elems.is_empty() && elems.iter().all(|t| *t == elems[0]) => {
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
                        "`{builtin}` vector argument must have `Vector<N, T>` type, found `{}`",
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
                let Some(start_u128) = eval_const_u128(&start_expr) else {
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
                let name = self.text(self.units.ast().node_main_token(node));
                let &field_id = self.scope.ledger_fields.get(name)?;
                Some((
                    field_id,
                    Vec::new(),
                    self.ledger_fields[field_id.0 as usize].adt.clone(),
                ))
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
                let mut args = Vec::with_capacity(arg_nodes.len());
                for &anode in arg_nodes {
                    let mut arg = self.check_expr(anode, scope, Some(&Type::Uint(16)))?;
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
                    } else if self.units.ast().node_tag(arg_nodes[1]) == NodeTag::DefaultExpr {
                        let inner_ty = NodeIndex(self.units.ast().node_data(arg_nodes[1]).lhs);
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
                    };
                    make_call(LedgerOp::MapInsert, vec![k, v], Type::unit(), target_adt)
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
    if raw.len() >= 2 {
        raw[1..raw.len() - 1].to_owned()
    } else {
        raw.to_owned()
    }
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
        ExprKind::WitnessCall { args, .. } => {
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
        | ExprKind::TransientHash { arg: operand, .. }
        | ExprKind::DegradeToTransient(operand)
        | ExprKind::UpgradeFromTransient(operand)
        | ExprKind::MerkleTreePathRoot { path: operand, .. }
        | ExprKind::FieldAccess { base: operand, .. }
        | ExprKind::Slice { base: operand, .. }
        | ExprKind::MaybeSome(operand) => expr_effects(operand, calls),
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
}
