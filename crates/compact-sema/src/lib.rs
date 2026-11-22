mod witness;

use std::collections::HashMap;

use compact_ast::{Ast, NodeIndex, NodeTag, TokenIndex, TokenTag};
use compact_diagnostics::{CompactDiagnostic, DiagnosticBag};
use compact_hir::{
    BinaryOp, Circuit, CircuitId, Constructor, EnumDecl, EnumId, Expr, ExprKind, LedgerAdt,
    LedgerField, LedgerFieldId, LedgerOp, LocalId, Param, ParamId, Program, Stmt, StructDecl,
    StructField, StructId, Type, UnaryOp, WitnessDecl, WitnessId,
};
use compact_span::{SourceFile, Span};

pub struct CheckResult {
    pub program: Program,
    pub diagnostics: DiagnosticBag,
}

/// Lower an AST into a type-checked, witness-checked [`Program`].
pub fn check(file: &SourceFile, ast: &Ast) -> CheckResult {
    let mut analyzer = Analyzer {
        file,
        ast,
        diagnostics: DiagnosticBag::new(),
        has_stdlib: false,
        enums: Vec::new(),
        enum_by_name: HashMap::new(),
        structs: Vec::new(),
        struct_by_name: HashMap::new(),
        ledger_fields: Vec::new(),
        ledger_by_name: HashMap::new(),
        witnesses: Vec::new(),
        witness_by_name: HashMap::new(),
        constructor_node: None,
        constructor: None,
        circuit_sigs: Vec::new(),
        circuit_by_name: HashMap::new(),
        circuits: Vec::new(),
        export_list_tokens: Vec::new(),
        exported_stdlib_types: Vec::new(),
    };
    analyzer.run();

    let mut program = Program {
        enums: analyzer.enums,
        structs: analyzer.structs,
        ledger_fields: analyzer.ledger_fields,
        witnesses: analyzer.witnesses,
        constructor: analyzer.constructor,
        circuits: analyzer.circuits,
        exported_stdlib_types: analyzer.exported_stdlib_types,
    };

    witness::reject_recursive_circuits(file, &program, &mut analyzer.diagnostics);
    propagate_purity(file, &mut program, &analyzer.circuit_sigs, &mut analyzer.diagnostics);
    if !analyzer.diagnostics.has_errors() {
        witness::check_witness_disclosure(file, &program, &mut analyzer.diagnostics);
    }

    CheckResult {
        program,
        diagnostics: analyzer.diagnostics,
    }
}

struct CircuitSig {
    id: CircuitId,
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
    file: &'a SourceFile,
    ast: &'a Ast,
    diagnostics: DiagnosticBag,
    has_stdlib: bool,
    enums: Vec<EnumDecl>,
    enum_by_name: HashMap<String, EnumId>,
    structs: Vec<StructDecl>,
    struct_by_name: HashMap<String, StructId>,
    ledger_fields: Vec<LedgerField>,
    ledger_by_name: HashMap<String, LedgerFieldId>,
    witnesses: Vec<WitnessDecl>,
    witness_by_name: HashMap<String, WitnessId>,
    constructor_node: Option<NodeIndex>,
    constructor: Option<Constructor>,
    circuit_sigs: Vec<CircuitSig>,
    circuit_by_name: HashMap<String, CircuitId>,
    circuits: Vec<Circuit>,
    export_list_tokens: Vec<TokenIndex>,
    exported_stdlib_types: Vec<String>,
}

impl<'a> Analyzer<'a> {
    fn text(&self, tok: TokenIndex) -> &'a str {
        self.ast.token_text(tok, self.file.text())
    }

    fn run(&mut self) {
        let decls: Vec<_> = self.ast.root_decls().collect();

        // Pass 1a: imports, export lists, and enums.
        for &decl in &decls {
            match self.ast.node_tag(decl) {
                NodeTag::ImportDecl => {
                    let import = self.ast.import_decl(decl);
                    let name = self.text(import.name_token);
                    if name == "CompactStandardLibrary" {
                        self.has_stdlib = true;
                    } else {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            self.ast.token_span(import.name_token),
                            format!("unknown module `{name}`"),
                        ));
                    }
                }
                NodeTag::ExportListDecl => {
                    let list = self.ast.export_list_decl(decl);
                    self.export_list_tokens
                        .extend(self.ast.extra_tokens(list.names_start, list.names_end));
                }
                NodeTag::EnumDecl => self.register_enum(decl),
                NodeTag::StructDecl => self.register_struct_name(decl),
                _ => {}
            }
        }

        // Pass 1a.5: resolve struct field types (allowing structs to reference earlier or later structs).
        for &decl in &decls {
            if self.ast.node_tag(decl) == NodeTag::StructDecl {
                self.populate_struct_fields(decl);
            }
        }

        // Pass 1b: ledger declarations, witnesses, constructor, and circuit signatures.
        for &decl in &decls {
            match self.ast.node_tag(decl) {
                NodeTag::LedgerDecl => self.register_ledger(decl),
                NodeTag::WitnessDecl => self.register_witness(decl),
                NodeTag::ConstructorDecl => {
                    if self.constructor_node.is_some() {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            self.ast.node_span(decl),
                            "duplicate `constructor` declaration",
                        ));
                    } else {
                        self.constructor_node = Some(decl);
                    }
                }
                NodeTag::CircuitDecl => self.register_circuit_sig(decl),
                _ => {}
            }
        }

        // Apply standalone `export { ... }` lists.
        let export_tokens = std::mem::take(&mut self.export_list_tokens);
        for tok in export_tokens {
            let name = self.text(tok);
            if let Some(&cid) = self.circuit_by_name.get(name) {
                self.circuit_sigs[cid.0 as usize].exported = true;
            } else if let Some(&eid) = self.enum_by_name.get(name) {
                self.enums[eid.0 as usize].exported = true;
            } else if let Some(&sid) = self.struct_by_name.get(name) {
                self.structs[sid.0 as usize].exported = true;
            } else if let Some(&fid) = self.ledger_by_name.get(name) {
                self.ledger_fields[fid.0 as usize].exported = true;
            } else if let Some(&wid) = self.witness_by_name.get(name) {
                self.witnesses[wid.0 as usize].exported = true;
            } else if self.has_stdlib
                && matches!(
                    name,
                    "Maybe" | "MerkleTreeDigest" | "MerkleTreePathEntry" | "MerkleTreePath"
                )
            {
                if !self.exported_stdlib_types.iter().any(|s| s == name) {
                    self.exported_stdlib_types.push(name.to_owned());
                }
            } else {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    self.ast.token_span(tok),
                    format!("cannot export unknown item `{name}`"),
                ));
            }
        }

        // Pass 2: type-check constructor & circuit bodies.
        if let Some(ctor_node) = self.constructor_node {
            self.check_constructor(ctor_node);
        }
        for sig_idx in 0..self.circuit_sigs.len() {
            self.check_circuit_body(sig_idx);
        }
    }

    fn register_enum(&mut self, node: NodeIndex) {
        let decl = self.ast.enum_decl(node);
        let name = self.text(decl.name_token).to_owned();
        let name_span = self.ast.token_span(decl.name_token);
        if self.enum_by_name.contains_key(&name) {
            self.diagnostics.push(CompactDiagnostic::error(
                self.file,
                name_span,
                format!("duplicate enum `{name}`"),
            ));
            return;
        }
        let mut variants = Vec::new();
        for vtok in self.ast.extra_tokens(decl.variants_start, decl.variants_end) {
            let vname = self.text(vtok).to_owned();
            if variants.contains(&vname) {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    self.ast.token_span(vtok),
                    format!("duplicate variant `{vname}` in enum `{name}`"),
                ));
                continue;
            }
            variants.push(vname);
        }
        if variants.is_empty() {
            self.diagnostics.push(CompactDiagnostic::error(
                self.file,
                name_span,
                format!("enum `{name}` must declare at least one variant"),
            ));
            return;
        }
        let id = EnumId(self.enums.len() as u32);
        self.enums.push(EnumDecl {
            id,
            name: name.clone(),
            variants,
            exported: decl.exported,
            span: self.ast.node_span(node),
        });
        self.enum_by_name.insert(name, id);
    }

    fn register_struct_name(&mut self, node: NodeIndex) {
        let decl = self.ast.struct_decl(node);
        let name = self.text(decl.name_token).to_owned();
        let name_span = self.ast.token_span(decl.name_token);
        if self.struct_by_name.contains_key(&name) || self.enum_by_name.contains_key(&name) {
            self.diagnostics.push(CompactDiagnostic::error(
                self.file,
                name_span,
                format!("duplicate type `{name}`"),
            ));
            return;
        }
        let id = StructId(self.structs.len() as u32);
        self.structs.push(StructDecl {
            id,
            name: name.clone(),
            fields: Vec::new(),
            exported: decl.exported,
            span: self.ast.node_span(node),
        });
        self.struct_by_name.insert(name, id);
    }

    fn populate_struct_fields(&mut self, node: NodeIndex) {
        let decl = self.ast.struct_decl(node);
        let name = self.text(decl.name_token);
        let Some(&sid) = self.struct_by_name.get(name) else {
            return;
        };
        let field_nodes: Vec<_> = self
            .ast
            .extra_nodes(decl.fields_start, decl.fields_end)
            .collect();
        let mut fields = Vec::with_capacity(field_nodes.len());
        let mut seen = HashMap::new();
        for fnode in field_nodes {
            let sf = self.ast.struct_field(fnode);
            let fname = self.text(sf.name_token).to_owned();
            if seen.contains_key(&fname) {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    self.ast.token_span(sf.name_token),
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
                span: self.ast.node_span(fnode),
            });
        }
        self.structs[sid.0 as usize].fields = fields;
    }

    fn register_ledger(&mut self, node: NodeIndex) {
        let decl = self.ast.ledger_decl(node);
        let name = self.text(decl.name_token).to_owned();
        let name_span = self.ast.token_span(decl.name_token);

        if self.ledger_by_name.contains_key(&name) {
            self.diagnostics.push(CompactDiagnostic::error(
                self.file,
                name_span,
                format!("duplicate ledger field `{name}`"),
            ));
            return;
        }

        let (adt, value_type) = match self.ast.node_tag(decl.type_node) {
            NodeTag::TypeNamed
                if self.text(self.ast.node_main_token(decl.type_node)) == "Counter" =>
            {
                (LedgerAdt::Counter, Type::Uint(64))
            }
            NodeTag::TypeGeneric
                if self.text(self.ast.node_main_token(decl.type_node)) == "Set" =>
            {
                let data = self.ast.node_data(decl.type_node);
                let arg_nodes: Vec<_> = self.ast.extra_nodes(data.lhs, data.rhs).collect();
                if arg_nodes.len() != 1 {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        self.ast.node_span(decl.type_node),
                        format!("`Set` expects 1 type argument, found {}", arg_nodes.len()),
                    ));
                    return;
                }
                let Some(elem_ty) = self.resolve_type(arg_nodes[0]) else {
                    return;
                };
                (LedgerAdt::Set, elem_ty)
            }
            NodeTag::TypeGeneric
                if self.text(self.ast.node_main_token(decl.type_node)) == "MerkleTree" =>
            {
                let data = self.ast.node_data(decl.type_node);
                let arg_nodes: Vec<_> = self.ast.extra_nodes(data.lhs, data.rhs).collect();
                if arg_nodes.len() != 2 {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        self.ast.node_span(decl.type_node),
                        format!(
                            "`MerkleTree` expects 2 type arguments (depth, element type), found {}",
                            arg_nodes.len()
                        ),
                    ));
                    return;
                }
                let Some(depth) = self.expect_type_nat(
                    &arg_nodes,
                    0,
                    "MerkleTree",
                    self.ast.node_span(decl.type_node),
                ) else {
                    return;
                };
                let Some(elem_ty) = self.resolve_type(arg_nodes[1]) else {
                    return;
                };
                (LedgerAdt::MerkleTree(depth), elem_ty)
            }
            _ => {
                let Some(ty) = self.resolve_type(decl.type_node) else {
                    return;
                };
                (LedgerAdt::Cell, ty)
            }
        };

        let id = LedgerFieldId(self.ledger_fields.len() as u32);
        let path = vec![id.0];
        self.ledger_fields.push(LedgerField {
            id,
            name: name.clone(),
            adt,
            value_type,
            path,
            exported: decl.exported,
            sealed: decl.sealed,
            span: self.ast.node_span(node),
        });
        self.ledger_by_name.insert(name, id);
    }

    fn register_witness(&mut self, node: NodeIndex) {
        let decl = self.ast.witness_decl(node);
        let name = self.text(decl.name_token).to_owned();
        let name_span = self.ast.token_span(decl.name_token);

        if self.witness_by_name.contains_key(&name) {
            self.diagnostics.push(CompactDiagnostic::error(
                self.file,
                name_span,
                format!("duplicate witness `{name}`"),
            ));
            return;
        }

        let params = self.resolve_params(decl.params_start, decl.params_end);
        let Some(ret_type) = self.resolve_type(decl.ret_type) else {
            return;
        };

        let id = WitnessId(self.witnesses.len() as u32);
        self.witness_by_name.insert(name.clone(), id);
        self.witnesses.push(WitnessDecl {
            id,
            name,
            params,
            ret_type,
            exported: decl.exported,
            span: self.ast.node_span(node),
        });
    }

    fn register_circuit_sig(&mut self, node: NodeIndex) {
        let decl = self.ast.circuit_decl(node);
        let name = self.text(decl.name_token).to_owned();
        let name_span = self.ast.token_span(decl.name_token);

        if self.circuit_by_name.contains_key(&name) {
            self.diagnostics.push(CompactDiagnostic::error(
                self.file,
                name_span,
                format!("duplicate circuit `{name}`"),
            ));
            return;
        }

        let params = self.resolve_params(decl.params_start, decl.params_end);
        let Some(ret_type) = self.resolve_type(decl.ret_type) else {
            return;
        };

        let id = CircuitId(self.circuit_sigs.len() as u32);
        self.circuit_by_name.insert(name.clone(), id);
        self.circuit_sigs.push(CircuitSig {
            id,
            name,
            name_span,
            params,
            ret_type,
            body_node: decl.body,
            exported: decl.exported,
            declared_pure: decl.pure,
            span: self.ast.node_span(node),
        });
    }

    fn resolve_params(&mut self, start: u32, end: u32) -> Vec<Param> {
        let mut params = Vec::new();
        let mut seen = HashMap::new();
        let param_nodes: Vec<_> = self.ast.extra_nodes(start, end).collect();
        for pnode in param_nodes {
            let p = self.ast.param(pnode);
            let pname = self.text(p.name_token).to_owned();
            if seen.contains_key(&pname) {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    self.ast.token_span(p.name_token),
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
                span: self.ast.node_span(pnode),
            });
        }
        params
    }

    fn resolve_type(&mut self, node: NodeIndex) -> Option<Type> {
        match self.ast.node_tag(node) {
            NodeTag::TypeNamed => {
                let tok = self.ast.node_main_token(node);
                let name = self.text(tok);
                match name {
                    "Field" => Some(Type::Field),
                    "Boolean" => Some(Type::Boolean),
                    "MerkleTreeDigest" => Some(Type::MerkleTreeDigest),
                    "MerkleTreePathEntry" => Some(Type::MerkleTreePathEntry),
                    _ => {
                        if let Some(&eid) = self.enum_by_name.get(name) {
                            Some(Type::Enum(eid))
                        } else if let Some(&sid) = self.struct_by_name.get(name) {
                            Some(Type::Struct(sid))
                        } else {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.file,
                                self.ast.token_span(tok),
                                format!("unknown type `{name}`"),
                            ));
                            None
                        }
                    }
                }
            }
            NodeTag::TypeGeneric => {
                let tok = self.ast.node_main_token(node);
                let name = self.text(tok);
                let data = self.ast.node_data(node);
                let arg_nodes: Vec<_> = self.ast.extra_nodes(data.lhs, data.rhs).collect();
                match name {
                    "Bytes" => {
                        let len = self.expect_type_nat(&arg_nodes, 0, "Bytes", self.ast.node_span(node))?;
                        Some(Type::Bytes(len))
                    }
                    "Uint" => {
                        let bits = self.expect_type_nat(&arg_nodes, 0, "Uint", self.ast.node_span(node))?;
                        Some(Type::Uint(bits))
                    }
                    "Opaque" => {
                        if arg_nodes.len() != 1
                            || self.ast.node_tag(arg_nodes[0]) != NodeTag::TypeString
                        {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.file,
                                self.ast.node_span(node),
                                "`Opaque` expects 1 string literal type argument (e.g. `Opaque<\"string\">`)",
                            ));
                            return None;
                        }
                        let ts_ty =
                            unquote_string(self.text(self.ast.node_main_token(arg_nodes[0])));
                        Some(Type::Opaque(ts_ty))
                    }
                    "Vector" => {
                        if arg_nodes.len() != 2 {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.file,
                                self.ast.node_span(node),
                                format!("`Vector` expects 2 type arguments, found {}", arg_nodes.len()),
                            ));
                            return None;
                        }
                        let len = self.expect_type_nat(&arg_nodes, 0, "Vector", self.ast.node_span(node))?;
                        let elem = self.resolve_type(arg_nodes[1])?;
                        Some(Type::Vector(len, Box::new(elem)))
                    }
                    "Maybe" => {
                        if arg_nodes.len() != 1 {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.file,
                                self.ast.node_span(node),
                                format!("`Maybe` expects 1 type argument, found {}", arg_nodes.len()),
                            ));
                            return None;
                        }
                        let inner = self.resolve_type(arg_nodes[0])?;
                        Some(Type::Maybe(Box::new(inner)))
                    }
                    "MerkleTreePath" => {
                        if arg_nodes.len() != 2 {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.file,
                                self.ast.node_span(node),
                                format!(
                                    "`MerkleTreePath` expects 2 type arguments, found {}",
                                    arg_nodes.len()
                                ),
                            ));
                            return None;
                        }
                        let depth = self.expect_type_nat(
                            &arg_nodes,
                            0,
                            "MerkleTreePath",
                            self.ast.node_span(node),
                        )?;
                        let leaf = self.resolve_type(arg_nodes[1])?;
                        Some(Type::MerkleTreePath(depth, Box::new(leaf)))
                    }
                    other => {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            self.ast.token_span(tok),
                            format!("unknown generic type `{other}`"),
                        ));
                        None
                    }
                }
            }
            NodeTag::TypeTuple => {
                let data = self.ast.node_data(node);
                let elem_nodes: Vec<_> = self.ast.extra_nodes(data.lhs, data.rhs).collect();
                let mut elems = Vec::with_capacity(elem_nodes.len());
                for enode in elem_nodes {
                    elems.push(self.resolve_type(enode)?);
                }
                Some(Type::Tuple(elems))
            }
            _ => None,
        }
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
                self.file,
                span,
                format!("`{type_name}` is missing a numeric size argument"),
            ));
            return None;
        };
        if self.ast.node_tag(arg) != NodeTag::TypeNat {
            self.diagnostics.push(CompactDiagnostic::error(
                self.file,
                self.ast.node_span(arg),
                format!("`{type_name}` size argument must be a numeric literal"),
            ));
            return None;
        }
        let raw = self.text(self.ast.node_main_token(arg));
        match raw.parse::<u32>() {
            Ok(n) => Some(n),
            Err(_) => {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    self.ast.node_span(arg),
                    format!("invalid numeric size `{raw}`"),
                ));
                None
            }
        }
    }

    fn struct_fields_of(&self, ty: &Type) -> Option<Vec<(String, Type)>> {
        match ty {
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
            Type::Maybe(inner) => format!("Maybe<{}>", self.format_type(inner)),
            Type::MerkleTreeDigest => "MerkleTreeDigest".into(),
            Type::MerkleTreePathEntry => "MerkleTreePathEntry".into(),
            Type::MerkleTreePath(depth, leaf) => {
                format!("MerkleTreePath<{depth}, {}>", self.format_type(leaf))
            }
        }
    }

    fn check_constructor(&mut self, node: NodeIndex) {
        let decl = self.ast.constructor_decl(node);
        let params = self.resolve_params(decl.params_start, decl.params_end);
        let mut scope: HashMap<String, ValueBinding> = HashMap::new();
        for p in &params {
            scope.insert(p.name.clone(), ValueBinding::Param(p.id, p.ty.clone()));
        }
        let mut next_local: u32 = 0;
        let block_data = self.ast.node_data(decl.body);
        let stmt_nodes: Vec<_> = self
            .ast
            .extra_nodes(block_data.lhs, block_data.rhs)
            .collect();
        let ret_unit = Type::unit();
        let mut body = Vec::new();
        for snode in stmt_nodes {
            if let Some(stmt) = self.check_stmt(snode, &mut scope, &mut next_local, &ret_unit) {
                body.push(stmt);
            }
        }
        self.constructor = Some(Constructor {
            params,
            body,
            span: self.ast.node_span(node),
        });
    }

    fn check_circuit_body(&mut self, sig_idx: usize) {
        let id = self.circuit_sigs[sig_idx].id;
        let name = self.circuit_sigs[sig_idx].name.clone();
        let params = self.circuit_sigs[sig_idx].params.clone();
        let ret_type = self.circuit_sigs[sig_idx].ret_type.clone();
        let body_node = self.circuit_sigs[sig_idx].body_node;
        let exported = self.circuit_sigs[sig_idx].exported;
        let span = self.circuit_sigs[sig_idx].span;

        let mut scope: HashMap<String, ValueBinding> = HashMap::new();
        for p in &params {
            scope.insert(p.name.clone(), ValueBinding::Param(p.id, p.ty.clone()));
        }
        let mut next_local: u32 = 0;

        let block_data = self.ast.node_data(body_node);
        let stmt_nodes: Vec<_> = self
            .ast
            .extra_nodes(block_data.lhs, block_data.rhs)
            .collect();

        let mut body = Vec::new();
        for snode in stmt_nodes {
            if let Some(stmt) = self.check_stmt(snode, &mut scope, &mut next_local, &ret_type) {
                body.push(stmt);
            }
        }

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
        next_local: &mut u32,
        expected_ret: &Type,
    ) -> Vec<Stmt> {
        let mut inner_scope = scope.clone();
        if self.ast.node_tag(node) == NodeTag::Block {
            let block_data = self.ast.node_data(node);
            let stmt_nodes: Vec<_> = self
                .ast
                .extra_nodes(block_data.lhs, block_data.rhs)
                .collect();
            let mut stmts = Vec::new();
            for snode in stmt_nodes {
                if let Some(stmt) =
                    self.check_stmt(snode, &mut inner_scope, next_local, expected_ret)
                {
                    stmts.push(stmt);
                }
            }
            stmts
        } else if let Some(stmt) = self.check_stmt(node, &mut inner_scope, next_local, expected_ret)
        {
            vec![stmt]
        } else {
            Vec::new()
        }
    }

    fn check_stmt(
        &mut self,
        node: NodeIndex,
        scope: &mut HashMap<String, ValueBinding>,
        next_local: &mut u32,
        expected_ret: &Type,
    ) -> Option<Stmt> {
        let data = self.ast.node_data(node);
        match self.ast.node_tag(node) {
            NodeTag::IfStmt => {
                let stmt = self.ast.if_stmt(node);
                let cond = self.check_expr(stmt.cond, scope, Some(&Type::Boolean))?;
                if cond.ty != Type::Boolean {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        cond.span,
                        format!(
                            "`if` condition must be `Boolean`, found `{}`",
                            self.format_type(&cond.ty)
                        ),
                    ));
                    return None;
                }
                let then_branch =
                    self.check_stmt_list(stmt.then_branch, scope, next_local, expected_ret);
                let else_branch = match stmt.else_branch {
                    Some(eb) => self.check_stmt_list(eb, scope, next_local, expected_ret),
                    None => Vec::new(),
                };
                Some(Stmt::If {
                    cond,
                    then_branch,
                    else_branch,
                    span: self.ast.node_span(node),
                })
            }
            NodeTag::ConstStmt => {
                let stmt = self.ast.const_stmt(node);
                let name = self.text(stmt.name_token).to_owned();
                let annotated = match stmt.ty {
                    Some(ty_node) => Some(self.resolve_type(ty_node)?),
                    None => None,
                };
                let mut init = self.check_expr(stmt.init, scope, annotated.as_ref())?;
                let ty = if let Some(ann) = annotated {
                    if !self.coerce_or_check(&mut init, &ann) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            init.span,
                            format!(
                                "type mismatch in `const {name}`: expected `{}`, found `{}`",
                                self.format_type(&ann),
                                self.format_type(&init.ty)
                            ),
                        ));
                    }
                    ann
                } else {
                    init.ty.clone()
                };
                let local = LocalId(*next_local);
                *next_local += 1;
                scope.insert(name.clone(), ValueBinding::Local(local, ty.clone()));
                Some(Stmt::Const {
                    local,
                    name,
                    ty,
                    init,
                    span: self.ast.node_span(node),
                })
            }
            NodeTag::AssignStmt => {
                let stmt = self.ast.assign_stmt(node);
                let assign_span = self.ast.node_span(node);
                if self.ast.node_tag(stmt.lhs) != NodeTag::IdentExpr {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        self.ast.node_span(stmt.lhs),
                        "left-hand side of assignment must be a ledger field",
                    ));
                    return None;
                }
                let lhs_tok = self.ast.node_main_token(stmt.lhs);
                let field_name = self.text(lhs_tok);
                let Some(&field_id) = self.ledger_by_name.get(field_name) else {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        self.ast.token_span(lhs_tok),
                        format!("cannot assign to `{field_name}`: not a ledger field"),
                    ));
                    return None;
                };
                let field = &self.ledger_fields[field_id.0 as usize];
                if field.adt != LedgerAdt::Cell {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        assign_span,
                        format!(
                            "cannot directly assign to ledger `{field_name}` of ADT type `{}`; use its methods instead",
                            field.adt.name()
                        ),
                    ));
                    return None;
                }
                let expected_val_ty = field.value_type.clone();
                let mut rhs = self.check_expr(stmt.rhs, scope, Some(&expected_val_ty))?;
                if !self.coerce_or_check(&mut rhs, &expected_val_ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        rhs.span,
                        format!(
                            "cannot assign `{}` to ledger field `{field_name}` of type `{}`",
                            self.format_type(&rhs.ty),
                            self.format_type(&expected_val_ty)
                        ),
                    ));
                    return None;
                }
                Some(Stmt::Expr(Expr {
                    kind: ExprKind::LedgerCall {
                        field: field_id,
                        op: LedgerOp::CellWrite,
                        args: vec![rhs],
                    },
                    ty: Type::unit(),
                    span: assign_span,
                }))
            }
            NodeTag::ExprStmt => {
                let expr = self.check_expr(NodeIndex(data.lhs), scope, None)?;
                Some(Stmt::Expr(expr))
            }
            NodeTag::ReturnStmt => {
                let span = self.ast.node_span(node);
                let value = if let Some(expr_node) = NodeIndex(data.lhs).into_option() {
                    let mut expr = self.check_expr(expr_node, scope, Some(expected_ret))?;
                    if !self.coerce_or_check(&mut expr, expected_ret) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
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
                            self.file,
                            span,
                            format!(
                                "empty `return` in circuit returning `{}`",
                                self.format_type(expected_ret)
                            ),
                        ));
                    }
                    None
                };
                Some(Stmt::Return { value, span })
            }
            _ => None,
        }
    }

    fn coerce_or_check(&self, expr: &mut Expr, expected: &Type) -> bool {
        if expr.ty == *expected {
            return true;
        }
        if let (ExprKind::IntLit(v), Type::Uint(bits)) = (&expr.kind, expected)
            && *bits < 128
            && *v < (1u128 << bits)
        {
            expr.ty = expected.clone();
            return true;
        }
        false
    }

    fn check_expr(
        &mut self,
        node: NodeIndex,
        scope: &HashMap<String, ValueBinding>,
        expected: Option<&Type>,
    ) -> Option<Expr> {
        let span = self.ast.node_span(node);
        match self.ast.node_tag(node) {
            NodeTag::IntLitExpr => {
                let tok = self.ast.node_main_token(node);
                let raw = self.text(tok);
                let val: u128 = match raw.parse() {
                    Ok(v) => v,
                    Err(_) => {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            span,
                            format!("integer literal `{raw}` is out of range"),
                        ));
                        return None;
                    }
                };
                let ty = match expected {
                    Some(Type::Uint(bits)) if *bits < 128 && val < (1u128 << bits) => {
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
            NodeTag::BoolLitExpr => {
                let tok = self.ast.node_main_token(node);
                let val = self.ast.token_tag(tok) == TokenTag::True;
                Some(Expr {
                    kind: ExprKind::BoolLit(val),
                    ty: Type::Boolean,
                    span,
                })
            }
            NodeTag::DefaultExpr => {
                let data = self.ast.node_data(node);
                let ty = self.resolve_type(NodeIndex(data.lhs))?;
                Some(Expr {
                    kind: ExprKind::Default(ty.clone()),
                    ty,
                    span,
                })
            }
            NodeTag::IdentExpr => {
                let tok = self.ast.node_main_token(node);
                let name = self.text(tok);
                if let Some(binding) = scope.get(name) {
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
                if let Some(&field_id) = self.ledger_by_name.get(name) {
                    let field = &self.ledger_fields[field_id.0 as usize];
                    if field.adt == LedgerAdt::Cell {
                        return Some(Expr {
                            kind: ExprKind::LedgerCall {
                                field: field_id,
                                op: LedgerOp::CellRead,
                                args: Vec::new(),
                            },
                            ty: field.value_type.clone(),
                            span,
                        });
                    }
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        span,
                        format!(
                            "ledger field `{name}` of type `{}` cannot be read directly as a value",
                            field.adt.name()
                        ),
                    ));
                    return None;
                }
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    span,
                    format!("unbound identifier `{name}`"),
                ));
                None
            }
            NodeTag::MemberExpr => {
                let data = self.ast.node_data(node);
                let lhs = NodeIndex(data.lhs);
                let field_tok = TokenIndex(data.rhs);
                let field_name = self.text(field_tok);
                if self.ast.node_tag(lhs) == NodeTag::IdentExpr {
                    let type_name = self.text(self.ast.node_main_token(lhs));
                    if let Some(&enum_id) = self.enum_by_name.get(type_name) {
                        if let Some(idx) = self.enums[enum_id.0 as usize]
                            .variants
                            .iter()
                            .position(|v| v == field_name)
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
                            self.file,
                            self.ast.token_span(field_tok),
                            format!("enum `{type_name}` has no variant `{field_name}`"),
                        ));
                        return None;
                    }
                }
                let base = self.check_expr(lhs, scope, None)?;
                if let Some(fields) = self.struct_fields_of(&base.ty) {
                    if let Some((_, field_ty)) = fields.into_iter().find(|(n, _)| n == field_name) {
                        return Some(Expr {
                            kind: ExprKind::FieldAccess {
                                base: Box::new(base),
                                field: field_name.to_owned(),
                            },
                            ty: field_ty,
                            span,
                        });
                    }
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        self.ast.token_span(field_tok),
                        format!(
                            "type `{}` has no field `{field_name}`",
                            self.format_type(&base.ty)
                        ),
                    ));
                    return None;
                }
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    span,
                    format!(
                        "cannot access field `{field_name}` on type `{}`",
                        self.format_type(&base.ty)
                    ),
                ));
                None
            }
            NodeTag::StructLitExpr => {
                let lit = self.ast.struct_lit_expr(node);
                let ty = self.resolve_type(lit.type_node)?;
                let Some(expected_fields) = self.struct_fields_of(&ty) else {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        self.ast.node_span(lit.type_node),
                        format!("`{}` is not a struct type", self.format_type(&ty)),
                    ));
                    return None;
                };
                let lit_nodes: Vec<_> = self
                    .ast
                    .extra_nodes(lit.fields_start, lit.fields_end)
                    .collect();
                let mut provided: HashMap<String, Expr> = HashMap::new();
                for fnode in lit_nodes {
                    let sf = self.ast.struct_lit_field(fnode);
                    let fname = self.text(sf.name_token).to_owned();
                    let Some((_, expected_ty)) = expected_fields.iter().find(|(n, _)| *n == fname)
                    else {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            self.ast.token_span(sf.name_token),
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
                            self.file,
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
                            self.file,
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
                Some(Expr {
                    kind: ExprKind::StructLit { fields: ordered },
                    ty,
                    span,
                })
            }
            NodeTag::TupleExpr => {
                let data = self.ast.node_data(node);
                let elem_nodes: Vec<_> = self.ast.extra_nodes(data.lhs, data.rhs).collect();
                if let Some(Type::Vector(expected_len, elem_ty)) = expected {
                    if elem_nodes.len() != *expected_len as usize {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
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
                                self.file,
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
                let op_tok = self.ast.node_main_token(node);
                let data = self.ast.node_data(node);
                let operand = self.check_expr(NodeIndex(data.lhs), scope, expected)?;
                match self.ast.token_tag(op_tok) {
                    TokenTag::Bang => {
                        if operand.ty != Type::Boolean {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.file,
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
                                self.file,
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
                let op_tok = self.ast.node_main_token(node);
                let op = match self.ast.token_tag(op_tok) {
                    TokenTag::Plus => BinaryOp::Add,
                    TokenTag::Minus => BinaryOp::Sub,
                    TokenTag::EqEq => BinaryOp::Eq,
                    TokenTag::BangEq => BinaryOp::Neq,
                    TokenTag::AmpAmp => BinaryOp::And,
                    TokenTag::PipePipe => BinaryOp::Or,
                    other => {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            self.ast.token_span(op_tok),
                            format!("unsupported binary operator `{}`", other.as_str()),
                        ));
                        return None;
                    }
                };
                let data = self.ast.node_data(node);
                if matches!(op, BinaryOp::And | BinaryOp::Or) {
                    let lhs = self.check_expr(NodeIndex(data.lhs), scope, Some(&Type::Boolean))?;
                    let rhs = self.check_expr(NodeIndex(data.rhs), scope, Some(&Type::Boolean))?;
                    if lhs.ty != Type::Boolean || rhs.ty != Type::Boolean {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            span,
                            format!(
                                "logical `{}` expects `Boolean` operands, found `{}` and `{}`",
                                self.ast.token_tag(op_tok).as_str(),
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
                let lhs = self.check_expr(NodeIndex(data.lhs), scope, None)?;
                let mut rhs = self.check_expr(NodeIndex(data.rhs), scope, Some(&lhs.ty))?;
                if !self.coerce_or_check(&mut rhs, &lhs.ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        span,
                        format!(
                            "incompatible operand types `{}` and `{}`",
                            self.format_type(&lhs.ty),
                            self.format_type(&rhs.ty)
                        ),
                    ));
                    return None;
                }
                let ty = match op {
                    BinaryOp::Eq | BinaryOp::Neq | BinaryOp::And | BinaryOp::Or => Type::Boolean,
                    BinaryOp::Add | BinaryOp::Sub => lhs.ty.clone(),
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
                let t = self.ast.ternary_expr(node);
                let cond = self.check_expr(t.cond, scope, Some(&Type::Boolean))?;
                if cond.ty != Type::Boolean {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
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
                        self.file,
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
                let data = self.ast.node_data(node);
                let target = self.resolve_type(NodeIndex(data.rhs))?;
                let inner = self.check_expr(NodeIndex(data.lhs), scope, None)?;
                let valid = matches!(
                    (&inner.ty, &target),
                    (Type::Uint(_), Type::Field)
                        | (Type::Boolean, Type::Field)
                        | (Type::Enum(_), Type::Field)
                        | (Type::Field, Type::Field)
                ) || inner.ty == target;
                if !valid {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
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
                let a = self.ast.assert_expr(node);
                let cond = self.check_expr(a.cond, scope, Some(&Type::Boolean))?;
                if cond.ty != Type::Boolean {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        cond.span,
                        format!(
                            "`assert` condition must be `Boolean`, found `{}`",
                            self.format_type(&cond.ty)
                        ),
                    ));
                    return None;
                }
                if self.ast.node_tag(a.msg) != NodeTag::StringLitExpr {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        self.ast.node_span(a.msg),
                        "`assert` message must be a string literal",
                    ));
                    return None;
                }
                let raw_msg = self.text(self.ast.node_main_token(a.msg));
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
                let data = self.ast.node_data(node);
                let inner = self.check_expr(NodeIndex(data.lhs), scope, expected)?;
                let ty = inner.ty.clone();
                Some(Expr {
                    kind: ExprKind::Disclose(Box::new(inner)),
                    ty,
                    span,
                })
            }
            NodeTag::GenericCallExpr => {
                let call = self.ast.generic_call_expr(node);
                let targ_nodes: Vec<_> = self
                    .ast
                    .extra_nodes(call.targs_start, call.targs_end)
                    .collect();
                let arg_nodes: Vec<_> = self
                    .ast
                    .extra_nodes(call.args_start, call.args_end)
                    .collect();
                if self.ast.node_tag(call.callee) == NodeTag::IdentExpr {
                    let callee_tok = self.ast.node_main_token(call.callee);
                    let callee_name = self.text(callee_tok);
                    return self.check_generic_builtin(
                        callee_name,
                        self.ast.token_span(callee_tok),
                        &targ_nodes,
                        &arg_nodes,
                        span,
                        scope,
                    );
                }
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    span,
                    "unsupported generic call target",
                ));
                None
            }
            NodeTag::CallExpr => {
                let call = self.ast.call_expr(node);
                let arg_nodes: Vec<_> = self
                    .ast
                    .extra_nodes(call.args_start, call.args_end)
                    .collect();

                // 1. Direct identifier call: `pad(...)`, circuit call, or witness call.
                if self.ast.node_tag(call.callee) == NodeTag::IdentExpr {
                    let callee_tok = self.ast.node_main_token(call.callee);
                    let callee_name = self.text(callee_tok);
                    if callee_name == "pad" {
                        return self.check_pad_call(&arg_nodes, span);
                    }
                    if let Some(&cid) = self.circuit_by_name.get(callee_name) {
                        return self.check_circuit_call(cid, &arg_nodes, span, scope);
                    }
                    if let Some(&wid) = self.witness_by_name.get(callee_name) {
                        return self.check_witness_call(wid, &arg_nodes, span, scope);
                    }
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        self.ast.token_span(callee_tok),
                        format!("unknown circuit or witness `{callee_name}`"),
                    ));
                    return None;
                }

                // 2. Ledger ADT method call.
                if self.ast.node_tag(call.callee) == NodeTag::MemberExpr {
                    let mdata = self.ast.node_data(call.callee);
                    let recv = NodeIndex(mdata.lhs);
                    let method_tok = TokenIndex(mdata.rhs);
                    if self.ast.node_tag(recv) == NodeTag::IdentExpr {
                        let recv_name = self.text(self.ast.node_main_token(recv));
                        if let Some(&field_id) = self.ledger_by_name.get(recv_name) {
                            let method_name = self.text(method_tok);
                            return self.check_ledger_call(
                                field_id,
                                method_name,
                                self.ast.token_span(method_tok),
                                &arg_nodes,
                                span,
                                scope,
                            );
                        }
                    }
                }

                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    span,
                    "unsupported call target",
                ));
                None
            }
            _ => {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
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
                self.file,
                call_span,
                format!("`pad` expects 2 arguments (length, string), found {}", arg_nodes.len()),
            ));
            return None;
        }
        if self.ast.node_tag(arg_nodes[0]) != NodeTag::IntLitExpr {
            self.diagnostics.push(CompactDiagnostic::error(
                self.file,
                self.ast.node_span(arg_nodes[0]),
                "`pad` length must be an integer literal",
            ));
            return None;
        }
        let len: u32 = match self.text(self.ast.node_main_token(arg_nodes[0])).parse() {
            Ok(n) => n,
            Err(_) => {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
                    self.ast.node_span(arg_nodes[0]),
                    "invalid `pad` length",
                ));
                return None;
            }
        };
        if self.ast.node_tag(arg_nodes[1]) != NodeTag::StringLitExpr {
            self.diagnostics.push(CompactDiagnostic::error(
                self.file,
                self.ast.node_span(arg_nodes[1]),
                "`pad` second argument must be a string literal",
            ));
            return None;
        }
        let text = unquote_string(self.text(self.ast.node_main_token(arg_nodes[1])));
        let raw_bytes = text.as_bytes();
        if raw_bytes.len() > len as usize {
            self.diagnostics.push(CompactDiagnostic::error(
                self.file,
                self.ast.node_span(arg_nodes[1]),
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
                        self.file,
                        call_span,
                        "`some<T>(value)` expects 1 type argument and 1 value argument",
                    ));
                    return None;
                }
                let ty = self.resolve_type(targ_nodes[0])?;
                let mut val = self.check_expr(arg_nodes[0], scope, Some(&ty))?;
                if !self.coerce_or_check(&mut val, &ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
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
                        self.file,
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
            "persistentHash" => {
                if targ_nodes.len() != 1 || arg_nodes.len() != 1 {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        call_span,
                        "`persistentHash<T>(value)` expects 1 type argument and 1 value argument",
                    ));
                    return None;
                }
                let input_ty = self.resolve_type(targ_nodes[0])?;
                let mut arg = self.check_expr(arg_nodes[0], scope, Some(&input_ty))?;
                if !self.coerce_or_check(&mut arg, &input_ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
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
            "merkleTreePathRoot" => {
                if targ_nodes.len() != 2 || arg_nodes.len() != 1 {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        call_span,
                        "`merkleTreePathRoot<N, T>(path)` expects 2 type arguments and 1 value argument",
                    ));
                    return None;
                }
                let depth =
                    self.expect_type_nat(targ_nodes, 0, "merkleTreePathRoot", call_span)?;
                let leaf_ty = self.resolve_type(targ_nodes[1])?;
                let expected_path_ty = Type::MerkleTreePath(depth, Box::new(leaf_ty.clone()));
                let mut path = self.check_expr(arg_nodes[0], scope, Some(&expected_path_ty))?;
                if !self.coerce_or_check(&mut path, &expected_path_ty) {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
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
            other => {
                self.diagnostics.push(CompactDiagnostic::error(
                    self.file,
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
                self.file,
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
                    self.file,
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
                self.file,
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
                    self.file,
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

    fn check_ledger_call(
        &mut self,
        field_id: LedgerFieldId,
        method_name: &str,
        method_span: Span,
        arg_nodes: &[NodeIndex],
        call_span: Span,
        scope: &HashMap<String, ValueBinding>,
    ) -> Option<Expr> {
        let adt = self.ledger_fields[field_id.0 as usize].adt;
        let value_type = self.ledger_fields[field_id.0 as usize].value_type.clone();

        match adt {
            LedgerAdt::Counter => {
                let (op, expected_args, ret_ty) = match method_name {
                    "increment" => (LedgerOp::CounterIncrement, 1usize, Type::unit()),
                    "decrement" => (LedgerOp::CounterDecrement, 1usize, Type::unit()),
                    "read" => (LedgerOp::CounterRead, 0usize, Type::Uint(64)),
                    other => {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            method_span,
                            format!("`Counter` has no method `{other}`"),
                        ));
                        return None;
                    }
                };

                if arg_nodes.len() != expected_args {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
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
                        && let ExprKind::IntLit(v) = arg.kind
                    {
                        if v > u16::MAX as u128 {
                            self.diagnostics.push(CompactDiagnostic::error(
                                self.file,
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

                Some(Expr {
                    kind: ExprKind::LedgerCall {
                        field: field_id,
                        op,
                        args,
                    },
                    ty: ret_ty,
                    span: call_span,
                })
            }
            LedgerAdt::Cell => match method_name {
                "read" => {
                    if !arg_nodes.is_empty() {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            call_span,
                            "`Cell.read` takes 0 arguments",
                        ));
                        return None;
                    }
                    Some(Expr {
                        kind: ExprKind::LedgerCall {
                            field: field_id,
                            op: LedgerOp::CellRead,
                            args: Vec::new(),
                        },
                        ty: value_type,
                        span: call_span,
                    })
                }
                "write" => {
                    if arg_nodes.len() != 1 {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            call_span,
                            "`Cell.write` takes 1 argument",
                        ));
                        return None;
                    }
                    let mut val = self.check_expr(arg_nodes[0], scope, Some(&value_type))?;
                    if !self.coerce_or_check(&mut val, &value_type) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            val.span,
                            format!(
                                "`Cell.write` expects `{}`, found `{}`",
                                self.format_type(&value_type),
                                self.format_type(&val.ty)
                            ),
                        ));
                        return None;
                    }
                    Some(Expr {
                        kind: ExprKind::LedgerCall {
                            field: field_id,
                            op: LedgerOp::CellWrite,
                            args: vec![val],
                        },
                        ty: Type::unit(),
                        span: call_span,
                    })
                }
                other => {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        method_span,
                        format!("`Cell` has no method `{other}`"),
                    ));
                    None
                }
            },
            LedgerAdt::Set => match method_name {
                "member" | "insert" | "remove" => {
                    let (op, ret_ty) = match method_name {
                        "member" => (LedgerOp::SetMember, Type::Boolean),
                        "insert" => (LedgerOp::SetInsert, Type::unit()),
                        _ => (LedgerOp::SetRemove, Type::unit()),
                    };
                    if arg_nodes.len() != 1 {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            call_span,
                            format!("`Set.{method_name}` takes 1 argument"),
                        ));
                        return None;
                    }
                    let mut elem = self.check_expr(arg_nodes[0], scope, Some(&value_type))?;
                    if !self.coerce_or_check(&mut elem, &value_type) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            elem.span,
                            format!(
                                "`Set.{method_name}` expects `{}`, found `{}`",
                                self.format_type(&value_type),
                                self.format_type(&elem.ty)
                            ),
                        ));
                        return None;
                    }
                    Some(Expr {
                        kind: ExprKind::LedgerCall {
                            field: field_id,
                            op,
                            args: vec![elem],
                        },
                        ty: ret_ty,
                        span: call_span,
                    })
                }
                other => {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        method_span,
                        format!("`Set` has no method `{other}`"),
                    ));
                    None
                }
            },
            LedgerAdt::MerkleTree(_) => match method_name {
                "insert" => {
                    if arg_nodes.len() != 1 {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            call_span,
                            "`MerkleTree.insert` takes 1 argument",
                        ));
                        return None;
                    }
                    let mut item = self.check_expr(arg_nodes[0], scope, Some(&value_type))?;
                    if !self.coerce_or_check(&mut item, &value_type) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            item.span,
                            format!(
                                "`MerkleTree.insert` expects `{}`, found `{}`",
                                self.format_type(&value_type),
                                self.format_type(&item.ty)
                            ),
                        ));
                        return None;
                    }
                    Some(Expr {
                        kind: ExprKind::LedgerCall {
                            field: field_id,
                            op: LedgerOp::MerkleTreeInsert,
                            args: vec![item],
                        },
                        ty: Type::unit(),
                        span: call_span,
                    })
                }
                "checkRoot" => {
                    if arg_nodes.len() != 1 {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            call_span,
                            "`MerkleTree.checkRoot` takes 1 argument",
                        ));
                        return None;
                    }
                    let mut rt =
                        self.check_expr(arg_nodes[0], scope, Some(&Type::MerkleTreeDigest))?;
                    if !self.coerce_or_check(&mut rt, &Type::MerkleTreeDigest) {
                        self.diagnostics.push(CompactDiagnostic::error(
                            self.file,
                            rt.span,
                            format!(
                                "`MerkleTree.checkRoot` expects `MerkleTreeDigest`, found `{}`",
                                self.format_type(&rt.ty)
                            ),
                        ));
                        return None;
                    }
                    Some(Expr {
                        kind: ExprKind::LedgerCall {
                            field: field_id,
                            op: LedgerOp::MerkleTreeCheckRoot,
                            args: vec![rt],
                        },
                        ty: Type::Boolean,
                        span: call_span,
                    })
                }
                other => {
                    self.diagnostics.push(CompactDiagnostic::error(
                        self.file,
                        method_span,
                        format!("`MerkleTree` has no method `{other}`"),
                    ));
                    None
                }
            },
        }
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
        ExprKind::LedgerCall { args, .. } => {
            let mut w = false;
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
        ExprKind::Tuple(elems) | ExprKind::Vector(elems) => {
            let (mut l, mut w) = (false, false);
            for e in elems {
                let (el, ew) = expr_effects(e, calls);
                l |= el;
                w |= ew;
            }
            (l, w)
        }
        ExprKind::Unary { operand, .. }
        | ExprKind::Cast { expr: operand, .. }
        | ExprKind::Assert { cond: operand, .. }
        | ExprKind::Disclose(operand)
        | ExprKind::PersistentHash { arg: operand, .. }
        | ExprKind::MerkleTreePathRoot { path: operand, .. }
        | ExprKind::FieldAccess { base: operand, .. }
        | ExprKind::MaybeSome(operand) => expr_effects(operand, calls),
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
        let src = "export ledger round: Counter; export circuit inc(): [] { round.increment(70000); }";
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        let checked = check(file, &parsed.ast);
        assert!(checked.diagnostics.has_errors());
        assert!(checked.diagnostics.diagnostics[0].message.contains("Uint<16>"));
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
}
