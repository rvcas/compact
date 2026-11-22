use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::{Path, PathBuf};

use compact_hir::{
    BinaryOp, Circuit, CircuitId, EnumDecl, Expr, ExprKind, LedgerAdt, LedgerOp, LocalId, Param,
    Program as HirProgram, Stmt, StructDecl, Type, UnaryOp,
};
use compact_span::Span as CompactSpan;
use oxc_allocator::{Allocator, ArenaVec, GetAllocator};
use oxc_ast::ast::*;
use oxc_ast::builder::{AstBuilder, GetAstBuilder};
use oxc_codegen::{Codegen, CodegenOptions};
use oxc_isolated_declarations::{IsolatedDeclarations, IsolatedDeclarationsOptions};
use oxc_semantic::SemanticBuilder;
use oxc_span::{SPAN, SourceType, Span};
use oxc_str::{Ident, Str};
use oxc_syntax::number::NumberBase;
use oxc_syntax::operator::{AssignmentOperator, BinaryOperator, LogicalOperator, UnaryOperator};
use oxc_transformer::{TransformOptions, Transformer};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum TsCodegenError {
    #[error("oxc isolated declarations failed:\n{}", .0.join("\n"))]
    IsolatedDeclarations(Vec<String>),
    #[error("oxc transformer failed:\n{}", .0.join("\n"))]
    Transform(Vec<String>),
}

pub struct TsCodegenInput<'a> {
    pub program: &'a HirProgram,
    pub source_name: &'a str,
    pub source_text: &'a str,
    /// Map of exported proof circuit name -> lowercase hex SHA-256 of its verifier key.
    pub verifier_key_hashes: &'a BTreeMap<String, String>,
}

#[derive(Debug, Clone)]
pub struct GeneratedTs {
    /// TypeScript source generated directly from the `oxc` TS AST.
    pub ts: String,
    /// JavaScript ESM output produced by `oxc_transformer` type-stripping + `oxc_codegen`.
    pub js: String,
    /// TypeScript declaration file produced by `oxc_isolated_declarations` + `oxc_codegen`.
    pub dts: String,
    /// VLQ Source Map v3 JSON mapping `index.js` back to the `.compact` source.
    pub source_map: String,
}

pub fn generate_ts(input: &TsCodegenInput<'_>) -> Result<GeneratedTs, TsCodegenError> {
    let allocator = Allocator::default();
    let emitter = TsEmitter::new(&allocator, input);
    let mut ts_program = emitter.build_program();

    // 1. Emit TypeScript source directly from the typed oxc AST.
    let ts = Codegen::new()
        .with_options(CodegenOptions::default())
        .build(&ts_program)
        .code;

    // 2. Derive `.d.ts` directly from the same TS AST via oxc_isolated_declarations.
    let dts_ret =
        IsolatedDeclarations::new(&allocator, IsolatedDeclarationsOptions::default())
            .build(&ts_program);
    if !dts_ret.diagnostics.is_empty() {
        let msgs: Vec<_> = dts_ret.diagnostics.iter().map(|d| d.to_string()).collect();
        return Err(TsCodegenError::IsolatedDeclarations(msgs));
    }
    let dts = Codegen::new()
        .with_options(CodegenOptions::default())
        .build(&dts_ret.program)
        .code;

    // 3. Strip TypeScript types in-place via oxc_semantic + oxc_transformer.
    let sem_ret = SemanticBuilder::new().with_enum_eval(true).build(&ts_program);
    let scoping = sem_ret.semantic.into_scoping();
    let tx_opts = TransformOptions::default();
    let tx_ret = Transformer::new(&allocator, Path::new("index.ts"), &tx_opts)
        .build_with_scoping(scoping, &mut ts_program);
    if !tx_ret.diagnostics.is_empty() {
        let msgs: Vec<_> = tx_ret.diagnostics.iter().map(|d| d.to_string()).collect();
        return Err(TsCodegenError::Transform(msgs));
    }

    // 4. Emit ESM JS + Source Map v3 referencing the original `.compact` source file.
    let js_opts = CodegenOptions {
        source_map_path: Some(PathBuf::from(input.source_name)),
        ..CodegenOptions::default()
    };
    let js_ret = Codegen::new().with_options(js_opts).build(&ts_program);
    let source_map = js_ret
        .map
        .map(|m| m.to_json_string())
        .unwrap_or_else(|| "{}".to_owned());

    Ok(GeneratedTs {
        ts,
        js: js_ret.code,
        dts,
        source_map,
    })
}

struct TsEmitter<'a, 'b> {
    builder: AstBuilder<'a>,
    input: &'b TsCodegenInput<'b>,
}

impl<'a> GetAstBuilder<'a> for TsEmitter<'a, '_> {
    type Builder = AstBuilder<'a>;

    fn builder(&self) -> &AstBuilder<'a> {
        &self.builder
    }
}

impl<'a> GetAllocator<'a> for TsEmitter<'a, '_> {
    fn allocator(&self) -> &'a Allocator {
        self.builder.allocator()
    }
}

impl<'a, 'b> TsEmitter<'a, 'b> {
    fn new(allocator: &'a Allocator, input: &'b TsCodegenInput<'b>) -> Self {
        Self {
            builder: AstBuilder::new(allocator),
            input,
        }
    }

    fn oxc_span(&self, span: CompactSpan) -> Span {
        let max = self.input.source_text.len() as u32;
        Span::new(span.start.min(max), span.end.min(max))
    }

    fn ident(&self, name: &str) -> Ident<'a> {
        Ident::from_str_in(name, self)
    }

    fn str_atom(&self, text: &str) -> Str<'a> {
        Str::from_str_in(text, self)
    }

    fn expr_ident(&self, span: Span, name: &str) -> Expression<'a> {
        Expression::new_identifier(span, self.ident(name), self)
    }

    fn expr_str(&self, span: Span, text: &str) -> Expression<'a> {
        Expression::new_string_literal(span, self.str_atom(text), None, self)
    }

    fn expr_num(&self, span: Span, value: f64) -> Expression<'a> {
        Expression::new_numeric_literal(span, value, None, NumberBase::Decimal, self)
    }

    fn expr_bool(&self, span: Span, value: bool) -> Expression<'a> {
        Expression::new_boolean_literal(span, value, self)
    }

    fn expr_member(&self, span: Span, object: Expression<'a>, prop: &str) -> Expression<'a> {
        Expression::StaticMemberExpression(StaticMemberExpression::boxed(
            span,
            object,
            IdentifierName::new(span, self.ident(prop), self),
            false,
            self,
        ))
    }

    fn expr_call(
        &self,
        span: Span,
        callee: Expression<'a>,
        args: ArenaVec<'a, Argument<'a>>,
    ) -> Expression<'a> {
        Expression::new_call_expression(span, callee, None, args, false, self)
    }

    fn binding_ident(&self, span: Span, name: &str) -> BindingPattern<'a> {
        BindingPattern::new_binding_identifier(span, self.ident(name), self)
    }

    fn ts_type_ref(&self, name: &str, type_args: Option<ArenaVec<'a, TSType<'a>>>) -> TSType<'a> {
        let type_name = TSTypeName::new_identifier_reference(SPAN, self.ident(name), self);
        let type_arguments =
            type_args.map(|params| TSTypeParameterInstantiation::boxed(SPAN, params, self));
        TSType::new_ts_type_reference(SPAN, type_name, type_arguments, self)
    }

    fn ts_runtime_type(
        &self,
        name: &str,
        type_args: Option<ArenaVec<'a, TSType<'a>>>,
    ) -> TSType<'a> {
        let qualified = TSQualifiedName::boxed(
            SPAN,
            TSTypeName::new_identifier_reference(SPAN, self.ident("__compactRuntime"), self),
            IdentifierName::new(SPAN, self.ident(name), self),
            self,
        );
        let type_arguments =
            type_args.map(|params| TSTypeParameterInstantiation::boxed(SPAN, params, self));
        TSType::new_ts_type_reference(SPAN, TSTypeName::QualifiedName(qualified), type_arguments, self)
    }

    fn ts_type_annotation(&self, ty: TSType<'a>) -> oxc_allocator::ArenaBox<'a, TSTypeAnnotation<'a>> {
        TSTypeAnnotation::boxed(SPAN, ty, self)
    }

    fn ts_type_param(&self, name: &str) -> TSTypeParameter<'a> {
        TSTypeParameter::new(
            SPAN,
            BindingIdentifier::new(SPAN, self.ident(name), self),
            None,
            None,
            false,
            false,
            false,
            self,
        )
    }

    fn hir_type_to_ts(&self, ty: &Type) -> TSType<'a> {
        match ty {
            Type::Field | Type::Uint(_) => TSType::new_ts_big_int_keyword(SPAN, self),
            Type::Boolean => TSType::new_ts_boolean_keyword(SPAN, self),
            Type::Bytes(_) => self.ts_type_ref("Uint8Array", None),
            Type::Opaque(ts_ty) => match ts_ty.as_str() {
                "string" => TSType::new_ts_string_keyword(SPAN, self),
                other => self.ts_type_ref(other, None),
            },
            Type::Vector(len, elem) => {
                let mut ts_elems = ArenaVec::with_capacity_in(*len as usize, self);
                for _ in 0..*len {
                    ts_elems.push(TSTupleElement::from(self.hir_type_to_ts(elem)));
                }
                TSType::new_ts_tuple_type(SPAN, ts_elems, self)
            }
            Type::Enum(id) => {
                let decl = self.input.program.enum_decl(*id);
                self.ts_type_ref(&decl.name, None)
            }
            Type::Struct(id) => {
                let decl = self.input.program.struct_decl(*id);
                self.ts_type_ref(&decl.name, None)
            }
            Type::Maybe(inner) => {
                let mut targs = ArenaVec::with_capacity_in(1, self);
                targs.push(self.hir_type_to_ts(inner));
                self.ts_type_ref("Maybe", Some(targs))
            }
            Type::MerkleTreeDigest => self.ts_runtime_type("MerkleTreeDigest", None),
            Type::MerkleTreePathEntry => self.ts_runtime_type("MerkleTreePathEntry", None),
            Type::MerkleTreePath(_, leaf) => {
                let mut targs = ArenaVec::with_capacity_in(1, self);
                targs.push(self.hir_type_to_ts(leaf));
                self.ts_runtime_type("MerkleTreePath", Some(targs))
            }
            Type::Tuple(elems) => {
                let mut ts_elems = ArenaVec::with_capacity_in(elems.len(), self);
                for elem in elems {
                    ts_elems.push(TSTupleElement::from(self.hir_type_to_ts(elem)));
                }
                TSType::new_ts_tuple_type(SPAN, ts_elems, self)
            }
        }
    }

    fn collect_called_circuits(&self) -> HashSet<CircuitId> {
        fn visit_expr(expr: &Expr, out: &mut HashSet<CircuitId>) {
            match &expr.kind {
                ExprKind::CircuitCall { circuit, args } => {
                    out.insert(*circuit);
                    for a in args {
                        visit_expr(a, out);
                    }
                }
                ExprKind::Tuple(es) | ExprKind::Vector(es) => {
                    for e in es {
                        visit_expr(e, out);
                    }
                }
                ExprKind::Unary { operand, .. }
                | ExprKind::Cast { expr: operand, .. }
                | ExprKind::Disclose(operand)
                | ExprKind::PersistentHash { arg: operand, .. }
                | ExprKind::MerkleTreePathRoot { path: operand, .. }
                | ExprKind::FieldAccess { base: operand, .. }
                | ExprKind::MaybeSome(operand) => visit_expr(operand, out),
                ExprKind::StructLit { fields } => {
                    for (_, e) in fields {
                        visit_expr(e, out);
                    }
                }
                ExprKind::Binary { lhs, rhs, .. } => {
                    visit_expr(lhs, out);
                    visit_expr(rhs, out);
                }
                ExprKind::Ternary {
                    cond,
                    then_branch,
                    else_branch,
                } => {
                    visit_expr(cond, out);
                    visit_expr(then_branch, out);
                    visit_expr(else_branch, out);
                }
                ExprKind::Assert { cond, .. } => visit_expr(cond, out),
                ExprKind::WitnessCall { args, .. } | ExprKind::LedgerCall { args, .. } => {
                    for a in args {
                        visit_expr(a, out);
                    }
                }
                ExprKind::IntLit(_)
                | ExprKind::BoolLit(_)
                | ExprKind::BytesLit(_)
                | ExprKind::Default(_)
                | ExprKind::ParamRef(_)
                | ExprKind::LocalRef(_)
                | ExprKind::EnumVariant { .. }
                | ExprKind::MaybeNone(_) => {}
            }
        }
        fn visit_stmts(stmts: &[Stmt], out: &mut HashSet<CircuitId>) {
            for stmt in stmts {
                match stmt {
                    Stmt::Const { init, .. } => visit_expr(init, out),
                    Stmt::If {
                        cond,
                        then_branch,
                        else_branch,
                        ..
                    } => {
                        visit_expr(cond, out);
                        visit_stmts(then_branch, out);
                        visit_stmts(else_branch, out);
                    }
                    Stmt::Expr(e) => visit_expr(e, out),
                    Stmt::Return { value: Some(e), .. } => visit_expr(e, out),
                    Stmt::Return { value: None, .. } => {}
                }
            }
        }
        let mut called = HashSet::new();
        if let Some(ctor) = &self.input.program.constructor {
            visit_stmts(&ctor.body, &mut called);
        }
        for c in &self.input.program.circuits {
            visit_stmts(&c.body, &mut called);
        }
        called
    }

    fn uses_maybe(&self) -> bool {
        fn ty_uses_maybe(ty: &Type) -> bool {
            match ty {
                Type::Maybe(_) => true,
                Type::Vector(_, e) => ty_uses_maybe(e),
                Type::Tuple(es) => es.iter().any(ty_uses_maybe),
                _ => false,
            }
        }
        self.input
            .program
            .exported_stdlib_types
            .iter()
            .any(|s| s == "Maybe")
            || self
                .input
                .program
                .circuits
                .iter()
                .any(|c| ty_uses_maybe(&c.ret_type) || c.params.iter().any(|p| ty_uses_maybe(&p.ty)))
            || self
                .input
                .program
                .ledger_fields
                .iter()
                .any(|f| ty_uses_maybe(&f.value_type))
            || self
                .input
                .program
                .witnesses
                .iter()
                .any(|w| ty_uses_maybe(&w.ret_type) || w.params.iter().any(|p| ty_uses_maybe(&p.ty)))
    }

    fn build_maybe_type(&self, exported: bool) -> Statement<'a> {
        let mut tparams = ArenaVec::with_capacity_in(1, self);
        tparams.push(self.ts_type_param("T"));
        let mut members = ArenaVec::with_capacity_in(2, self);
        members.push(TSSignature::new_ts_property_signature(
            SPAN,
            false,
            false,
            false,
            PropertyKey::StaticIdentifier(IdentifierName::boxed(SPAN, self.ident("is_some"), self)),
            Some(self.ts_type_annotation(TSType::new_ts_boolean_keyword(SPAN, self))),
            self,
        ));
        members.push(TSSignature::new_ts_property_signature(
            SPAN,
            false,
            false,
            false,
            PropertyKey::StaticIdentifier(IdentifierName::boxed(SPAN, self.ident("value"), self)),
            Some(self.ts_type_annotation(self.ts_type_ref("T", None))),
            self,
        ));
        let obj = TSType::new_ts_type_literal(SPAN, members, self);
        let type_parameters = Some(TSTypeParameterDeclaration::boxed(SPAN, tparams, self));
        let decl = Declaration::new_ts_type_alias_declaration(
            SPAN,
            BindingIdentifier::new(SPAN, self.ident("Maybe"), self),
            type_parameters,
            obj,
            false,
            self,
        );
        if exported {
            Statement::new_export_declaration(SPAN, decl, self)
        } else {
            Statement::from(decl)
        }
    }

    fn build_program(&self) -> Program<'a> {
        let mut body = ArenaVec::new_in(self);

        // import * as __compactRuntime from '@midnight-ntwrk/compact-runtime';
        body.push(self.build_runtime_import());

        // Emit standard library types such as `export type Maybe<T> = { is_some: boolean; value: T };`
        if self.uses_maybe() {
            let exported = self
                .input
                .program
                .exported_stdlib_types
                .iter()
                .any(|s| s == "Maybe");
            body.push(self.build_maybe_type(exported));
        }

        // Emit enum declarations (exported if exported in Compact; still emitted locally if used).
        for enum_decl in &self.input.program.enums {
            body.push(self.build_enum_decl(enum_decl));
        }

        // Emit struct type aliases.
        for struct_decl in &self.input.program.structs {
            body.push(self.build_struct_decl(struct_decl));
        }

        // Emit helper functions for non-exported circuits and any circuit called by another circuit/constructor.
        let called_circuits = self.collect_called_circuits();
        for circuit in &self.input.program.circuits {
            if !circuit.exported || called_circuits.contains(&circuit.id) {
                body.push(self.build_helper_circuit_fn(circuit));
            }
        }

        // export type Witnesses<T> = {};
        body.push(self.build_witnesses_type());

        // export type ImpureCircuits<T> = { ... };
        body.push(self.build_circuits_type("ImpureCircuits", true, true));

        // export type PureCircuits = { ... };
        body.push(self.build_pure_circuits_type());

        // export type Circuits<T> = { ... };
        body.push(self.build_circuits_type("Circuits", false, true));

        // export type Ledger = { readonly round: bigint; ... };
        body.push(self.build_ledger_type());

        // export const pureCircuits: PureCircuits = { ... };
        body.push(self.build_pure_circuits_const());

        // export const ledger = (state: __compactRuntime.StateValue): Ledger => ({ ... });
        body.push(self.build_ledger_fn());

        // export class Contract<T, W extends Witnesses<T> = Witnesses<T>> { ... }
        body.push(self.build_contract_class());

        // export const _expectedVk: Record<string, string> = { ... };
        if !self.input.verifier_key_hashes.is_empty() {
            body.push(self.build_expected_vk_const());
        }

        let source_text = self.builder.allocator().alloc_str(self.input.source_text);
        Program::new(
            SPAN,
            SourceType::ts(),
            source_text,
            ArenaVec::new_in(self),
            None,
            ArenaVec::new_in(self),
            body,
            self,
        )
    }

    fn build_runtime_import(&self) -> Statement<'a> {
        let mut specifiers = ArenaVec::with_capacity_in(1, self);
        specifiers.push(ImportDeclarationSpecifier::new_import_namespace_specifier(
            SPAN,
            BindingIdentifier::new(SPAN, self.ident("__compactRuntime"), self),
            self,
        ));
        Statement::new_import_declaration(
            SPAN,
            Some(specifiers),
            StringLiteral::new(
                SPAN,
                self.str_atom("@midnight-ntwrk/compact-runtime"),
                None,
                self,
            ),
            None,
            None,
            ImportOrExportKind::Value,
            self,
        )
    }

    fn build_enum_decl(&self, decl: &EnumDecl) -> Statement<'a> {
        let span = self.oxc_span(decl.span);
        let mut members = ArenaVec::with_capacity_in(decl.variants.len(), self);
        for (idx, variant) in decl.variants.iter().enumerate() {
            members.push(TSEnumMember::new(
                SPAN,
                TSEnumMemberName::Identifier(IdentifierName::boxed(SPAN, self.ident(variant), self)),
                Some(self.expr_num(SPAN, idx as f64)),
                self,
            ));
        }
        let body = TSEnumBody::new(SPAN, members, self);
        let enum_decl = Declaration::new_ts_enum_declaration(
            span,
            BindingIdentifier::new(span, self.ident(&decl.name), self),
            body,
            false,
            false,
            self,
        );
        if decl.exported {
            Statement::new_export_declaration(span, enum_decl, self)
        } else {
            Statement::from(enum_decl)
        }
    }

    fn build_struct_decl(&self, decl: &StructDecl) -> Statement<'a> {
        let mut members = ArenaVec::with_capacity_in(decl.fields.len(), self);
        for f in &decl.fields {
            members.push(TSSignature::new_ts_property_signature(
                SPAN,
                false,
                false,
                false,
                PropertyKey::StaticIdentifier(IdentifierName::boxed(
                    SPAN,
                    self.ident(&f.name),
                    self,
                )),
                Some(self.ts_type_annotation(self.hir_type_to_ts(&f.ty))),
                self,
            ));
        }
        let obj = TSType::new_ts_type_literal(SPAN, members, self);
        let td = Declaration::new_ts_type_alias_declaration(
            self.oxc_span(decl.span),
            BindingIdentifier::new(SPAN, self.ident(&decl.name), self),
            None,
            obj,
            false,
            self,
        );
        if decl.exported {
            Statement::new_export_declaration(SPAN, td, self)
        } else {
            Statement::from(td)
        }
    }

    fn build_helper_circuit_fn(&self, circuit: &Circuit) -> Statement<'a> {
        let span = self.oxc_span(circuit.span);
        let mut params = ArenaVec::new_in(self);
        if !circuit.pure {
            let mut ctx_targs = ArenaVec::with_capacity_in(1, self);
            ctx_targs.push(TSType::new_ts_unknown_keyword(SPAN, self));
            params.push(FormalParameter::new(
                SPAN,
                ArenaVec::new_in(self),
                self.binding_ident(SPAN, "context"),
                Some(self.ts_type_annotation(self.ts_runtime_type("CircuitContext", Some(ctx_targs)))),
                None,
                false,
                None,
                false,
                false,
                self,
            ));
        }
        for p in &circuit.params {
            params.push(FormalParameter::new(
                self.oxc_span(p.span),
                ArenaVec::new_in(self),
                self.binding_ident(self.oxc_span(p.span), &p.name),
                Some(self.ts_type_annotation(self.hir_type_to_ts(&p.ty))),
                None,
                false,
                None,
                false,
                false,
                self,
            ));
        }
        let formal_params = FormalParameters::boxed(
            SPAN,
            FormalParameterKind::FormalParameter,
            params,
            None,
            self,
        );
        let stmts = self.lower_stmts(circuit);
        let body = FunctionBody::boxed(SPAN, ArenaVec::new_in(self), stmts, self);
        let func = Declaration::new_function_declaration(
            span,
            FunctionType::FunctionDeclaration,
            Some(BindingIdentifier::new(span, self.ident(&format!("_{}", circuit.name)), self)),
            false,
            false,
            false,
            None,
            None,
            formal_params,
            Some(self.ts_type_annotation(self.hir_type_to_ts(&circuit.ret_type))),
            Some(body),
            self,
        );
        Statement::from(func)
    }

    fn export_type_alias(
        &self,
        name: &str,
        type_params: Option<ArenaVec<'a, TSTypeParameter<'a>>>,
        ty: TSType<'a>,
    ) -> Statement<'a> {
        let type_parameters =
            type_params.map(|params| TSTypeParameterDeclaration::boxed(SPAN, params, self));
        let decl = Declaration::new_ts_type_alias_declaration(
            SPAN,
            BindingIdentifier::new(SPAN, self.ident(name), self),
            type_parameters,
            ty,
            false,
            self,
        );
        Statement::new_export_declaration(SPAN, decl, self)
    }

    fn export_const(&self, name: &str, ty: TSType<'a>, init: Expression<'a>) -> Statement<'a> {
        let declarator = VariableDeclarator::new(
            SPAN,
            self.binding_ident(SPAN, name),
            Some(self.ts_type_annotation(ty)),
            Some(init),
            false,
            self,
        );
        let mut declarators = ArenaVec::with_capacity_in(1, self);
        declarators.push(declarator);
        let decl = Declaration::new_variable_declaration(
            SPAN,
            VariableDeclarationKind::Const,
            declarators,
            false,
            self,
        );
        Statement::new_export_declaration(SPAN, decl, self)
    }

    fn build_witnesses_type(&self) -> Statement<'a> {
        let mut tparams = ArenaVec::with_capacity_in(1, self);
        tparams.push(self.ts_type_param("T"));
        let mut members = ArenaVec::with_capacity_in(self.input.program.witnesses.len(), self);
        for w in &self.input.program.witnesses {
            let mut params = ArenaVec::with_capacity_in(w.params.len() + 1, self);
            let mut ctx_args = ArenaVec::with_capacity_in(2, self);
            ctx_args.push(self.ts_type_ref("Ledger", None));
            ctx_args.push(self.ts_type_ref("T", None));
            params.push(FormalParameter::new(
                SPAN,
                ArenaVec::new_in(self),
                self.binding_ident(SPAN, "context"),
                Some(self.ts_type_annotation(self.ts_runtime_type("WitnessContext", Some(ctx_args)))),
                None,
                false,
                None,
                false,
                false,
                self,
            ));
            for p in &w.params {
                params.push(FormalParameter::new(
                    SPAN,
                    ArenaVec::new_in(self),
                    self.binding_ident(SPAN, &p.name),
                    Some(self.ts_type_annotation(self.hir_type_to_ts(&p.ty))),
                    None,
                    false,
                    None,
                    false,
                    false,
                    self,
                ));
            }
            let formal_params = FormalParameters::boxed(
                SPAN,
                FormalParameterKind::Signature,
                params,
                None,
                self,
            );
            let mut ret_tuple = ArenaVec::with_capacity_in(2, self);
            ret_tuple.push(TSTupleElement::from(self.ts_type_ref("T", None)));
            ret_tuple.push(TSTupleElement::from(self.hir_type_to_ts(&w.ret_type)));
            let ret_ty = TSType::new_ts_tuple_type(SPAN, ret_tuple, self);
            members.push(TSSignature::new_ts_method_signature(
                SPAN,
                PropertyKey::StaticIdentifier(IdentifierName::boxed(
                    SPAN,
                    self.ident(&w.name),
                    self,
                )),
                false,
                false,
                TSMethodSignatureKind::Method,
                None,
                None,
                formal_params,
                Some(self.ts_type_annotation(ret_ty)),
                self,
            ));
        }
        let obj = TSType::new_ts_type_literal(SPAN, members, self);
        self.export_type_alias("Witnesses", Some(tparams), obj)
    }

    fn build_pure_circuits_type(&self) -> Statement<'a> {
        let mut members = ArenaVec::new_in(self);
        for circuit in &self.input.program.circuits {
            if circuit.exported && circuit.pure {
                members.push(self.build_circuit_method_signature(circuit, false));
            }
        }
        let lit = TSType::new_ts_type_literal(SPAN, members, self);
        self.export_type_alias("PureCircuits", None, lit)
    }

    fn build_circuits_type(
        &self,
        type_name: &str,
        impure_only: bool,
        with_context: bool,
    ) -> Statement<'a> {
        let mut tparams = ArenaVec::with_capacity_in(1, self);
        tparams.push(self.ts_type_param("T"));
        let mut members = ArenaVec::new_in(self);
        for circuit in &self.input.program.circuits {
            if !circuit.exported {
                continue;
            }
            if impure_only && circuit.pure {
                continue;
            }
            members.push(self.build_circuit_method_signature(circuit, with_context));
        }
        let lit = TSType::new_ts_type_literal(SPAN, members, self);
        self.export_type_alias(type_name, Some(tparams), lit)
    }

    fn build_circuit_method_signature(
        &self,
        circuit: &Circuit,
        with_context: bool,
    ) -> TSSignature<'a> {
        let mut params = ArenaVec::new_in(self);
        if with_context {
            let mut ctx_args = ArenaVec::with_capacity_in(1, self);
            ctx_args.push(self.ts_type_ref("T", None));
            params.push(FormalParameter::new(
                SPAN,
                ArenaVec::new_in(self),
                self.binding_ident(SPAN, "context"),
                Some(self.ts_type_annotation(self.ts_runtime_type("CircuitContext", Some(ctx_args)))),
                None,
                false,
                None,
                false,
                false,
                self,
            ));
        }
        for p in &circuit.params {
            params.push(FormalParameter::new(
                SPAN,
                ArenaVec::new_in(self),
                self.binding_ident(SPAN, &p.name),
                Some(self.ts_type_annotation(self.hir_type_to_ts(&p.ty))),
                None,
                false,
                None,
                false,
                false,
                self,
            ));
        }
        let formal_params = FormalParameters::boxed(
            SPAN,
            FormalParameterKind::Signature,
            params,
            None,
            self,
        );
        let ret_ty = if with_context {
            let mut res_args = ArenaVec::with_capacity_in(2, self);
            res_args.push(self.ts_type_ref("T", None));
            res_args.push(self.hir_type_to_ts(&circuit.ret_type));
            self.ts_runtime_type("CircuitResults", Some(res_args))
        } else {
            self.hir_type_to_ts(&circuit.ret_type)
        };
        TSSignature::new_ts_method_signature(
            SPAN,
            PropertyKey::StaticIdentifier(IdentifierName::boxed(
                SPAN,
                self.ident(&circuit.name),
                self,
            )),
            false,
            false,
            TSMethodSignatureKind::Method,
            None,
            None,
            formal_params,
            Some(self.ts_type_annotation(ret_ty)),
            self,
        )
    }

    fn build_ledger_type(&self) -> Statement<'a> {
        let mut members = ArenaVec::new_in(self);
        for field in &self.input.program.ledger_fields {
            if !field.exported {
                continue;
            }
            members.push(TSSignature::new_ts_property_signature(
                SPAN,
                false,
                false,
                true,
                PropertyKey::StaticIdentifier(IdentifierName::boxed(
                    SPAN,
                    self.ident(&field.name),
                    self,
                )),
                Some(self.ts_type_annotation(self.hir_type_to_ts(&field.value_type))),
                self,
            ));
        }
        let lit = TSType::new_ts_type_literal(SPAN, members, self);
        self.export_type_alias("Ledger", None, lit)
    }

    fn build_pure_circuits_const(&self) -> Statement<'a> {
        let mut props = ArenaVec::new_in(self);
        for circuit in &self.input.program.circuits {
            if circuit.exported && circuit.pure {
                let func = self.build_pure_circuit_arrow(circuit);
                props.push(ObjectPropertyKind::new_object_property(
                    self.oxc_span(circuit.span),
                    PropertyKind::Init,
                    PropertyKey::StaticIdentifier(IdentifierName::boxed(
                        SPAN,
                        self.ident(&circuit.name),
                        self,
                    )),
                    func,
                    false,
                    false,
                    false,
                    self,
                ));
            }
        }
        let init = Expression::new_object_expression(SPAN, props, self);
        self.export_const("pureCircuits", self.ts_type_ref("PureCircuits", None), init)
    }

    fn build_pure_circuit_arrow(&self, circuit: &Circuit) -> Expression<'a> {
        let mut params = ArenaVec::with_capacity_in(circuit.params.len(), self);
        for p in &circuit.params {
            params.push(FormalParameter::new(
                self.oxc_span(p.span),
                ArenaVec::new_in(self),
                self.binding_ident(self.oxc_span(p.span), &p.name),
                Some(self.ts_type_annotation(self.hir_type_to_ts(&p.ty))),
                None,
                false,
                None,
                false,
                false,
                self,
            ));
        }
        let formal_params = FormalParameters::boxed(
            SPAN,
            FormalParameterKind::ArrowFormalParameters,
            params,
            None,
            self,
        );
        let stmts = self.lower_stmts(circuit);
        let body = FunctionBody::boxed(SPAN, ArenaVec::new_in(self), stmts, self);
        Expression::new_arrow_function_expression(
            self.oxc_span(circuit.span),
            false,
            None,
            formal_params,
            Some(self.ts_type_annotation(self.hir_type_to_ts(&circuit.ret_type))),
            ArrowFunctionBody::FunctionBody(body),
            self,
        )
    }

    fn build_ledger_fn(&self) -> Statement<'a> {
        let mut params = ArenaVec::with_capacity_in(1, self);
        params.push(FormalParameter::new(
            SPAN,
            ArenaVec::new_in(self),
            self.binding_ident(SPAN, "state"),
            Some(self.ts_type_annotation(self.ts_runtime_type("StateValue", None))),
            None,
            false,
            None,
            false,
            false,
            self,
        ));
        let formal_params = FormalParameters::boxed(
            SPAN,
            FormalParameterKind::ArrowFormalParameters,
            params,
            None,
            self,
        );

        let mut props = ArenaVec::new_in(self);
        for field in &self.input.program.ledger_fields {
            if !field.exported {
                continue;
            }
            let decode_fn = match field.adt {
                LedgerAdt::Counter => "decodeCounter",
                LedgerAdt::Cell => "decodeCell",
                LedgerAdt::Set => "decodeSet",
                LedgerAdt::MerkleTree(_) => "decodeMerkleTree",
                LedgerAdt::HistoricMerkleTree(_) => "decodeHistoricMerkleTree",
            };
            let mut args = ArenaVec::with_capacity_in(2, self);
            args.push(Argument::from(self.expr_ident(SPAN, "state")));
            args.push(Argument::from(self.expr_num(SPAN, field.path[0] as f64)));
            let decode_call = self.expr_call(
                self.oxc_span(field.span),
                self.expr_member(SPAN, self.expr_ident(SPAN, "__compactRuntime"), decode_fn),
                args,
            );
            props.push(ObjectPropertyKind::new_object_property(
                self.oxc_span(field.span),
                PropertyKind::Init,
                PropertyKey::StaticIdentifier(IdentifierName::boxed(
                    SPAN,
                    self.ident(&field.name),
                    self,
                )),
                decode_call,
                false,
                false,
                false,
                self,
            ));
        }

        let mut stmts = ArenaVec::with_capacity_in(1, self);
        stmts.push(Statement::new_return_statement(
            SPAN,
            Some(Expression::new_object_expression(SPAN, props, self)),
            self,
        ));
        let body = FunctionBody::boxed(SPAN, ArenaVec::new_in(self), stmts, self);

        let arrow = Expression::new_arrow_function_expression(
            SPAN,
            false,
            None,
            formal_params,
            Some(self.ts_type_annotation(self.ts_type_ref("Ledger", None))),
            ArrowFunctionBody::FunctionBody(body),
            self,
        );

        let mut sig_params = ArenaVec::with_capacity_in(1, self);
        sig_params.push(FormalParameter::new(
            SPAN,
            ArenaVec::new_in(self),
            self.binding_ident(SPAN, "state"),
            Some(self.ts_type_annotation(self.ts_runtime_type("StateValue", None))),
            None,
            false,
            None,
            false,
            false,
            self,
        ));
        let fn_type = TSType::new_ts_function_type(
            SPAN,
            None,
            None,
            FormalParameters::boxed(SPAN, FormalParameterKind::Signature, sig_params, None, self),
            self.ts_type_annotation(self.ts_type_ref("Ledger", None)),
            self,
        );

        self.export_const("ledger", fn_type, arrow)
    }

    fn build_contract_class(&self) -> Statement<'a> {
        let mut class_tparams = ArenaVec::with_capacity_in(2, self);
        class_tparams.push(self.ts_type_param("T"));
        let mut w_targs = ArenaVec::with_capacity_in(1, self);
        w_targs.push(self.ts_type_ref("T", None));
        let mut w_default_targs = ArenaVec::with_capacity_in(1, self);
        w_default_targs.push(self.ts_type_ref("T", None));
        class_tparams.push(TSTypeParameter::new(
            SPAN,
            BindingIdentifier::new(SPAN, self.ident("W"), self),
            Some(self.ts_type_ref("Witnesses", Some(w_targs))),
            Some(self.ts_type_ref("Witnesses", Some(w_default_targs))),
            false,
            false,
            false,
            self,
        ));

        let mut elements = ArenaVec::new_in(self);
        elements.push(self.class_prop("witnesses", self.ts_type_ref("W", None)));

        let mut c_targs = ArenaVec::with_capacity_in(1, self);
        c_targs.push(self.ts_type_ref("T", None));
        elements.push(self.class_prop("circuits", self.ts_type_ref("Circuits", Some(c_targs))));

        let mut ic_targs = ArenaVec::with_capacity_in(1, self);
        ic_targs.push(self.ts_type_ref("T", None));
        elements.push(self.class_prop(
            "impureCircuits",
            self.ts_type_ref("ImpureCircuits", Some(ic_targs)),
        ));

        elements.push(self.build_contract_constructor());
        elements.push(self.build_initial_state_method());

        let class = Class::boxed(
            SPAN,
            ClassType::ClassDeclaration,
            ArenaVec::new_in(self),
            Some(BindingIdentifier::new(SPAN, self.ident("Contract"), self)),
            Some(TSTypeParameterDeclaration::boxed(SPAN, class_tparams, self)),
            None,
            ArenaVec::new_in(self),
            ClassBody::boxed(SPAN, elements, self),
            false,
            false,
            self,
        );
        let decl = Declaration::ClassDeclaration(class);
        Statement::new_export_declaration(SPAN, decl, self)
    }

    fn class_prop(&self, name: &str, ty: TSType<'a>) -> ClassElement<'a> {
        ClassElement::new_property_definition(
            SPAN,
            PropertyDefinitionType::PropertyDefinition,
            ArenaVec::new_in(self),
            PropertyKey::StaticIdentifier(IdentifierName::boxed(SPAN, self.ident(name), self)),
            Some(self.ts_type_annotation(ty)),
            None,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            None,
            self,
        )
    }

    fn build_contract_constructor(&self) -> ClassElement<'a> {
        let mut params = ArenaVec::with_capacity_in(1, self);
        params.push(FormalParameter::new(
            SPAN,
            ArenaVec::new_in(self),
            self.binding_ident(SPAN, "witnesses"),
            Some(self.ts_type_annotation(self.ts_type_ref("W", None))),
            None,
            false,
            None,
            false,
            false,
            self,
        ));
        let formal_params = FormalParameters::boxed(
            SPAN,
            FormalParameterKind::FormalParameter,
            params,
            None,
            self,
        );

        let mut stmts = ArenaVec::new_in(self);
        stmts.push(self.assign_this_prop("witnesses", self.expr_ident(SPAN, "witnesses")));

        let mut impure_props = ArenaVec::new_in(self);
        let mut all_props = ArenaVec::new_in(self);
        for circuit in &self.input.program.circuits {
            if !circuit.exported {
                continue;
            }
            let handler = self.build_exported_circuit_handler(circuit);
            all_props.push(ObjectPropertyKind::new_object_property(
                self.oxc_span(circuit.span),
                PropertyKind::Init,
                PropertyKey::StaticIdentifier(IdentifierName::boxed(
                    SPAN,
                    self.ident(&circuit.name),
                    self,
                )),
                handler,
                false,
                false,
                false,
                self,
            ));

            if !circuit.pure {
                let handler2 = self.build_exported_circuit_handler(circuit);
                impure_props.push(ObjectPropertyKind::new_object_property(
                    self.oxc_span(circuit.span),
                    PropertyKind::Init,
                    PropertyKey::StaticIdentifier(IdentifierName::boxed(
                        SPAN,
                        self.ident(&circuit.name),
                        self,
                    )),
                    handler2,
                    false,
                    false,
                    false,
                    self,
                ));
            }
        }

        stmts.push(self.assign_this_prop(
            "impureCircuits",
            Expression::new_object_expression(SPAN, impure_props, self),
        ));
        stmts.push(self.assign_this_prop(
            "circuits",
            Expression::new_object_expression(SPAN, all_props, self),
        ));

        let body = FunctionBody::boxed(SPAN, ArenaVec::new_in(self), stmts, self);
        let func = Function::boxed(
            SPAN,
            FunctionType::FunctionExpression,
            None,
            false,
            false,
            false,
            None,
            None,
            formal_params,
            None,
            Some(body),
            self,
        );

        ClassElement::new_method_definition(
            SPAN,
            MethodDefinitionType::MethodDefinition,
            ArenaVec::new_in(self),
            PropertyKey::StaticIdentifier(IdentifierName::boxed(
                SPAN,
                self.ident("constructor"),
                self,
            )),
            func,
            MethodDefinitionKind::Constructor,
            false,
            false,
            false,
            false,
            None,
            self,
        )
    }

    fn assign_this_prop(&self, prop: &str, value: Expression<'a>) -> Statement<'a> {
        let target = AssignmentTarget::StaticMemberExpression(StaticMemberExpression::boxed(
            SPAN,
            Expression::new_this_expression(SPAN, self),
            IdentifierName::new(SPAN, self.ident(prop), self),
            false,
            self,
        ));
        Statement::new_expression_statement(
            SPAN,
            Expression::new_assignment_expression(
                SPAN,
                AssignmentOperator::Assign,
                target,
                value,
                self,
            ),
            self,
        )
    }

    fn build_exported_circuit_handler(&self, circuit: &Circuit) -> Expression<'a> {
        let mut params = ArenaVec::with_capacity_in(circuit.params.len() + 1, self);
        let mut ctx_targs = ArenaVec::with_capacity_in(1, self);
        ctx_targs.push(self.ts_type_ref("T", None));
        params.push(FormalParameter::new(
            SPAN,
            ArenaVec::new_in(self),
            self.binding_ident(SPAN, "context"),
            Some(self.ts_type_annotation(self.ts_runtime_type("CircuitContext", Some(ctx_targs)))),
            None,
            false,
            None,
            false,
            false,
            self,
        ));
        for p in &circuit.params {
            params.push(FormalParameter::new(
                self.oxc_span(p.span),
                ArenaVec::new_in(self),
                self.binding_ident(self.oxc_span(p.span), &p.name),
                Some(self.ts_type_annotation(self.hir_type_to_ts(&p.ty))),
                None,
                false,
                None,
                false,
                false,
                self,
            ));
        }
        let formal_params = FormalParameters::boxed(
            SPAN,
            FormalParameterKind::ArrowFormalParameters,
            params,
            None,
            self,
        );

        let mut locals = HashMap::new();
        let (mut stmts, returned) =
            self.lower_stmts_inner(&circuit.params, &circuit.body, &mut locals, true);

        if !returned {
            let empty = Expression::new_array_expression(SPAN, ArenaVec::new_in(self), self);
            stmts.push(self.return_circuit_results(self.oxc_span(circuit.span), empty));
        }

        let mut res_targs = ArenaVec::with_capacity_in(2, self);
        res_targs.push(self.ts_type_ref("T", None));
        res_targs.push(self.hir_type_to_ts(&circuit.ret_type));

        let body = FunctionBody::boxed(SPAN, ArenaVec::new_in(self), stmts, self);
        Expression::new_arrow_function_expression(
            self.oxc_span(circuit.span),
            false,
            None,
            formal_params,
            Some(self.ts_type_annotation(self.ts_runtime_type("CircuitResults", Some(res_targs)))),
            ArrowFunctionBody::FunctionBody(body),
            self,
        )
    }

    fn return_circuit_results(&self, span: Span, result_expr: Expression<'a>) -> Statement<'a> {
        let mut ret_props = ArenaVec::with_capacity_in(2, self);
        ret_props.push(ObjectPropertyKind::new_object_property(
            SPAN,
            PropertyKind::Init,
            PropertyKey::StaticIdentifier(IdentifierName::boxed(SPAN, self.ident("result"), self)),
            result_expr,
            false,
            false,
            false,
            self,
        ));
        ret_props.push(ObjectPropertyKind::new_object_property(
            SPAN,
            PropertyKind::Init,
            PropertyKey::StaticIdentifier(IdentifierName::boxed(SPAN, self.ident("context"), self)),
            self.expr_ident(SPAN, "context"),
            false,
            true,
            false,
            self,
        ));
        Statement::new_return_statement(
            span,
            Some(Expression::new_object_expression(SPAN, ret_props, self)),
            self,
        )
    }

    fn lower_stmts(&self, circuit: &Circuit) -> ArenaVec<'a, Statement<'a>> {
        self.lower_stmts_for(&circuit.params, &circuit.body)
    }

    fn lower_stmts_for(&self, params: &[Param], body: &[Stmt]) -> ArenaVec<'a, Statement<'a>> {
        let mut locals = HashMap::new();
        self.lower_stmts_inner(params, body, &mut locals, false).0
    }

    fn lower_stmts_inner(
        &self,
        params: &[Param],
        body: &[Stmt],
        locals: &mut HashMap<LocalId, String>,
        wrap_circuit_results: bool,
    ) -> (ArenaVec<'a, Statement<'a>>, bool) {
        let mut stmts = ArenaVec::new_in(self);
        let mut returned = false;
        for stmt in body {
            match stmt {
                Stmt::Const {
                    local,
                    name,
                    ty,
                    init,
                    span,
                } => {
                    locals.insert(*local, name.clone());
                    let init_expr = self.lower_expr(params, init, locals);
                    let declarator = VariableDeclarator::new(
                        self.oxc_span(*span),
                        self.binding_ident(self.oxc_span(*span), name),
                        Some(self.ts_type_annotation(self.hir_type_to_ts(ty))),
                        Some(init_expr),
                        false,
                        self,
                    );
                    let mut declarators = ArenaVec::with_capacity_in(1, self);
                    declarators.push(declarator);
                    stmts.push(Statement::from(Declaration::new_variable_declaration(
                        self.oxc_span(*span),
                        VariableDeclarationKind::Const,
                        declarators,
                        false,
                        self,
                    )));
                }
                Stmt::If {
                    cond,
                    then_branch,
                    else_branch,
                    span,
                } => {
                    let test = self.lower_expr(params, cond, locals);
                    let mut then_locals = locals.clone();
                    let (then_stmts, then_ret) = self.lower_stmts_inner(
                        params,
                        then_branch,
                        &mut then_locals,
                        wrap_circuit_results,
                    );
                    let consequent = Statement::new_block_statement(SPAN, then_stmts, self);
                    let (alternate, else_ret) = if else_branch.is_empty() {
                        (None, false)
                    } else {
                        let mut else_locals = locals.clone();
                        let (else_stmts, er) = self.lower_stmts_inner(
                            params,
                            else_branch,
                            &mut else_locals,
                            wrap_circuit_results,
                        );
                        (Some(Statement::new_block_statement(SPAN, else_stmts, self)), er)
                    };
                    if then_ret && else_ret {
                        returned = true;
                    }
                    stmts.push(Statement::new_if_statement(
                        self.oxc_span(*span),
                        test,
                        consequent,
                        alternate,
                        self,
                    ));
                }
                Stmt::Expr(expr) => {
                    stmts.push(Statement::new_expression_statement(
                        self.oxc_span(expr.span),
                        self.lower_expr(params, expr, locals),
                        self,
                    ));
                }
                Stmt::Return { value, span } => {
                    returned = true;
                    if wrap_circuit_results {
                        let result_expr = value
                            .as_ref()
                            .map(|e| self.lower_expr(params, e, locals))
                            .unwrap_or_else(|| {
                                Expression::new_array_expression(SPAN, ArenaVec::new_in(self), self)
                            });
                        stmts.push(self.return_circuit_results(self.oxc_span(*span), result_expr));
                    } else {
                        stmts.push(Statement::new_return_statement(
                            self.oxc_span(*span),
                            value.as_ref().map(|e| self.lower_expr(params, e, locals)),
                            self,
                        ));
                    }
                }
            }
        }
        (stmts, returned)
    }

    fn default_expr_for_type(&self, span: Span, ty: &Type) -> Expression<'a> {
        match ty {
            Type::Field | Type::Uint(_) => Expression::new_big_int_literal(
                span,
                self.str_atom("0"),
                None,
                oxc_syntax::number::BigintBase::Decimal,
                self,
            ),
            Type::Boolean => self.expr_bool(span, false),
            Type::Opaque(ts_ty) => {
                if ts_ty == "string" {
                    self.expr_str(span, "")
                } else {
                    let mut args = ArenaVec::with_capacity_in(1, self);
                    args.push(Argument::from(self.expr_num(span, 0.0)));
                    Expression::new_new_expression(
                        span,
                        self.expr_ident(span, ts_ty),
                        None,
                        args,
                        self,
                    )
                }
            }
            Type::Bytes(len) => {
                let mut args = ArenaVec::with_capacity_in(1, self);
                args.push(Argument::from(self.expr_num(span, *len as f64)));
                Expression::new_new_expression(
                    span,
                    self.expr_ident(span, "Uint8Array"),
                    None,
                    args,
                    self,
                )
            }
            Type::Enum(id) => {
                let decl = self.input.program.enum_decl(*id);
                self.expr_member(span, self.expr_ident(span, &decl.name), &decl.variants[0])
            }
            Type::Tuple(elems) => {
                let mut arr = ArenaVec::with_capacity_in(elems.len(), self);
                for e in elems {
                    arr.push(ArrayExpressionElement::from(
                        self.default_expr_for_type(span, e),
                    ));
                }
                Expression::new_array_expression(span, arr, self)
            }
            Type::Vector(len, elem) => {
                let mut arr = ArenaVec::with_capacity_in(*len as usize, self);
                for _ in 0..*len {
                    arr.push(ArrayExpressionElement::from(
                        self.default_expr_for_type(span, elem),
                    ));
                }
                Expression::new_array_expression(span, arr, self)
            }
            Type::Struct(_)
            | Type::Maybe(_)
            | Type::MerkleTreeDigest
            | Type::MerkleTreePathEntry
            | Type::MerkleTreePath(_, _) => {
                let fields = self
                    .input
                    .program
                    .struct_fields_of(ty)
                    .unwrap_or_default();
                let mut props = ArenaVec::with_capacity_in(fields.len(), self);
                for (fname, fty) in fields {
                    props.push(ObjectPropertyKind::new_object_property(
                        span,
                        PropertyKind::Init,
                        PropertyKey::StaticIdentifier(IdentifierName::boxed(
                            span,
                            self.ident(&fname),
                            self,
                        )),
                        self.default_expr_for_type(span, &fty),
                        false,
                        false,
                        false,
                        self,
                    ));
                }
                Expression::new_object_expression(span, props, self)
            }
        }
    }

    fn lower_expr(
        &self,
        params: &[Param],
        expr: &Expr,
        locals: &HashMap<LocalId, String>,
    ) -> Expression<'a> {
        let span = self.oxc_span(expr.span);
        match &expr.kind {
            ExprKind::IntLit(v) => Expression::new_big_int_literal(
                span,
                self.str_atom(&v.to_string()),
                None,
                oxc_syntax::number::BigintBase::Decimal,
                self,
            ),
            ExprKind::BoolLit(b) => self.expr_bool(span, *b),
            ExprKind::BytesLit(bytes) => {
                let mut elems = ArenaVec::with_capacity_in(bytes.len(), self);
                for &b in bytes {
                    elems.push(ArrayExpressionElement::from(self.expr_num(span, b as f64)));
                }
                let mut args = ArenaVec::with_capacity_in(1, self);
                args.push(Argument::from(Expression::new_array_expression(
                    span, elems, self,
                )));
                Expression::new_new_expression(
                    span,
                    self.expr_ident(span, "Uint8Array"),
                    None,
                    args,
                    self,
                )
            }
            ExprKind::Default(ty) => self.default_expr_for_type(span, ty),
            ExprKind::ParamRef(pid) => self.expr_ident(span, &params[pid.0 as usize].name),
            ExprKind::LocalRef(lid) => self.expr_ident(span, &locals[lid]),
            ExprKind::EnumVariant {
                enum_id,
                variant_idx,
            } => {
                let decl = self.input.program.enum_decl(*enum_id);
                self.expr_member(
                    span,
                    self.expr_ident(span, &decl.name),
                    &decl.variants[*variant_idx as usize],
                )
            }
            ExprKind::Tuple(elems) | ExprKind::Vector(elems) => {
                let mut arr = ArenaVec::with_capacity_in(elems.len(), self);
                for elem in elems {
                    arr.push(ArrayExpressionElement::from(
                        self.lower_expr(params, elem, locals),
                    ));
                }
                Expression::new_array_expression(span, arr, self)
            }
            ExprKind::Unary { op, operand } => {
                let uop = match op {
                    UnaryOp::Not => UnaryOperator::LogicalNot,
                    UnaryOp::Neg => UnaryOperator::UnaryNegation,
                };
                Expression::new_unary_expression(
                    span,
                    uop,
                    self.lower_expr(params, operand, locals),
                    self,
                )
            }
            ExprKind::Binary { op, lhs, rhs } => {
                if matches!(op, BinaryOp::And | BinaryOp::Or) {
                    let lop = if *op == BinaryOp::And {
                        LogicalOperator::And
                    } else {
                        LogicalOperator::Or
                    };
                    return Expression::new_logical_expression(
                        span,
                        self.lower_expr(params, lhs, locals),
                        lop,
                        self.lower_expr(params, rhs, locals),
                        self,
                    );
                }
                if matches!(op, BinaryOp::Eq | BinaryOp::Neq)
                    && matches!(
                        lhs.ty,
                        Type::Bytes(_)
                            | Type::Vector(_, _)
                            | Type::Tuple(_)
                            | Type::Struct(_)
                            | Type::Maybe(_)
                            | Type::MerkleTreeDigest
                            | Type::MerkleTreePathEntry
                            | Type::MerkleTreePath(_, _)
                    )
                {
                    let mut eq_args = ArenaVec::with_capacity_in(2, self);
                    eq_args.push(Argument::from(self.lower_expr(params, lhs, locals)));
                    eq_args.push(Argument::from(self.lower_expr(params, rhs, locals)));
                    let eq_call = self.expr_call(
                        span,
                        self.expr_member(span, self.expr_ident(span, "__compactRuntime"), "equal"),
                        eq_args,
                    );
                    return if matches!(op, BinaryOp::Neq) {
                        Expression::new_unary_expression(
                            span,
                            UnaryOperator::LogicalNot,
                            eq_call,
                            self,
                        )
                    } else {
                        eq_call
                    };
                }
                let bin_op = match op {
                    BinaryOp::Add => BinaryOperator::Addition,
                    BinaryOp::Sub => BinaryOperator::Subtraction,
                    BinaryOp::Eq => BinaryOperator::StrictEquality,
                    BinaryOp::Neq => BinaryOperator::StrictInequality,
                    BinaryOp::And | BinaryOp::Or => unreachable!(),
                };
                Expression::new_binary_expression(
                    span,
                    self.lower_expr(params, lhs, locals),
                    bin_op,
                    self.lower_expr(params, rhs, locals),
                    self,
                )
            }
            ExprKind::Ternary {
                cond,
                then_branch,
                else_branch,
            } => Expression::new_conditional_expression(
                span,
                self.lower_expr(params, cond, locals),
                self.lower_expr(params, then_branch, locals),
                self.lower_expr(params, else_branch, locals),
                self,
            ),
            ExprKind::Cast { expr, .. } | ExprKind::Disclose(expr) => {
                self.lower_expr(params, expr, locals)
            }
            ExprKind::Assert { cond, message } => {
                let mut args = ArenaVec::with_capacity_in(2, self);
                args.push(Argument::from(self.lower_expr(params, cond, locals)));
                args.push(Argument::from(self.expr_str(span, message)));
                self.expr_call(
                    span,
                    self.expr_member(span, self.expr_ident(span, "__compactRuntime"), "assert"),
                    args,
                )
            }
            ExprKind::WitnessCall { witness, args } => {
                let w = self.input.program.witness(*witness);
                let witness_fn = self.expr_member(
                    span,
                    self.expr_member(
                        span,
                        Expression::new_this_expression(span, self),
                        "witnesses",
                    ),
                    &w.name,
                );
                let mut call_args = ArenaVec::with_capacity_in(args.len() + 2, self);
                call_args.push(Argument::from(witness_fn));
                call_args.push(Argument::from(self.expr_ident(span, "context")));
                for a in args {
                    call_args.push(Argument::from(self.lower_expr(params, a, locals)));
                }
                self.expr_call(
                    span,
                    self.expr_member(
                        span,
                        self.expr_ident(span, "__compactRuntime"),
                        "callWitness",
                    ),
                    call_args,
                )
            }
            ExprKind::PersistentHash { arg, .. } => {
                let mut call_args = ArenaVec::with_capacity_in(1, self);
                call_args.push(Argument::from(self.lower_expr(params, arg, locals)));
                self.expr_call(
                    span,
                    self.expr_member(
                        span,
                        self.expr_ident(span, "__compactRuntime"),
                        "persistentHash",
                    ),
                    call_args,
                )
            }
            ExprKind::MerkleTreePathRoot { path, .. } => {
                let mut call_args = ArenaVec::with_capacity_in(1, self);
                call_args.push(Argument::from(self.lower_expr(params, path, locals)));
                self.expr_call(
                    span,
                    self.expr_member(
                        span,
                        self.expr_ident(span, "__compactRuntime"),
                        "merkleTreePathRoot",
                    ),
                    call_args,
                )
            }
            ExprKind::StructLit { fields } => {
                let mut props = ArenaVec::with_capacity_in(fields.len(), self);
                for (fname, fexpr) in fields {
                    props.push(ObjectPropertyKind::new_object_property(
                        span,
                        PropertyKind::Init,
                        PropertyKey::StaticIdentifier(IdentifierName::boxed(
                            span,
                            self.ident(fname),
                            self,
                        )),
                        self.lower_expr(params, fexpr, locals),
                        false,
                        false,
                        false,
                        self,
                    ));
                }
                Expression::new_object_expression(span, props, self)
            }
            ExprKind::FieldAccess { base, field } => {
                self.expr_member(span, self.lower_expr(params, base, locals), field)
            }
            ExprKind::MaybeSome(inner) => {
                let mut props = ArenaVec::with_capacity_in(2, self);
                props.push(ObjectPropertyKind::new_object_property(
                    span,
                    PropertyKind::Init,
                    PropertyKey::StaticIdentifier(IdentifierName::boxed(
                        span,
                        self.ident("is_some"),
                        self,
                    )),
                    self.expr_bool(span, true),
                    false,
                    false,
                    false,
                    self,
                ));
                props.push(ObjectPropertyKind::new_object_property(
                    span,
                    PropertyKind::Init,
                    PropertyKey::StaticIdentifier(IdentifierName::boxed(
                        span,
                        self.ident("value"),
                        self,
                    )),
                    self.lower_expr(params, inner, locals),
                    false,
                    false,
                    false,
                    self,
                ));
                Expression::new_object_expression(span, props, self)
            }
            ExprKind::MaybeNone(inner_ty) => {
                let mut props = ArenaVec::with_capacity_in(2, self);
                props.push(ObjectPropertyKind::new_object_property(
                    span,
                    PropertyKind::Init,
                    PropertyKey::StaticIdentifier(IdentifierName::boxed(
                        span,
                        self.ident("is_some"),
                        self,
                    )),
                    self.expr_bool(span, false),
                    false,
                    false,
                    false,
                    self,
                ));
                props.push(ObjectPropertyKind::new_object_property(
                    span,
                    PropertyKind::Init,
                    PropertyKey::StaticIdentifier(IdentifierName::boxed(
                        span,
                        self.ident("value"),
                        self,
                    )),
                    self.default_expr_for_type(span, inner_ty),
                    false,
                    false,
                    false,
                    self,
                ));
                Expression::new_object_expression(span, props, self)
            }
            ExprKind::CircuitCall {
                circuit: callee_id,
                args,
            } => {
                let callee = self.input.program.circuit(*callee_id);
                let mut call_args = ArenaVec::new_in(self);
                if !callee.pure {
                    call_args.push(Argument::from(self.expr_ident(span, "context")));
                }
                for a in args {
                    call_args.push(Argument::from(self.lower_expr(params, a, locals)));
                }
                self.expr_call(
                    span,
                    self.expr_ident(span, &format!("_{}", callee.name)),
                    call_args,
                )
            }
            ExprKind::LedgerCall { field, op, args } => {
                let ledger_field = self.input.program.ledger_field(*field);
                match op {
                    LedgerOp::CellRead => {
                        let mut call_args = ArenaVec::with_capacity_in(2, self);
                        call_args.push(Argument::from(self.expr_ident(span, "context")));
                        call_args.push(Argument::from(
                            self.expr_num(span, ledger_field.path[0] as f64),
                        ));
                        self.expr_call(
                            span,
                            self.expr_member(
                                span,
                                self.expr_ident(span, "__compactRuntime"),
                                "readCell",
                            ),
                            call_args,
                        )
                    }
                    LedgerOp::CellWrite => {
                        let mut call_args = ArenaVec::with_capacity_in(3, self);
                        call_args.push(Argument::from(self.expr_ident(span, "context")));
                        call_args.push(Argument::from(
                            self.expr_num(span, ledger_field.path[0] as f64),
                        ));
                        call_args.push(Argument::from(self.lower_expr(params, &args[0], locals)));
                        self.expr_call(
                            span,
                            self.expr_member(
                                span,
                                self.expr_ident(span, "__compactRuntime"),
                                "writeCell",
                            ),
                            call_args,
                        )
                    }
                    LedgerOp::CounterIncrement | LedgerOp::CounterDecrement => {
                        let amount = match args.first().map(|a| &a.kind) {
                            Some(ExprKind::IntLit(v)) => *v as f64,
                            _ => 0.0,
                        };
                        let op_key = if matches!(op, LedgerOp::CounterIncrement) {
                            "addi"
                        } else {
                            "subi"
                        };
                        let mut ops = ArenaVec::with_capacity_in(3, self);
                        ops.push(ArrayExpressionElement::from(self.make_vm_op(
                            "idx",
                            vec![
                                ("cached", self.expr_bool(span, false)),
                                ("pushPath", self.expr_bool(span, true)),
                                ("path", self.expr_num(span, ledger_field.path[0] as f64)),
                            ],
                        )));
                        ops.push(ArrayExpressionElement::from(self.make_vm_op(
                            op_key,
                            vec![("immediate", self.expr_num(span, amount))],
                        )));
                        ops.push(ArrayExpressionElement::from(self.make_vm_op(
                            "ins",
                            vec![
                                ("cached", self.expr_bool(span, true)),
                                ("n", self.expr_num(span, ledger_field.path.len() as f64)),
                            ],
                        )));
                        let mut call_args = ArenaVec::with_capacity_in(2, self);
                        call_args.push(Argument::from(self.expr_ident(span, "context")));
                        call_args.push(Argument::from(Expression::new_array_expression(
                            span, ops, self,
                        )));
                        self.expr_call(
                            span,
                            self.expr_member(
                                span,
                                self.expr_ident(span, "__compactRuntime"),
                                "queryLedger",
                            ),
                            call_args,
                        )
                    }
                    LedgerOp::CounterRead => {
                        let mut call_args = ArenaVec::with_capacity_in(2, self);
                        call_args.push(Argument::from(self.expr_ident(span, "context")));
                        call_args.push(Argument::from(
                            self.expr_num(span, ledger_field.path[0] as f64),
                        ));
                        self.expr_call(
                            span,
                            self.expr_member(
                                span,
                                self.expr_ident(span, "__compactRuntime"),
                                "readCounter",
                            ),
                            call_args,
                        )
                    }
                    LedgerOp::SetMember
                    | LedgerOp::SetInsert
                    | LedgerOp::SetRemove
                    | LedgerOp::MerkleTreeInsert
                    | LedgerOp::MerkleTreeCheckRoot
                    | LedgerOp::HistoricMerkleTreeInsert
                    | LedgerOp::HistoricMerkleTreeCheckRoot => {
                        let rt_fn = match op {
                            LedgerOp::SetMember => "setMember",
                            LedgerOp::SetInsert => "setInsert",
                            LedgerOp::SetRemove => "setRemove",
                            LedgerOp::MerkleTreeInsert => "merkleTreeInsert",
                            LedgerOp::MerkleTreeCheckRoot => "merkleTreeCheckRoot",
                            LedgerOp::HistoricMerkleTreeInsert => "historicMerkleTreeInsert",
                            LedgerOp::HistoricMerkleTreeCheckRoot => "historicMerkleTreeCheckRoot",
                            _ => unreachable!(),
                        };
                        let mut call_args = ArenaVec::with_capacity_in(3, self);
                        call_args.push(Argument::from(self.expr_ident(span, "context")));
                        call_args.push(Argument::from(
                            self.expr_num(span, ledger_field.path[0] as f64),
                        ));
                        call_args.push(Argument::from(self.lower_expr(params, &args[0], locals)));
                        self.expr_call(
                            span,
                            self.expr_member(span, self.expr_ident(span, "__compactRuntime"), rt_fn),
                            call_args,
                        )
                    }
                }
            }
        }
    }

    fn make_vm_op(&self, name: &str, fields: Vec<(&str, Expression<'a>)>) -> Expression<'a> {
        let mut inner_props = ArenaVec::with_capacity_in(fields.len(), self);
        for (k, v) in fields {
            inner_props.push(ObjectPropertyKind::new_object_property(
                SPAN,
                PropertyKind::Init,
                PropertyKey::StaticIdentifier(IdentifierName::boxed(SPAN, self.ident(k), self)),
                v,
                false,
                false,
                false,
                self,
            ));
        }
        let mut outer_props = ArenaVec::with_capacity_in(1, self);
        outer_props.push(ObjectPropertyKind::new_object_property(
            SPAN,
            PropertyKind::Init,
            PropertyKey::StaticIdentifier(IdentifierName::boxed(SPAN, self.ident(name), self)),
            Expression::new_object_expression(SPAN, inner_props, self),
            false,
            false,
            false,
            self,
        ));
        Expression::new_object_expression(SPAN, outer_props, self)
    }

    fn build_initial_state_method(&self) -> ClassElement<'a> {
        let ctor = self.input.program.constructor.as_ref();
        let extra_params = ctor.map_or(0, |c| c.params.len());
        let mut params = ArenaVec::with_capacity_in(1 + extra_params, self);
        let mut ctx_targs = ArenaVec::with_capacity_in(1, self);
        ctx_targs.push(self.ts_type_ref("T", None));
        params.push(FormalParameter::new(
            SPAN,
            ArenaVec::new_in(self),
            self.binding_ident(SPAN, "context"),
            Some(self.ts_type_annotation(
                self.ts_runtime_type("ConstructorContext", Some(ctx_targs)),
            )),
            None,
            false,
            None,
            false,
            false,
            self,
        ));
        if let Some(ctor) = ctor {
            for p in &ctor.params {
                params.push(FormalParameter::new(
                    self.oxc_span(p.span),
                    ArenaVec::new_in(self),
                    self.binding_ident(self.oxc_span(p.span), &p.name),
                    Some(self.ts_type_annotation(self.hir_type_to_ts(&p.ty))),
                    None,
                    false,
                    None,
                    false,
                    false,
                    self,
                ));
            }
        }
        let formal_params = FormalParameters::boxed(
            SPAN,
            FormalParameterKind::FormalParameter,
            params,
            None,
            self,
        );

        let mut ret_targs = ArenaVec::with_capacity_in(1, self);
        ret_targs.push(self.ts_type_ref("T", None));
        let ret_ty = self.ts_runtime_type("ConstructorResult", Some(ret_targs));

        let mut stmts = if let Some(ctor) = ctor {
            self.lower_stmts_for(&ctor.params, &ctor.body)
        } else {
            ArenaVec::new_in(self)
        };
        let mut call_args = ArenaVec::with_capacity_in(1, self);
        call_args.push(Argument::from(self.expr_ident(SPAN, "context")));
        let call = self.expr_call(
            SPAN,
            self.expr_member(
                SPAN,
                self.expr_ident(SPAN, "__compactRuntime"),
                "emptyContractState",
            ),
            call_args,
        );
        stmts.push(Statement::new_return_statement(SPAN, Some(call), self));
        let body = FunctionBody::boxed(SPAN, ArenaVec::new_in(self), stmts, self);

        let func = Function::boxed(
            SPAN,
            FunctionType::FunctionExpression,
            None,
            false,
            false,
            false,
            None,
            None,
            formal_params,
            Some(self.ts_type_annotation(ret_ty)),
            Some(body),
            self,
        );

        ClassElement::new_method_definition(
            SPAN,
            MethodDefinitionType::MethodDefinition,
            ArenaVec::new_in(self),
            PropertyKey::StaticIdentifier(IdentifierName::boxed(
                SPAN,
                self.ident("initialState"),
                self,
            )),
            func,
            MethodDefinitionKind::Method,
            false,
            false,
            false,
            false,
            None,
            self,
        )
    }

    fn build_expected_vk_const(&self) -> Statement<'a> {
        let mut props = ArenaVec::with_capacity_in(self.input.verifier_key_hashes.len(), self);
        for (name, hash) in self.input.verifier_key_hashes {
            props.push(ObjectPropertyKind::new_object_property(
                SPAN,
                PropertyKind::Init,
                PropertyKey::StaticIdentifier(IdentifierName::boxed(SPAN, self.ident(name), self)),
                self.expr_str(SPAN, hash),
                false,
                false,
                false,
                self,
            ));
        }
        let mut rec_args = ArenaVec::with_capacity_in(2, self);
        rec_args.push(TSType::new_ts_string_keyword(SPAN, self));
        rec_args.push(TSType::new_ts_string_keyword(SPAN, self));
        let ty = self.ts_type_ref("Record", Some(rec_args));
        self.export_const(
            "_expectedVk",
            ty,
            Expression::new_object_expression(SPAN, props, self),
        )
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use compact_parser::parse;
    use compact_sema::check;
    use compact_span::SourceMap;
    use compact_test_utils::assert_compact_snapshot;

    use super::{TsCodegenInput, generate_ts};

    fn compile_ts_bundle(src: &str) -> String {
        let mut sm = SourceMap::new();
        let id = sm.add_file("contract.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let checked = check(file, &parsed.ast);
        assert!(
            !checked.diagnostics.has_errors(),
            "unexpected sema errors: {:?}",
            checked.diagnostics
        );
        let hashes = BTreeMap::new();
        let out = generate_ts(&TsCodegenInput {
            program: &checked.program,
            source_name: "contract.compact",
            source_text: src,
            verifier_key_hashes: &hashes,
        })
        .unwrap();
        format!(
            "=== index.ts ===\n{}\n=== index.js ===\n{}\n=== index.d.ts ===\n{}",
            out.ts, out.js, out.dts
        )
    }

    #[test]
    fn codegen_counter_ts_js_dts() {
        assert_compact_snapshot!(
            r#"
            import CompactStandardLibrary;

            export ledger round: Counter;

            export circuit increment(): [] {
              round.increment(1);
            }
            "#,
            compile_ts_bundle
        );
    }

    #[test]
    fn codegen_cell_enum_ts_js_dts() {
        assert_compact_snapshot!(
            r#"
            import CompactStandardLibrary;

            export enum STATE { unset, set }

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
              return in_state(STATE.set) ? value : 0 as Field;
            }
            "#,
            compile_ts_bundle
        );
    }

    #[test]
    fn codegen_tiny_contract() {
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
            compile_ts_bundle
        );
    }

    #[test]
    fn codegen_election_contract() {
        assert_compact_snapshot!(
            file: include_str!("../../../examples/election.compact"),
            compile_ts_bundle
        );
    }

    #[test]
    fn codegen_zerocash_contract() {
        assert_compact_snapshot!(
            file: include_str!("../../../examples/zerocash.compact"),
            compile_ts_bundle
        );
    }
}
