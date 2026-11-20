use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use compact_hir::{BinaryOp, Circuit, Expr, ExprKind, LedgerAdt, LedgerOp, Program as HirProgram, Stmt, Type};
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
use oxc_syntax::operator::{AssignmentOperator, BinaryOperator};
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
    let sem_ret = SemanticBuilder::new().build(&ts_program);
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
            Type::Tuple(elems) => {
                let mut ts_elems = ArenaVec::with_capacity_in(elems.len(), self);
                for elem in elems {
                    ts_elems.push(TSTupleElement::from(self.hir_type_to_ts(elem)));
                }
                TSType::new_ts_tuple_type(SPAN, ts_elems, self)
            }
            Type::Adt(LedgerAdt::Counter) => TSType::new_ts_big_int_keyword(SPAN, self),
        }
    }

    fn build_program(&self) -> Program<'a> {
        let mut body = ArenaVec::new_in(self);

        // import * as __compactRuntime from '@midnight-ntwrk/compact-runtime';
        body.push(self.build_runtime_import());

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
        let empty_obj = TSType::new_ts_type_literal(SPAN, ArenaVec::new_in(self), self);
        self.export_type_alias("Witnesses", Some(tparams), empty_obj)
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
                Some(self.ts_type_annotation(self.hir_type_to_ts(&field.ty))),
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
        let mut stmts = ArenaVec::new_in(self);
        for stmt in &circuit.body {
            stmts.push(self.lower_stmt(circuit, stmt));
        }
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
            // __compactRuntime.decodeCounter(state, <idx>)
            let mut args = ArenaVec::with_capacity_in(2, self);
            args.push(Argument::from(self.expr_ident(SPAN, "state")));
            args.push(Argument::from(self.expr_num(SPAN, field.path[0] as f64)));
            let decode_call = self.expr_call(
                self.oxc_span(field.span),
                self.expr_member(
                    SPAN,
                    self.expr_ident(SPAN, "__compactRuntime"),
                    "decodeCounter",
                ),
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

        // Build explicit function type for isolatedDeclarations compatibility:
        // (state: __compactRuntime.StateValue) => Ledger
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

        // witnesses: W;
        elements.push(self.class_prop("witnesses", self.ts_type_ref("W", None)));

        // circuits: Circuits<T>;
        let mut c_targs = ArenaVec::with_capacity_in(1, self);
        c_targs.push(self.ts_type_ref("T", None));
        elements.push(self.class_prop("circuits", self.ts_type_ref("Circuits", Some(c_targs))));

        // impureCircuits: ImpureCircuits<T>;
        let mut ic_targs = ArenaVec::with_capacity_in(1, self);
        ic_targs.push(self.ts_type_ref("T", None));
        elements.push(self.class_prop(
            "impureCircuits",
            self.ts_type_ref("ImpureCircuits", Some(ic_targs)),
        ));

        // constructor(witnesses: W) { ... }
        elements.push(self.build_contract_constructor());

        // initialState(context: __compactRuntime.ConstructorContext<T>): __compactRuntime.ConstructorResult<T>
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

        // this.witnesses = witnesses;
        stmts.push(self.assign_this_prop("witnesses", self.expr_ident(SPAN, "witnesses")));

        // Build object literal of impure circuit handlers
        let mut impure_props = ArenaVec::new_in(self);
        let mut all_props = ArenaVec::new_in(self);
        for circuit in &self.input.program.circuits {
            if !circuit.exported {
                continue;
            }
            let handler = self.build_impure_or_wrapped_circuit(circuit);
            let prop_for_all = ObjectPropertyKind::new_object_property(
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
            );
            all_props.push(prop_for_all);

            if !circuit.pure {
                let handler2 = self.build_impure_or_wrapped_circuit(circuit);
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

    fn build_impure_or_wrapped_circuit(&self, circuit: &Circuit) -> Expression<'a> {
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

        let mut stmts = ArenaVec::new_in(self);
        for stmt in &circuit.body {
            if let Stmt::Expr(expr) = stmt {
                stmts.push(self.lower_impure_expr_stmt(expr));
            }
        }

        // return { result: [], context, proofData: { input: [], output: [], publicTranscript: [], privateTranscriptOutputs: [] } };
        let result_expr = if let Some(Stmt::Return {
            value: Some(expr), ..
        }) = circuit.body.last()
        {
            self.lower_expr(circuit, expr)
        } else {
            Expression::new_array_expression(SPAN, ArenaVec::new_in(self), self)
        };

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
        stmts.push(Statement::new_return_statement(
            self.oxc_span(circuit.span),
            Some(Expression::new_object_expression(SPAN, ret_props, self)),
            self,
        ));

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

    fn lower_impure_expr_stmt(&self, expr: &Expr) -> Statement<'a> {
        let span = self.oxc_span(expr.span);
        if let ExprKind::LedgerCall { field, op, args } = &expr.kind {
            let ledger_field = self.input.program.ledger_field(*field);
            let mut ops = ArenaVec::new_in(self);
            match op {
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

                    // { idx: { cached: false, pushPath: true, path: [{ tag: 'value', value: { value: [new Uint8Array([0])], alignment: [{ tag: 'atom', value: { tag: 'bytes', length: 1 } }] } }] } }
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
                }
                LedgerOp::CounterRead => {
                    ops.push(ArrayExpressionElement::from(self.make_vm_op(
                        "idx",
                        vec![
                            ("cached", self.expr_bool(span, false)),
                            ("pushPath", self.expr_bool(span, false)),
                            ("path", self.expr_num(span, ledger_field.path[0] as f64)),
                        ],
                    )));
                }
            }

            // __compactRuntime.queryLedger(context, [...ops]);
            let mut call_args = ArenaVec::with_capacity_in(2, self);
            call_args.push(Argument::from(self.expr_ident(span, "context")));
            call_args.push(Argument::from(Expression::new_array_expression(span, ops, self)));
            let call = self.expr_call(
                span,
                self.expr_member(span, self.expr_ident(span, "__compactRuntime"), "queryLedger"),
                call_args,
            );
            return Statement::new_expression_statement(span, call, self);
        }

        Statement::new_expression_statement(span, Expression::new_void_0(span, self), self)
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
        let mut params = ArenaVec::with_capacity_in(1, self);
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
        let mut stmts = ArenaVec::with_capacity_in(1, self);
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

    fn lower_stmt(&self, circuit: &Circuit, stmt: &Stmt) -> Statement<'a> {
        match stmt {
            Stmt::Expr(expr) => {
                Statement::new_expression_statement(self.oxc_span(expr.span), self.lower_expr(circuit, expr), self)
            }
            Stmt::Return { value, span } => Statement::new_return_statement(
                self.oxc_span(*span),
                value.as_ref().map(|e| self.lower_expr(circuit, e)),
                self,
            ),
        }
    }

    fn lower_expr(&self, circuit: &Circuit, expr: &Expr) -> Expression<'a> {
        let span = self.oxc_span(expr.span);
        match &expr.kind {
            ExprKind::IntLit(v) => Expression::new_big_int_literal(
                span,
                self.str_atom(&v.to_string()),
                None,
                oxc_syntax::number::BigintBase::Decimal,
                self,
            ),
            ExprKind::ParamRef(pid) => {
                self.expr_ident(span, &circuit.params[pid.0 as usize].name)
            }
            ExprKind::Tuple(elems) => {
                let mut arr = ArenaVec::with_capacity_in(elems.len(), self);
                for elem in elems {
                    arr.push(ArrayExpressionElement::from(self.lower_expr(circuit, elem)));
                }
                Expression::new_array_expression(span, arr, self)
            }
            ExprKind::Binary { op, lhs, rhs } => {
                let bin_op = match op {
                    BinaryOp::Add => BinaryOperator::Addition,
                    BinaryOp::Sub => BinaryOperator::Subtraction,
                };
                Expression::new_binary_expression(
                    span,
                    self.lower_expr(circuit, lhs),
                    bin_op,
                    self.lower_expr(circuit, rhs),
                    self,
                )
            }
            ExprKind::LedgerCall { .. } => Expression::new_void_0(span, self),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use compact_hir::lower;
    use compact_parser::parse;
    use compact_span::SourceMap;
    use compact_test_utils::assert_compact_snapshot;

    use super::{TsCodegenInput, generate_ts};

    fn compile_ts_bundle(src: &str) -> String {
        let mut sm = SourceMap::new();
        let id = sm.add_file("counter.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let lowered = lower(file, &parsed.ast);
        assert!(!lowered.diagnostics.has_errors());
        let hashes = BTreeMap::new();
        let out = generate_ts(&TsCodegenInput {
            program: &lowered.program,
            source_name: "counter.compact",
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
}
