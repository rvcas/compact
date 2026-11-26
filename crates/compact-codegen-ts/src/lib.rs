// This file is part of Compact.
// Copyright (C) 2025 Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::{Path, PathBuf};

use compact_hir::{
    BinaryOp, Circuit, CircuitId, CurveFieldKind, CurveKind, EnumDecl, Expr, ExprKind, LedgerAdt,
    LedgerOp, LocalId, NewTypeDecl, Param, Program as HirProgram, Stmt, StructDecl, Type, UnaryOp,
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
    let dts_ret = IsolatedDeclarations::new(&allocator, IsolatedDeclarationsOptions::default())
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
    let sem_ret = SemanticBuilder::new()
        .with_enum_eval(true)
        .build(&ts_program);
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
        TSType::new_ts_type_reference(
            SPAN,
            TSTypeName::QualifiedName(qualified),
            type_arguments,
            self,
        )
    }

    fn ts_type_annotation(
        &self,
        ty: TSType<'a>,
    ) -> oxc_allocator::ArenaBox<'a, TSTypeAnnotation<'a>> {
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
            Type::Field | Type::Uint(_) | Type::CurveField(_) => {
                TSType::new_ts_big_int_keyword(SPAN, self)
            }
            Type::CurvePoint(curve) => self.ts_runtime_type(curve.point_type_name(), None),
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
            Type::NewType(id) => {
                let decl = self.input.program.new_type_decl(*id);
                self.ts_type_ref(&decl.name, None)
            }
            Type::Contract(_) => {
                let mut members = ArenaVec::with_capacity_in(1, self);
                members.push(TSSignature::new_ts_property_signature(
                    SPAN,
                    false,
                    false,
                    false,
                    PropertyKey::StaticIdentifier(IdentifierName::boxed(
                        SPAN,
                        self.ident("bytes"),
                        self,
                    )),
                    Some(self.ts_type_annotation(self.ts_type_ref("Uint8Array", None))),
                    self,
                ));
                TSType::new_ts_type_literal(SPAN, members, self)
            }
            Type::Maybe(inner) => {
                let mut targs = ArenaVec::with_capacity_in(1, self);
                targs.push(self.hir_type_to_ts(inner));
                self.ts_type_ref("Maybe", Some(targs))
            }
            Type::Either(left, right) => {
                let mut targs = ArenaVec::with_capacity_in(2, self);
                targs.push(self.hir_type_to_ts(left));
                targs.push(self.hir_type_to_ts(right));
                self.ts_type_ref("Either", Some(targs))
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
                ExprKind::ContractCall { receiver, args, .. } => {
                    visit_expr(receiver, out);
                    for a in args {
                        visit_expr(a, out);
                    }
                }
                ExprKind::Emit { value, .. } => visit_expr(value, out),
                ExprKind::Serialize { value, .. } => visit_expr(value, out),
                ExprKind::Deserialize { bytes, .. } => visit_expr(bytes, out),
                ExprKind::Tuple(es) | ExprKind::Vector(es) | ExprKind::BytesPack(es) => {
                    for e in es {
                        visit_expr(e, out);
                    }
                }
                ExprKind::Block { stmts, tail } => {
                    visit_stmts(stmts, out);
                    visit_expr(tail, out);
                }
                ExprKind::Unary { operand, .. }
                | ExprKind::Cast { expr: operand, .. }
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
                | ExprKind::MaybeSome(operand) => visit_expr(operand, out),
                ExprKind::EcAdd { lhs: a, rhs: b }
                | ExprKind::EcMul {
                    point: a,
                    scalar: b,
                }
                | ExprKind::ConstructJubjubPoint { x: a, y: b } => {
                    visit_expr(a, out);
                    visit_expr(b, out);
                }
                ExprKind::PersistentCommit { value, rand, .. }
                | ExprKind::TransientCommit { value, rand, .. } => {
                    visit_expr(value, out);
                    visit_expr(rand, out);
                }
                ExprKind::Index { base, index } => {
                    visit_expr(base, out);
                    visit_expr(index, out);
                }
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
                ExprKind::WitnessCall { args, .. } | ExprKind::NativeWitness { args, .. } => {
                    for a in args {
                        visit_expr(a, out);
                    }
                }
                ExprKind::LedgerCall { key_path, args, .. } => {
                    for k in key_path {
                        visit_expr(k, out);
                    }
                    for a in args {
                        visit_expr(a, out);
                    }
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
                    Stmt::ForRange { body, .. } => visit_stmts(body, out),
                    Stmt::ForEach { iter, body, .. } => {
                        visit_expr(iter, out);
                        visit_stmts(body, out);
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
        fn adt_uses_maybe(adt: &LedgerAdt, exported_root: bool) -> bool {
            match adt {
                LedgerAdt::Cell(ty) | LedgerAdt::Set(ty) => ty_uses_maybe(ty),
                LedgerAdt::Counter | LedgerAdt::Kernel => false,
                LedgerAdt::List(ty) => exported_root || ty_uses_maybe(ty),
                LedgerAdt::Map { key, value } => {
                    ty_uses_maybe(key) || adt_uses_maybe(value, exported_root)
                }
                LedgerAdt::MerkleTree { value, .. }
                | LedgerAdt::HistoricMerkleTree { value, .. } => ty_uses_maybe(value),
            }
        }
        self.input
            .program
            .exported_stdlib_types
            .iter()
            .any(|s| s == "Maybe")
            || self.input.program.circuits.iter().any(|c| {
                ty_uses_maybe(&c.ret_type) || c.params.iter().any(|p| ty_uses_maybe(&p.ty))
            })
            || self
                .input
                .program
                .ledger_fields
                .iter()
                .any(|f| adt_uses_maybe(&f.adt, f.exported))
            || self.input.program.witnesses.iter().any(|w| {
                ty_uses_maybe(&w.ret_type) || w.params.iter().any(|p| ty_uses_maybe(&p.ty))
            })
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

    fn uses_either(&self) -> bool {
        fn ty_uses_either(ty: &Type) -> bool {
            match ty {
                Type::Either(_, _) => true,
                Type::Maybe(e) | Type::Vector(_, e) => ty_uses_either(e),
                Type::Tuple(es) => es.iter().any(ty_uses_either),
                _ => false,
            }
        }
        fn adt_uses_either(adt: &LedgerAdt) -> bool {
            match adt {
                LedgerAdt::Cell(ty) | LedgerAdt::Set(ty) | LedgerAdt::List(ty) => {
                    ty_uses_either(ty)
                }
                LedgerAdt::Counter | LedgerAdt::Kernel => false,
                LedgerAdt::Map { key, value } => ty_uses_either(key) || adt_uses_either(value),
                LedgerAdt::MerkleTree { value, .. }
                | LedgerAdt::HistoricMerkleTree { value, .. } => ty_uses_either(value),
            }
        }
        self.input
            .program
            .exported_stdlib_types
            .iter()
            .any(|s| s == "Either")
            || self.input.program.circuits.iter().any(|c| {
                ty_uses_either(&c.ret_type) || c.params.iter().any(|p| ty_uses_either(&p.ty))
            })
            || self
                .input
                .program
                .ledger_fields
                .iter()
                .any(|f| adt_uses_either(&f.adt))
            || self.input.program.witnesses.iter().any(|w| {
                ty_uses_either(&w.ret_type) || w.params.iter().any(|p| ty_uses_either(&p.ty))
            })
            || self
                .input
                .program
                .structs
                .iter()
                .any(|s| s.fields.iter().any(|f| ty_uses_either(&f.ty)))
    }

    fn build_either_type(&self, exported: bool) -> Statement<'a> {
        let mut tparams = ArenaVec::with_capacity_in(2, self);
        tparams.push(self.ts_type_param("A"));
        tparams.push(self.ts_type_param("B"));
        let mut members = ArenaVec::with_capacity_in(3, self);
        members.push(TSSignature::new_ts_property_signature(
            SPAN,
            false,
            false,
            false,
            PropertyKey::StaticIdentifier(IdentifierName::boxed(SPAN, self.ident("is_left"), self)),
            Some(self.ts_type_annotation(TSType::new_ts_boolean_keyword(SPAN, self))),
            self,
        ));
        members.push(TSSignature::new_ts_property_signature(
            SPAN,
            false,
            false,
            false,
            PropertyKey::StaticIdentifier(IdentifierName::boxed(SPAN, self.ident("left"), self)),
            Some(self.ts_type_annotation(self.ts_type_ref("A", None))),
            self,
        ));
        members.push(TSSignature::new_ts_property_signature(
            SPAN,
            false,
            false,
            false,
            PropertyKey::StaticIdentifier(IdentifierName::boxed(SPAN, self.ident("right"), self)),
            Some(self.ts_type_annotation(self.ts_type_ref("B", None))),
            self,
        ));
        let obj = TSType::new_ts_type_literal(SPAN, members, self);
        let type_parameters = Some(TSTypeParameterDeclaration::boxed(SPAN, tparams, self));
        let decl = Declaration::new_ts_type_alias_declaration(
            SPAN,
            BindingIdentifier::new(SPAN, self.ident("Either"), self),
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
        if self.uses_either() {
            let exported = self
                .input
                .program
                .exported_stdlib_types
                .iter()
                .any(|s| s == "Either");
            body.push(self.build_either_type(exported));
        }

        // Emit enum declarations (exported if exported in Compact; still emitted locally if used).
        for enum_decl in &self.input.program.enums {
            body.push(self.build_enum_decl(enum_decl));
        }

        // Emit struct type aliases.
        for struct_decl in &self.input.program.structs {
            body.push(self.build_struct_decl(struct_decl));
        }

        // Emit nominal `new type` aliases.
        for nt_decl in &self.input.program.new_types {
            body.push(self.build_new_type_decl(nt_decl));
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
                TSEnumMemberName::Identifier(IdentifierName::boxed(
                    SPAN,
                    self.ident(variant),
                    self,
                )),
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

    fn build_new_type_decl(&self, decl: &NewTypeDecl) -> Statement<'a> {
        let td = Declaration::new_ts_type_alias_declaration(
            self.oxc_span(decl.span),
            BindingIdentifier::new(SPAN, self.ident(&decl.name), self),
            None,
            self.hir_type_to_ts(&decl.inner),
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
                Some(
                    self.ts_type_annotation(
                        self.ts_runtime_type("CircuitContext", Some(ctx_targs)),
                    ),
                ),
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
            Some(BindingIdentifier::new(
                span,
                self.ident(&format!("_{}", circuit.name)),
                self,
            )),
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
                Some(
                    self.ts_type_annotation(self.ts_runtime_type("WitnessContext", Some(ctx_args))),
                ),
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
            let formal_params =
                FormalParameters::boxed(SPAN, FormalParameterKind::Signature, params, None, self);
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
                Some(
                    self.ts_type_annotation(self.ts_runtime_type("CircuitContext", Some(ctx_args))),
                ),
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
        let formal_params =
            FormalParameters::boxed(SPAN, FormalParameterKind::Signature, params, None, self);
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

    fn ts_method_sig(
        &self,
        name: &str,
        params_spec: Vec<(&str, TSType<'a>)>,
        ret: TSType<'a>,
    ) -> TSSignature<'a> {
        let mut params = ArenaVec::with_capacity_in(params_spec.len(), self);
        for (pname, pty) in params_spec {
            params.push(FormalParameter::new(
                SPAN,
                ArenaVec::new_in(self),
                self.binding_ident(SPAN, pname),
                Some(self.ts_type_annotation(pty)),
                None,
                false,
                None,
                false,
                false,
                self,
            ));
        }
        let formal_params =
            FormalParameters::boxed(SPAN, FormalParameterKind::Signature, params, None, self);
        TSSignature::new_ts_method_signature(
            SPAN,
            PropertyKey::StaticIdentifier(IdentifierName::boxed(SPAN, self.ident(name), self)),
            false,
            false,
            TSMethodSignatureKind::Method,
            None,
            None,
            formal_params,
            Some(self.ts_type_annotation(ret)),
            self,
        )
    }

    fn ledger_adt_to_ts(&self, adt: &LedgerAdt) -> TSType<'a> {
        match adt {
            LedgerAdt::Cell(ty) => self.hir_type_to_ts(ty),
            LedgerAdt::Counter => TSType::new_ts_big_int_keyword(SPAN, self),
            LedgerAdt::Set(ty) => {
                let mut members = ArenaVec::with_capacity_in(3, self);
                members.push(self.ts_method_sig(
                    "isEmpty",
                    vec![],
                    TSType::new_ts_boolean_keyword(SPAN, self),
                ));
                members.push(self.ts_method_sig(
                    "size",
                    vec![],
                    TSType::new_ts_big_int_keyword(SPAN, self),
                ));
                members.push(self.ts_method_sig(
                    "member",
                    vec![("elem", self.hir_type_to_ts(ty))],
                    TSType::new_ts_boolean_keyword(SPAN, self),
                ));
                TSType::new_ts_type_literal(SPAN, members, self)
            }
            LedgerAdt::List(ty) => {
                let mut members = ArenaVec::with_capacity_in(3, self);
                members.push(self.ts_method_sig(
                    "isEmpty",
                    vec![],
                    TSType::new_ts_boolean_keyword(SPAN, self),
                ));
                members.push(self.ts_method_sig(
                    "length",
                    vec![],
                    TSType::new_ts_big_int_keyword(SPAN, self),
                ));
                let mut maybe_args = ArenaVec::with_capacity_in(1, self);
                maybe_args.push(self.hir_type_to_ts(ty));
                members.push(self.ts_method_sig(
                    "head",
                    vec![],
                    self.ts_type_ref("Maybe", Some(maybe_args)),
                ));
                TSType::new_ts_type_literal(SPAN, members, self)
            }
            LedgerAdt::Map { key, value } => {
                let mut members = ArenaVec::with_capacity_in(4, self);
                members.push(self.ts_method_sig(
                    "isEmpty",
                    vec![],
                    TSType::new_ts_boolean_keyword(SPAN, self),
                ));
                members.push(self.ts_method_sig(
                    "size",
                    vec![],
                    TSType::new_ts_big_int_keyword(SPAN, self),
                ));
                members.push(self.ts_method_sig(
                    "member",
                    vec![("key", self.hir_type_to_ts(key))],
                    TSType::new_ts_boolean_keyword(SPAN, self),
                ));
                members.push(self.ts_method_sig(
                    "lookup",
                    vec![("key", self.hir_type_to_ts(key))],
                    self.ledger_adt_to_ts(value),
                ));
                TSType::new_ts_type_literal(SPAN, members, self)
            }
            LedgerAdt::MerkleTree { .. } | LedgerAdt::HistoricMerkleTree { .. } => {
                let mut members = ArenaVec::with_capacity_in(2, self);
                members.push(self.ts_method_sig(
                    "isFull",
                    vec![],
                    TSType::new_ts_boolean_keyword(SPAN, self),
                ));
                members.push(self.ts_method_sig(
                    "checkRoot",
                    vec![("rt", self.ts_runtime_type("MerkleTreeDigest", None))],
                    TSType::new_ts_boolean_keyword(SPAN, self),
                ));
                TSType::new_ts_type_literal(SPAN, members, self)
            }
            LedgerAdt::Kernel => TSType::new_ts_unknown_keyword(SPAN, self),
        }
    }

    fn build_ledger_type(&self) -> Statement<'a> {
        let mut members = ArenaVec::new_in(self);
        for field in &self.input.program.ledger_fields {
            if !field.exported || matches!(field.adt, LedgerAdt::Kernel) {
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
                Some(self.ts_type_annotation(self.ledger_adt_to_ts(&field.adt))),
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
                LedgerAdt::Cell(_) => "decodeCell",
                LedgerAdt::Set(_) => "decodeSet",
                LedgerAdt::List(_) => "decodeList",
                LedgerAdt::Map { .. } => "decodeMap",
                LedgerAdt::MerkleTree { .. } => "decodeMerkleTree",
                LedgerAdt::HistoricMerkleTree { .. } => "decodeHistoricMerkleTree",
                LedgerAdt::Kernel => continue,
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
                        (
                            Some(Statement::new_block_statement(SPAN, else_stmts, self)),
                            er,
                        )
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
                Stmt::ForRange {
                    local,
                    name,
                    start,
                    end,
                    body,
                    span,
                } => {
                    let s = self.oxc_span(*span);
                    let mut loop_locals = locals.clone();
                    loop_locals.insert(*local, name.clone());
                    let (body_stmts, _) = self.lower_stmts_inner(
                        params,
                        body,
                        &mut loop_locals,
                        wrap_circuit_results,
                    );
                    let init_lit = Expression::new_big_int_literal(
                        s,
                        self.str_atom(&start.to_string()),
                        None,
                        oxc_syntax::number::BigintBase::Decimal,
                        self,
                    );
                    let end_lit = Expression::new_big_int_literal(
                        s,
                        self.str_atom(&end.to_string()),
                        None,
                        oxc_syntax::number::BigintBase::Decimal,
                        self,
                    );
                    let one_lit = Expression::new_big_int_literal(
                        s,
                        self.str_atom("1"),
                        None,
                        oxc_syntax::number::BigintBase::Decimal,
                        self,
                    );
                    let mut decls = ArenaVec::with_capacity_in(1, self);
                    decls.push(VariableDeclarator::new(
                        s,
                        self.binding_ident(s, name),
                        Some(self.ts_type_annotation(TSType::new_ts_big_int_keyword(SPAN, self))),
                        Some(init_lit),
                        false,
                        self,
                    ));
                    let init = ForStatementInit::VariableDeclaration(VariableDeclaration::boxed(
                        s,
                        VariableDeclarationKind::Let,
                        decls,
                        false,
                        self,
                    ));
                    let test = Expression::new_binary_expression(
                        s,
                        self.expr_ident(s, name),
                        BinaryOperator::LessThan,
                        end_lit,
                        self,
                    );
                    let update = Expression::new_assignment_expression(
                        s,
                        AssignmentOperator::Assign,
                        AssignmentTarget::new_assignment_target_identifier(
                            s,
                            self.ident(name),
                            self,
                        ),
                        Expression::new_binary_expression(
                            s,
                            self.expr_ident(s, name),
                            BinaryOperator::Addition,
                            one_lit,
                            self,
                        ),
                        self,
                    );
                    stmts.push(Statement::new_for_statement(
                        s,
                        Some(init),
                        Some(test),
                        Some(update),
                        Statement::new_block_statement(s, body_stmts, self),
                        self,
                    ));
                }
                Stmt::ForEach {
                    local,
                    name,
                    iter,
                    body,
                    span,
                    ..
                } => {
                    let s = self.oxc_span(*span);
                    let right = self.lower_expr(params, iter, locals);
                    let mut loop_locals = locals.clone();
                    loop_locals.insert(*local, name.clone());
                    let (body_stmts, _) = self.lower_stmts_inner(
                        params,
                        body,
                        &mut loop_locals,
                        wrap_circuit_results,
                    );
                    let mut decls = ArenaVec::with_capacity_in(1, self);
                    decls.push(VariableDeclarator::new(
                        s,
                        self.binding_ident(s, name),
                        None,
                        None,
                        false,
                        self,
                    ));
                    let left = ForStatementLeft::VariableDeclaration(VariableDeclaration::boxed(
                        s,
                        VariableDeclarationKind::Const,
                        decls,
                        false,
                        self,
                    ));
                    stmts.push(Statement::new_for_of_statement(
                        s,
                        false,
                        left,
                        right,
                        Statement::new_block_statement(s, body_stmts, self),
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
            Type::Field | Type::Uint(_) | Type::CurveField(_) => Expression::new_big_int_literal(
                span,
                self.str_atom("0"),
                None,
                oxc_syntax::number::BigintBase::Decimal,
                self,
            ),
            Type::CurvePoint(curve) => {
                let zero = Expression::new_big_int_literal(
                    span,
                    self.str_atom("0"),
                    None,
                    oxc_syntax::number::BigintBase::Decimal,
                    self,
                );
                match curve {
                    CurveKind::Jubjub | CurveKind::Curve25519 => {
                        let one = Expression::new_big_int_literal(
                            span,
                            self.str_atom("1"),
                            None,
                            oxc_syntax::number::BigintBase::Decimal,
                            self,
                        );
                        let mut props = ArenaVec::with_capacity_in(2, self);
                        props.push(ObjectPropertyKind::new_object_property(
                            span,
                            PropertyKind::Init,
                            PropertyKey::StaticIdentifier(IdentifierName::boxed(
                                span,
                                self.ident("x"),
                                self,
                            )),
                            zero,
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
                                self.ident("y"),
                                self,
                            )),
                            one,
                            false,
                            false,
                            false,
                            self,
                        ));
                        Expression::new_object_expression(span, props, self)
                    }
                    CurveKind::Secp256k1 | CurveKind::Secp256r1 => {
                        let zero2 = Expression::new_big_int_literal(
                            span,
                            self.str_atom("0"),
                            None,
                            oxc_syntax::number::BigintBase::Decimal,
                            self,
                        );
                        let mut props = ArenaVec::with_capacity_in(3, self);
                        props.push(ObjectPropertyKind::new_object_property(
                            span,
                            PropertyKind::Init,
                            PropertyKey::StaticIdentifier(IdentifierName::boxed(
                                span,
                                self.ident("x"),
                                self,
                            )),
                            zero,
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
                                self.ident("y"),
                                self,
                            )),
                            zero2,
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
                                self.ident("identity"),
                                self,
                            )),
                            self.expr_bool(span, true),
                            false,
                            false,
                            false,
                            self,
                        ));
                        Expression::new_object_expression(span, props, self)
                    }
                }
            }
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
            Type::NewType(id) => {
                let inner = &self.input.program.new_type_decl(*id).inner;
                self.default_expr_for_type(span, inner)
            }
            Type::Contract(_) => {
                let mut props = ArenaVec::with_capacity_in(1, self);
                props.push(ObjectPropertyKind::new_object_property(
                    span,
                    PropertyKind::Init,
                    PropertyKey::StaticIdentifier(IdentifierName::boxed(
                        span,
                        self.ident("bytes"),
                        self,
                    )),
                    self.default_expr_for_type(span, &Type::Bytes(32)),
                    false,
                    false,
                    false,
                    self,
                ));
                Expression::new_object_expression(span, props, self)
            }
            Type::Struct(_)
            | Type::Maybe(_)
            | Type::Either(_, _)
            | Type::MerkleTreeDigest
            | Type::MerkleTreePathEntry
            | Type::MerkleTreePath(_, _) => {
                let fields = self.input.program.struct_fields_of(ty).unwrap_or_default();
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
            ExprKind::DefaultAdt(adt) => {
                let mut args = ArenaVec::with_capacity_in(1, self);
                args.push(Argument::from(self.expr_str(span, adt.name())));
                self.expr_call(
                    span,
                    self.expr_member(
                        span,
                        self.expr_ident(span, "__compactRuntime"),
                        "defaultAdt",
                    ),
                    args,
                )
            }
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
                if matches!(op, UnaryOp::Neg)
                    && let Type::CurveField(f) = self.input.program.underlying_type(&operand.ty)
                {
                    let mut args = ArenaVec::with_capacity_in(1, self);
                    args.push(Argument::from(self.lower_expr(params, operand, locals)));
                    let fn_name = format!("{}Neg", f.runtime_prefix());
                    return self.expr_call(
                        span,
                        self.expr_member(span, self.expr_ident(span, "__compactRuntime"), &fn_name),
                        args,
                    );
                }
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
                if matches!(op, BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul)
                    && let Type::CurveField(f) = self.input.program.underlying_type(&lhs.ty)
                {
                    let suffix = match op {
                        BinaryOp::Add => "Add",
                        BinaryOp::Sub => "Sub",
                        BinaryOp::Mul => "Mul",
                        _ => unreachable!(),
                    };
                    let fn_name = format!("{}{suffix}", f.runtime_prefix());
                    let mut call_args = ArenaVec::with_capacity_in(2, self);
                    call_args.push(Argument::from(self.lower_expr(params, lhs, locals)));
                    call_args.push(Argument::from(self.lower_expr(params, rhs, locals)));
                    return self.expr_call(
                        span,
                        self.expr_member(span, self.expr_ident(span, "__compactRuntime"), &fn_name),
                        call_args,
                    );
                }
                if matches!(op, BinaryOp::Eq | BinaryOp::Neq)
                    && matches!(
                        self.input.program.underlying_type(&lhs.ty),
                        Type::Bytes(_)
                            | Type::CurvePoint(_)
                            | Type::Contract(_)
                            | Type::Vector(_, _)
                            | Type::Tuple(_)
                            | Type::Struct(_)
                            | Type::Maybe(_)
                            | Type::Either(_, _)
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
                    BinaryOp::Mul => BinaryOperator::Multiplication,
                    BinaryOp::Eq => BinaryOperator::StrictEquality,
                    BinaryOp::Neq => BinaryOperator::StrictInequality,
                    BinaryOp::Lt => BinaryOperator::LessThan,
                    BinaryOp::Le => BinaryOperator::LessEqualThan,
                    BinaryOp::Gt => BinaryOperator::GreaterThan,
                    BinaryOp::Ge => BinaryOperator::GreaterEqualThan,
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
            ExprKind::Disclose(expr) => self.lower_expr(params, expr, locals),
            ExprKind::Cast { expr, target } => {
                let src_u = self.input.program.underlying_type(&expr.ty);
                let dst_u = self.input.program.underlying_type(target);
                match (src_u, dst_u) {
                    (Type::Bytes(_), Type::Vector(_, _)) => {
                        // `Array.from(expr, (b) => BigInt(b))`
                        let mut b_params = ArenaVec::with_capacity_in(1, self);
                        b_params.push(FormalParameter::new(
                            span,
                            ArenaVec::new_in(self),
                            self.binding_ident(span, "b"),
                            None,
                            None,
                            false,
                            None,
                            false,
                            false,
                            self,
                        ));
                        let formal_params = FormalParameters::boxed(
                            span,
                            FormalParameterKind::ArrowFormalParameters,
                            b_params,
                            None,
                            self,
                        );
                        let mut bigint_args = ArenaVec::with_capacity_in(1, self);
                        bigint_args.push(Argument::from(self.expr_ident(span, "b")));
                        let bigint_call =
                            self.expr_call(span, self.expr_ident(span, "BigInt"), bigint_args);
                        let mut m_stmts = ArenaVec::with_capacity_in(1, self);
                        m_stmts.push(Statement::new_return_statement(
                            span,
                            Some(bigint_call),
                            self,
                        ));
                        let m_body =
                            FunctionBody::boxed(span, ArenaVec::new_in(self), m_stmts, self);
                        let mapper = Expression::new_arrow_function_expression(
                            span,
                            false,
                            None,
                            formal_params,
                            None,
                            ArrowFunctionBody::FunctionBody(m_body),
                            self,
                        );
                        let mut from_args = ArenaVec::with_capacity_in(2, self);
                        from_args.push(Argument::from(self.lower_expr(params, expr, locals)));
                        from_args.push(Argument::from(mapper));
                        self.expr_call(
                            span,
                            self.expr_member(span, self.expr_ident(span, "Array"), "from"),
                            from_args,
                        )
                    }
                    (Type::Vector(_, _), Type::Bytes(_)) => {
                        // `new Uint8Array(expr.map((b) => Number(b)))`
                        let mut b_params = ArenaVec::with_capacity_in(1, self);
                        b_params.push(FormalParameter::new(
                            span,
                            ArenaVec::new_in(self),
                            self.binding_ident(span, "b"),
                            None,
                            None,
                            false,
                            None,
                            false,
                            false,
                            self,
                        ));
                        let formal_params = FormalParameters::boxed(
                            span,
                            FormalParameterKind::ArrowFormalParameters,
                            b_params,
                            None,
                            self,
                        );
                        let mut num_args = ArenaVec::with_capacity_in(1, self);
                        num_args.push(Argument::from(self.expr_ident(span, "b")));
                        let num_call =
                            self.expr_call(span, self.expr_ident(span, "Number"), num_args);
                        let mut m_stmts = ArenaVec::with_capacity_in(1, self);
                        m_stmts.push(Statement::new_return_statement(span, Some(num_call), self));
                        let m_body =
                            FunctionBody::boxed(span, ArenaVec::new_in(self), m_stmts, self);
                        let mapper = Expression::new_arrow_function_expression(
                            span,
                            false,
                            None,
                            formal_params,
                            None,
                            ArrowFunctionBody::FunctionBody(m_body),
                            self,
                        );
                        let mut map_args = ArenaVec::with_capacity_in(1, self);
                        map_args.push(Argument::from(mapper));
                        let mapped = self.expr_call(
                            span,
                            self.expr_member(span, self.lower_expr(params, expr, locals), "map"),
                            map_args,
                        );
                        let mut ctor_args = ArenaVec::with_capacity_in(1, self);
                        ctor_args.push(Argument::from(mapped));
                        Expression::new_new_expression(
                            span,
                            self.expr_ident(span, "Uint8Array"),
                            None,
                            ctor_args,
                            self,
                        )
                    }
                    (
                        Type::Field | Type::Uint(_) | Type::Boolean | Type::Enum(_),
                        Type::CurveField(CurveFieldKind::JubjubScalar),
                    ) => {
                        let mut call_args = ArenaVec::with_capacity_in(1, self);
                        call_args.push(Argument::from(self.lower_expr(params, expr, locals)));
                        self.expr_call(
                            span,
                            self.expr_member(
                                span,
                                self.expr_ident(span, "__compactRuntime"),
                                "convertNumericToJubjubScalar",
                            ),
                            call_args,
                        )
                    }
                    (Type::CurveField(_) | Type::Field, Type::Bytes(n)) => {
                        let mut call_args = ArenaVec::with_capacity_in(2, self);
                        call_args.push(Argument::from(self.expr_num(span, *n as f64)));
                        call_args.push(Argument::from(self.lower_expr(params, expr, locals)));
                        self.expr_call(
                            span,
                            self.expr_member(
                                span,
                                self.expr_ident(span, "__compactRuntime"),
                                "convertBigintToBytes",
                            ),
                            call_args,
                        )
                    }
                    (Type::Bytes(_), Type::CurveField(f)) => {
                        let mut call_args = ArenaVec::with_capacity_in(2, self);
                        call_args.push(Argument::from(self.lower_expr(params, expr, locals)));
                        call_args.push(Argument::from(self.expr_member(
                            span,
                            self.expr_ident(span, "__compactRuntime"),
                            f.runtime_max_const(),
                        )));
                        self.expr_call(
                            span,
                            self.expr_member(
                                span,
                                self.expr_ident(span, "__compactRuntime"),
                                "convertBytesToField",
                            ),
                            call_args,
                        )
                    }
                    _ => self.lower_expr(params, expr, locals),
                }
            }
            ExprKind::BytesPack(elems) => {
                let mut arr = ArenaVec::with_capacity_in(elems.len(), self);
                for elem in elems {
                    let elem_expr = match &elem.kind {
                        ExprKind::IntLit(v) => self.expr_num(span, *v as f64),
                        _ => {
                            let mut nargs = ArenaVec::with_capacity_in(1, self);
                            nargs.push(Argument::from(self.lower_expr(params, elem, locals)));
                            self.expr_call(span, self.expr_ident(span, "Number"), nargs)
                        }
                    };
                    arr.push(ArrayExpressionElement::from(elem_expr));
                }
                let mut args = ArenaVec::with_capacity_in(1, self);
                args.push(Argument::from(Expression::new_array_expression(
                    span, arr, self,
                )));
                Expression::new_new_expression(
                    span,
                    self.expr_ident(span, "Uint8Array"),
                    None,
                    args,
                    self,
                )
            }
            ExprKind::Block { stmts, tail } => {
                let mut block_locals = locals.clone();
                let (mut body_stmts, _) =
                    self.lower_stmts_inner(params, stmts, &mut block_locals, false);
                let tail_expr = self.lower_expr(params, tail, &block_locals);
                body_stmts.push(Statement::new_return_statement(span, Some(tail_expr), self));
                let body = FunctionBody::boxed(span, ArenaVec::new_in(self), body_stmts, self);
                let formal_params = FormalParameters::boxed(
                    span,
                    FormalParameterKind::ArrowFormalParameters,
                    ArenaVec::new_in(self),
                    None,
                    self,
                );
                let arrow = Expression::new_arrow_function_expression(
                    span,
                    false,
                    None,
                    formal_params,
                    None,
                    ArrowFunctionBody::FunctionBody(body),
                    self,
                );
                self.expr_call(
                    span,
                    Expression::new_parenthesized_expression(span, arrow, self),
                    ArenaVec::new_in(self),
                )
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
            ExprKind::NativeWitness { kind, args } => {
                let mut call_args = ArenaVec::with_capacity_in(1 + args.len(), self);
                call_args.push(Argument::from(self.expr_ident(span, "context")));
                for a in args {
                    call_args.push(Argument::from(self.lower_expr(params, a, locals)));
                }
                self.expr_call(
                    span,
                    self.expr_member(
                        span,
                        self.expr_ident(span, "__compactRuntime"),
                        kind.runtime_name(),
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
            ExprKind::Keccak256 { arg, .. } => {
                let mut call_args = ArenaVec::with_capacity_in(1, self);
                call_args.push(Argument::from(self.lower_expr(params, arg, locals)));
                self.expr_call(
                    span,
                    self.expr_member(span, self.expr_ident(span, "__compactRuntime"), "keccak256"),
                    call_args,
                )
            }
            ExprKind::Sha512 { arg, .. } => {
                let mut call_args = ArenaVec::with_capacity_in(1, self);
                call_args.push(Argument::from(self.lower_expr(params, arg, locals)));
                self.expr_call(
                    span,
                    self.expr_member(span, self.expr_ident(span, "__compactRuntime"), "sha512"),
                    call_args,
                )
            }
            ExprKind::FieldInv(arg) => {
                let fn_name = match self.input.program.underlying_type(&arg.ty) {
                    Type::CurveField(f) => format!("{}Inv", f.runtime_prefix()),
                    _ => "fieldInv".to_owned(),
                };
                let mut call_args = ArenaVec::with_capacity_in(1, self);
                call_args.push(Argument::from(self.lower_expr(params, arg, locals)));
                self.expr_call(
                    span,
                    self.expr_member(span, self.expr_ident(span, "__compactRuntime"), &fn_name),
                    call_args,
                )
            }
            ExprKind::EcAdd { lhs, rhs } => {
                let fn_name = match self.input.program.underlying_type(&lhs.ty) {
                    Type::CurvePoint(CurveKind::Jubjub) => "ecAdd",
                    Type::CurvePoint(CurveKind::Secp256k1) => "secp256k1Add",
                    Type::CurvePoint(CurveKind::Secp256r1) => "secp256r1Add",
                    Type::CurvePoint(CurveKind::Curve25519) => "curve25519Add",
                    _ => "ecAdd",
                };
                let mut call_args = ArenaVec::with_capacity_in(2, self);
                call_args.push(Argument::from(self.lower_expr(params, lhs, locals)));
                call_args.push(Argument::from(self.lower_expr(params, rhs, locals)));
                self.expr_call(
                    span,
                    self.expr_member(span, self.expr_ident(span, "__compactRuntime"), fn_name),
                    call_args,
                )
            }
            ExprKind::EcNeg(arg) => {
                let mut call_args = ArenaVec::with_capacity_in(1, self);
                call_args.push(Argument::from(self.lower_expr(params, arg, locals)));
                self.expr_call(
                    span,
                    self.expr_member(span, self.expr_ident(span, "__compactRuntime"), "ecNeg"),
                    call_args,
                )
            }
            ExprKind::EcMul { point, scalar } => {
                let fn_name = match self.input.program.underlying_type(&point.ty) {
                    Type::CurvePoint(CurveKind::Jubjub) => "ecMul",
                    Type::CurvePoint(CurveKind::Secp256k1) => "secp256k1Mul",
                    Type::CurvePoint(CurveKind::Secp256r1) => "secp256r1Mul",
                    Type::CurvePoint(CurveKind::Curve25519) => "curve25519Mul",
                    _ => "ecMul",
                };
                let mut call_args = ArenaVec::with_capacity_in(2, self);
                call_args.push(Argument::from(self.lower_expr(params, point, locals)));
                call_args.push(Argument::from(self.lower_expr(params, scalar, locals)));
                self.expr_call(
                    span,
                    self.expr_member(span, self.expr_ident(span, "__compactRuntime"), fn_name),
                    call_args,
                )
            }
            ExprKind::EcMulGenerator(scalar) => {
                let fn_name = match self.input.program.underlying_type(&scalar.ty) {
                    Type::CurveField(CurveFieldKind::JubjubScalar) => "ecMulGenerator",
                    Type::CurveField(CurveFieldKind::Secp256k1Scalar) => "secp256k1MulGenerator",
                    Type::CurveField(CurveFieldKind::Secp256r1Scalar) => "secp256r1MulGenerator",
                    Type::CurveField(CurveFieldKind::Curve25519Scalar) => "curve25519MulGenerator",
                    _ => "ecMulGenerator",
                };
                let mut call_args = ArenaVec::with_capacity_in(1, self);
                call_args.push(Argument::from(self.lower_expr(params, scalar, locals)));
                self.expr_call(
                    span,
                    self.expr_member(span, self.expr_ident(span, "__compactRuntime"), fn_name),
                    call_args,
                )
            }
            ExprKind::HashToCurve { arg, .. } => {
                let mut call_args = ArenaVec::with_capacity_in(1, self);
                call_args.push(Argument::from(self.lower_expr(params, arg, locals)));
                self.expr_call(
                    span,
                    self.expr_member(
                        span,
                        self.expr_ident(span, "__compactRuntime"),
                        "hashToCurve",
                    ),
                    call_args,
                )
            }
            ExprKind::ConstructJubjubPoint { x, y } => {
                let mut call_args = ArenaVec::with_capacity_in(2, self);
                call_args.push(Argument::from(self.lower_expr(params, x, locals)));
                call_args.push(Argument::from(self.lower_expr(params, y, locals)));
                self.expr_call(
                    span,
                    self.expr_member(
                        span,
                        self.expr_ident(span, "__compactRuntime"),
                        "constructJubjubPoint",
                    ),
                    call_args,
                )
            }
            ExprKind::PointCoord { point, is_y } => {
                let fn_name = match (self.input.program.underlying_type(&point.ty), *is_y) {
                    (Type::CurvePoint(CurveKind::Jubjub), false) => "jubjubPointX",
                    (Type::CurvePoint(CurveKind::Jubjub), true) => "jubjubPointY",
                    (Type::CurvePoint(CurveKind::Secp256k1), false) => "secp256k1PointX",
                    (Type::CurvePoint(CurveKind::Secp256k1), true) => "secp256k1PointY",
                    (Type::CurvePoint(CurveKind::Secp256r1), false) => "secp256r1PointX",
                    (Type::CurvePoint(CurveKind::Secp256r1), true) => "secp256r1PointY",
                    (Type::CurvePoint(CurveKind::Curve25519), false) => "curve25519PointX",
                    (Type::CurvePoint(CurveKind::Curve25519), true) => "curve25519PointY",
                    _ => "jubjubPointX",
                };
                let mut call_args = ArenaVec::with_capacity_in(1, self);
                call_args.push(Argument::from(self.lower_expr(params, point, locals)));
                self.expr_call(
                    span,
                    self.expr_member(span, self.expr_ident(span, "__compactRuntime"), fn_name),
                    call_args,
                )
            }
            ExprKind::TransientHash { arg, .. } => {
                let mut call_args = ArenaVec::with_capacity_in(1, self);
                call_args.push(Argument::from(self.lower_expr(params, arg, locals)));
                self.expr_call(
                    span,
                    self.expr_member(
                        span,
                        self.expr_ident(span, "__compactRuntime"),
                        "transientHash",
                    ),
                    call_args,
                )
            }
            ExprKind::PersistentCommit { value, rand, .. } => {
                let mut call_args = ArenaVec::with_capacity_in(2, self);
                call_args.push(Argument::from(self.lower_expr(params, value, locals)));
                call_args.push(Argument::from(self.lower_expr(params, rand, locals)));
                self.expr_call(
                    span,
                    self.expr_member(
                        span,
                        self.expr_ident(span, "__compactRuntime"),
                        "persistentCommit",
                    ),
                    call_args,
                )
            }
            ExprKind::TransientCommit { value, rand, .. } => {
                let mut call_args = ArenaVec::with_capacity_in(2, self);
                call_args.push(Argument::from(self.lower_expr(params, value, locals)));
                call_args.push(Argument::from(self.lower_expr(params, rand, locals)));
                self.expr_call(
                    span,
                    self.expr_member(
                        span,
                        self.expr_ident(span, "__compactRuntime"),
                        "transientCommit",
                    ),
                    call_args,
                )
            }
            ExprKind::DegradeToTransient(arg) => {
                let mut call_args = ArenaVec::with_capacity_in(1, self);
                call_args.push(Argument::from(self.lower_expr(params, arg, locals)));
                self.expr_call(
                    span,
                    self.expr_member(
                        span,
                        self.expr_ident(span, "__compactRuntime"),
                        "degradeToTransient",
                    ),
                    call_args,
                )
            }
            ExprKind::UpgradeFromTransient(arg) => {
                let mut call_args = ArenaVec::with_capacity_in(1, self);
                call_args.push(Argument::from(self.lower_expr(params, arg, locals)));
                self.expr_call(
                    span,
                    self.expr_member(
                        span,
                        self.expr_ident(span, "__compactRuntime"),
                        "upgradeFromTransient",
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
            ExprKind::Index { base, index } => {
                let obj = self.lower_expr(params, base, locals);
                let idx_expr = match &index.kind {
                    ExprKind::IntLit(v) => self.expr_num(span, *v as f64),
                    _ => {
                        let mut nargs = ArenaVec::with_capacity_in(1, self);
                        nargs.push(Argument::from(self.lower_expr(params, index, locals)));
                        self.expr_call(span, self.expr_ident(span, "Number"), nargs)
                    }
                };
                Expression::ComputedMemberExpression(ComputedMemberExpression::boxed(
                    span, obj, idx_expr, false, self,
                ))
            }
            ExprKind::Slice { base, start, len } => {
                let obj = self.lower_expr(params, base, locals);
                let mut sargs = ArenaVec::with_capacity_in(2, self);
                sargs.push(Argument::from(self.expr_num(span, *start as f64)));
                sargs.push(Argument::from(self.expr_num(span, (*start + *len) as f64)));
                self.expr_call(span, self.expr_member(span, obj, "slice"), sargs)
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
            ExprKind::ContractCall {
                contract,
                receiver,
                method,
                args,
            } => {
                let decl = self.input.program.contract_decl(*contract);
                let recv_expr = self.lower_expr(params, receiver, locals);
                let mut dec_args = ArenaVec::with_capacity_in(1, self);
                dec_args.push(Argument::from(self.expr_member(span, recv_expr, "bytes")));
                let callee_addr = self.expr_call(
                    span,
                    self.expr_member(
                        span,
                        self.expr_ident(span, "__compactRuntime"),
                        "decodeContractAddress",
                    ),
                    dec_args,
                );
                let mut arg_elems = ArenaVec::with_capacity_in(args.len(), self);
                for a in args {
                    arg_elems.push(ArrayExpressionElement::from(
                        self.lower_expr(params, a, locals),
                    ));
                }
                let args_arr = Expression::new_array_expression(span, arg_elems, self);
                let mut props = ArenaVec::with_capacity_in(5, self);
                let push_prop = |props: &mut ArenaVec<'a, ObjectPropertyKind<'a>>,
                                 key: &str,
                                 val: Expression<'a>| {
                    props.push(ObjectPropertyKind::new_object_property(
                        span,
                        PropertyKind::Init,
                        PropertyKey::StaticIdentifier(IdentifierName::boxed(
                            span,
                            self.ident(key),
                            self,
                        )),
                        val,
                        false,
                        false,
                        false,
                        self,
                    ));
                };
                push_prop(&mut props, "context", self.expr_ident(span, "context"));
                push_prop(&mut props, "interfaceName", self.expr_str(span, &decl.name));
                push_prop(&mut props, "calleeCircuitId", self.expr_str(span, method));
                push_prop(&mut props, "calleeAddress", callee_addr);
                push_prop(&mut props, "args", args_arr);
                let opts = Expression::new_object_expression(span, props, self);
                let mut call_args = ArenaVec::with_capacity_in(1, self);
                call_args.push(Argument::from(opts));
                self.expr_call(
                    span,
                    self.expr_member(
                        span,
                        self.expr_ident(span, "__compactRuntime"),
                        "crossContractCall",
                    ),
                    call_args,
                )
            }
            ExprKind::Emit {
                event_tag,
                payload_len,
                value,
                ..
            } => {
                let mut call_args = ArenaVec::with_capacity_in(5, self);
                call_args.push(Argument::from(self.expr_ident(span, "context")));
                call_args.push(Argument::from(self.expr_num(span, 1.0)));
                call_args.push(Argument::from(self.expr_num(span, *event_tag as f64)));
                call_args.push(Argument::from(self.expr_num(span, *payload_len as f64)));
                call_args.push(Argument::from(self.lower_expr(params, value, locals)));
                self.expr_call(
                    span,
                    self.expr_member(span, self.expr_ident(span, "__compactRuntime"), "emitEvent"),
                    call_args,
                )
            }
            ExprKind::Serialize { len, value, .. } => {
                let mut call_args = ArenaVec::with_capacity_in(2, self);
                call_args.push(Argument::from(self.expr_num(span, *len as f64)));
                call_args.push(Argument::from(self.lower_expr(params, value, locals)));
                self.expr_call(
                    span,
                    self.expr_member(span, self.expr_ident(span, "__compactRuntime"), "serialize"),
                    call_args,
                )
            }
            ExprKind::Deserialize { len, bytes, .. } => {
                let mut call_args = ArenaVec::with_capacity_in(2, self);
                call_args.push(Argument::from(self.expr_num(span, *len as f64)));
                call_args.push(Argument::from(self.lower_expr(params, bytes, locals)));
                self.expr_call(
                    span,
                    self.expr_member(
                        span,
                        self.expr_ident(span, "__compactRuntime"),
                        "deserialize",
                    ),
                    call_args,
                )
            }
            ExprKind::LedgerCall {
                field,
                key_path,
                op,
                args,
                ..
            } => {
                let ledger_field = self.input.program.ledger_field(*field);
                if matches!(ledger_field.adt, LedgerAdt::Kernel) {
                    let mut call_args = ArenaVec::with_capacity_in(1 + args.len(), self);
                    call_args.push(Argument::from(self.expr_ident(span, "context")));
                    for a in args {
                        call_args.push(Argument::from(self.lower_expr(params, a, locals)));
                    }
                    return self.expr_call(
                        span,
                        self.expr_member(
                            span,
                            self.expr_member(
                                span,
                                self.expr_ident(span, "__compactRuntime"),
                                "kernel",
                            ),
                            op.name(),
                        ),
                        call_args,
                    );
                }
                let path_arg = if key_path.is_empty() {
                    self.expr_num(span, ledger_field.path[0] as f64)
                } else {
                    let mut elems = ArenaVec::with_capacity_in(1 + key_path.len(), self);
                    elems.push(ArrayExpressionElement::from(
                        self.expr_num(span, ledger_field.path[0] as f64),
                    ));
                    for k in key_path {
                        elems.push(ArrayExpressionElement::from(
                            self.lower_expr(params, k, locals),
                        ));
                    }
                    Expression::new_array_expression(span, elems, self)
                };
                match op {
                    LedgerOp::CounterIncrement | LedgerOp::CounterDecrement
                        if key_path.is_empty()
                            && matches!(
                                args.first().map(|a| &a.kind),
                                Some(ExprKind::IntLit(_))
                            ) =>
                    {
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
                    _ => {
                        let rt_fn = match op {
                            LedgerOp::CellRead => "readCell",
                            LedgerOp::CellWrite => "writeCell",
                            LedgerOp::CellWriteCoin => "writeCoin",
                            LedgerOp::CounterRead => "readCounter",
                            LedgerOp::CounterLessThan => "counterLessThan",
                            LedgerOp::CounterIncrement => "counterIncrement",
                            LedgerOp::CounterDecrement => "counterDecrement",
                            LedgerOp::SetMember => "setMember",
                            LedgerOp::SetInsert => "setInsert",
                            LedgerOp::SetInsertCoin => "setInsertCoin",
                            LedgerOp::SetRemove => "setRemove",
                            LedgerOp::SetIsEmpty => "setIsEmpty",
                            LedgerOp::SetSize => "setSize",
                            LedgerOp::MapMember => "mapMember",
                            LedgerOp::MapLookup => "mapLookup",
                            LedgerOp::MapInsert => "mapInsert",
                            LedgerOp::MapInsertCoin => "mapInsertCoin",
                            LedgerOp::MapInsertDefault => "mapInsertDefault",
                            LedgerOp::MapRemove => "mapRemove",
                            LedgerOp::MapIsEmpty => "mapIsEmpty",
                            LedgerOp::MapSize => "mapSize",
                            LedgerOp::ListPushFront => "listPushFront",
                            LedgerOp::ListPushFrontCoin => "listPushFrontCoin",
                            LedgerOp::ListPopFront => "listPopFront",
                            LedgerOp::ListHead => "listHead",
                            LedgerOp::ListLength => "listLength",
                            LedgerOp::ListIsEmpty => "listIsEmpty",
                            LedgerOp::MerkleTreeInsert => "merkleTreeInsert",
                            LedgerOp::MerkleTreeInsertHash => "merkleTreeInsertHash",
                            LedgerOp::MerkleTreeInsertHashIndex => "merkleTreeInsertHashIndex",
                            LedgerOp::MerkleTreeInsertIndex => "merkleTreeInsertIndex",
                            LedgerOp::MerkleTreeInsertIndexDefault => {
                                "merkleTreeInsertIndexDefault"
                            }
                            LedgerOp::MerkleTreeIsFull => "merkleTreeIsFull",
                            LedgerOp::MerkleTreeCheckRoot => "merkleTreeCheckRoot",
                            LedgerOp::HistoricMerkleTreeInsert => "historicMerkleTreeInsert",
                            LedgerOp::HistoricMerkleTreeInsertHash => {
                                "historicMerkleTreeInsertHash"
                            }
                            LedgerOp::HistoricMerkleTreeInsertHashIndex => {
                                "historicMerkleTreeInsertHashIndex"
                            }
                            LedgerOp::HistoricMerkleTreeInsertIndex => {
                                "historicMerkleTreeInsertIndex"
                            }
                            LedgerOp::HistoricMerkleTreeInsertIndexDefault => {
                                "historicMerkleTreeInsertIndexDefault"
                            }
                            LedgerOp::HistoricMerkleTreeIsFull => "historicMerkleTreeIsFull",
                            LedgerOp::HistoricMerkleTreeCheckRoot => "historicMerkleTreeCheckRoot",
                            LedgerOp::HistoricMerkleTreeResetHistory => {
                                "historicMerkleTreeResetHistory"
                            }
                            LedgerOp::CellResetToDefault
                            | LedgerOp::CounterResetToDefault
                            | LedgerOp::SetResetToDefault
                            | LedgerOp::MapResetToDefault
                            | LedgerOp::ListResetToDefault
                            | LedgerOp::MerkleTreeResetToDefault
                            | LedgerOp::HistoricMerkleTreeResetToDefault => "resetToDefault",
                            _ => unreachable!("Kernel ops handled above"),
                        };
                        let mut call_args = ArenaVec::with_capacity_in(2 + args.len(), self);
                        call_args.push(Argument::from(self.expr_ident(span, "context")));
                        call_args.push(Argument::from(path_arg));
                        for a in args {
                            call_args.push(Argument::from(self.lower_expr(params, a, locals)));
                        }
                        self.expr_call(
                            span,
                            self.expr_member(
                                span,
                                self.expr_ident(span, "__compactRuntime"),
                                rt_fn,
                            ),
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
            Some(
                self.ts_type_annotation(
                    self.ts_runtime_type("ConstructorContext", Some(ctx_targs)),
                ),
            ),
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

    #[test]
    fn codegen_adt_showcase_contract() {
        assert_compact_snapshot!(
            file: include_str!("../../../examples/adt_showcase.compact"),
            compile_ts_bundle
        );
    }

    #[test]
    fn codegen_modules_and_generics() {
        assert_compact_snapshot!(
            r#"
            pragma language_version >= 0.16.0;

            import CompactStandardLibrary;

            export new type AccountId = Bytes<32>;
            struct Pair<A, B> {
              first: A;
              second: B;
            }

            module CounterMod<#N> {
              export ledger count: Counter;
              export circuit bump(): [] {
                for (const i of 0..N) {
                  count.increment(1);
                }
              }
            }

            import { bump as bump_two } from CounterMod<2>;
            export { bump_two }

            circuit first<A, B>(p: Pair<A, B>): A {
              return p.first;
            }

            export circuit sample(acct: AccountId, v: Vector<3, Field>): [Field, Vector<2, Field>] {
              const p: Pair<Field, AccountId> = Pair<Field, AccountId>{ first: v[0], second: acct };
              const idx = 2;
              bump_two();
              return [first<Field, AccountId>(p) + v[idx], slice<2>(v, 1)];
            }
            "#,
            compile_ts_bundle
        );
    }

    #[test]
    fn codegen_patterns_map_fold_and_either() {
        assert_compact_snapshot!(
            file: include_str!("../../../examples/functional_patterns.compact"),
            compile_ts_bundle
        );
    }

    #[test]
    fn codegen_kernel_block_time_and_tokens() {
        assert_compact_snapshot!(
            file: include_str!("../../../examples/token_vault.compact"),
            compile_ts_bundle
        );
    }

    #[test]
    fn codegen_crypto_curves_and_signatures() {
        assert_compact_snapshot!(
            file: include_str!("../../../examples/crypto_curves.compact"),
            compile_ts_bundle
        );
    }

    #[test]
    fn codegen_composable_contracts_and_events() {
        assert_compact_snapshot!(
            file: include_str!("../../../examples/composable_events.compact"),
            compile_ts_bundle
        );
    }
}
