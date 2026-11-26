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

//! Compact code fixer & language migrator (`compact-fixup`).
//!
//! Mirrors upstream `compiler/fixup.ss`:
//! 1. Pre-fixup AST rewrites that do not require semantic analysis (`include "std";` ->
//!    `import CompactStandardLibrary;`, and optional `--update-uint-ranges` upper-bound updates).
//! 2. Semantic analysis in fixup mode (`compact_sema::check_with_loader_for_fixup`) to resolve
//!    deprecated standard-library and ledger-operator names accurately with scope & shadowing checks.
//! 3. Span-preserving source edits followed by canonical formatting via `compact-fmt`.

use std::collections::BTreeMap;

use compact_ast::{Ast, NodeIndex, NodeTag, unescape_string_bytes};
use compact_diagnostics::{CompactDiagnostic, DiagnosticBag};
use compact_fmt::{FormatOptions, format_ast};
use compact_parser::parse;
use compact_sema::{FixupCollector, ModuleLoader, check_with_loader_for_fixup};
use compact_span::{SourceFile, Span};

/// Options controlling `compact-fixup`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FixupOptions {
    /// Target maximum line length passed to `compact-fmt`.
    pub line_length: usize,
    /// When true, increment constant `Uint<lo..hi>` upper bounds by 1 (preserving numeric radix)
    /// and warn on generic-size upper bounds (`Uint<0..N>`).
    pub update_uint_ranges: bool,
}

impl Default for FixupOptions {
    fn default() -> Self {
        Self {
            line_length: 100,
            update_uint_ranges: false,
        }
    }
}

/// Output produced by [`fixup_source`].
#[derive(Debug)]
pub struct FixupOutput {
    /// The migrated and canonically formatted Compact source code.
    pub formatted: String,
    /// Non-fatal warnings emitted during migration (e.g. skipped shadowing renames or generic
    /// `Uint` range bounds requiring manual update), ordered by source location.
    pub warnings: Vec<CompactDiagnostic>,
    /// Total number of source edits applied (pre-fixup + semantic alias renames).
    pub edits_applied: usize,
}

struct NoopLoader;

impl ModuleLoader for NoopLoader {
    fn load(
        &self,
        _from_file: &SourceFile,
        specifier: &str,
    ) -> Result<(SourceFile, Ast), compact_sema::LoadError> {
        Err(compact_sema::LoadError::NotFound(format!(
            "cannot resolve external file `{specifier}` without a module loader"
        )))
    }
}

/// Migrate and format a single-file Compact source without external module loading.
pub fn fixup_single_file(
    file: &SourceFile,
    options: &FixupOptions,
) -> Result<FixupOutput, DiagnosticBag> {
    fixup_source(file, options, &NoopLoader)
}

/// Migrate and format a Compact source file, resolving external `include`/`import` files via `loader`.
pub fn fixup_source(
    file: &SourceFile,
    options: &FixupOptions,
    loader: &dyn ModuleLoader,
) -> Result<FixupOutput, DiagnosticBag> {
    // 1. Parse original source.
    let parsed = parse(file);
    let ast = parsed.diagnostics.into_result(parsed.ast)?;

    // 2. Pre-fixup AST rewrites (do not depend on semantic analysis).
    let mut pre_edits: BTreeMap<Span, String> = BTreeMap::new();
    let mut warnings: Vec<(u32, CompactDiagnostic)> = Vec::new();
    collect_pre_fixup_edits(file, &ast, options, &mut pre_edits, &mut warnings);

    let pre_edit_count = pre_edits.len();
    let (work_file, work_ast) = if pre_edits.is_empty() {
        (file.clone(), ast)
    } else {
        let rewritten = apply_span_edits(file.text(), &pre_edits);
        let next_file = SourceFile::new(file.id, file.name.clone(), file.path.clone(), rewritten);
        let reparsed = parse(&next_file);
        let next_ast = reparsed.diagnostics.into_result(reparsed.ast)?;
        (next_file, next_ast)
    };

    // 3. Semantic analysis in fixup mode to discover scope-accurate alias renamings.
    let mut collector = FixupCollector::default();
    let checked = check_with_loader_for_fixup(&work_file, &work_ast, loader, &mut collector);
    if checked.diagnostics.has_errors() {
        return Err(checked.diagnostics);
    }

    for warn in collector.warnings {
        let offset = warn.labels.first().map_or(0, |l| l.offset() as u32);
        warnings.push((offset, warn));
    }
    warnings.sort_by_key(|(offset, _)| *offset);
    let ordered_warnings = warnings.into_iter().map(|(_, d)| d).collect();

    // 4. Apply semantic renamings (if any) and format canonically.
    let rename_count = collector.renamings.len();
    let (final_source, final_ast) = if collector.renamings.is_empty() {
        (work_file.text().to_owned(), work_ast)
    } else {
        let mut edits = BTreeMap::new();
        for (span, rename) in &collector.renamings {
            let current = span.slice(work_file.text());
            debug_assert_eq!(
                current, rename.old_name,
                "fixup rename span mismatch: expected `{}`, found `{}`",
                rename.old_name, current
            );
            edits.insert(*span, rename.new_name.clone());
        }
        let rewritten = apply_span_edits(work_file.text(), &edits);
        let final_file = SourceFile::new(
            file.id,
            file.name.clone(),
            file.path.clone(),
            rewritten.clone(),
        );
        let reparsed = parse(&final_file);
        let ast = reparsed.diagnostics.into_result(reparsed.ast)?;
        (rewritten, ast)
    };

    let formatted = format_ast(
        &final_ast,
        &final_source,
        &FormatOptions {
            line_length: options.line_length,
        },
    );

    Ok(FixupOutput {
        formatted,
        warnings: ordered_warnings,
        edits_applied: pre_edit_count + rename_count,
    })
}

fn collect_pre_fixup_edits(
    file: &SourceFile,
    ast: &Ast,
    options: &FixupOptions,
    edits: &mut BTreeMap<Span, String>,
    warnings: &mut Vec<(u32, CompactDiagnostic)>,
) {
    let source = file.text();
    for raw_idx in 0..ast.nodes.len() {
        let node = NodeIndex(raw_idx as u32);
        match ast.node_tag(node) {
            NodeTag::IncludeDecl => {
                let decl = ast.include_decl(node);
                let raw = ast.token_text(decl.path_token, source);
                if unescape_string_bytes(raw) == b"std" {
                    let kw_span = ast.token_span(ast.node_main_token(node));
                    let path_span = ast.token_span(decl.path_token);
                    edits.insert(
                        Span::new(kw_span.start, path_span.end),
                        "import CompactStandardLibrary".to_owned(),
                    );
                }
            }
            NodeTag::TypeGeneric if options.update_uint_ranges => {
                let name = ast.token_text(ast.node_main_token(node), source);
                if name != "Uint" {
                    continue;
                }
                let data = ast.node_data(node);
                let args: Vec<_> = ast.extra_nodes(data.lhs, data.rhs).collect();
                if args.len() != 1 || ast.node_tag(args[0]) != NodeTag::TypeRange {
                    continue;
                }
                let range_data = ast.node_data(args[0]);
                let rhs = NodeIndex(range_data.rhs);
                match ast.node_tag(rhs) {
                    NodeTag::TypeNat => {
                        let tok = ast.node_main_token(rhs);
                        let text = ast.token_text(tok, source);
                        if let Some(incremented) = increment_nat_literal(text) {
                            edits.insert(ast.token_span(tok), incremented);
                        }
                    }
                    NodeTag::TypeNamed => {
                        let tok = ast.node_main_token(rhs);
                        let ident = ast.token_text(tok, source);
                        let span = ast.token_span(tok);
                        warnings.push((
                            span.start,
                            CompactDiagnostic::warning(
                                file,
                                span,
                                format!(
                                    "Uint range end expressed as a reference to generic size `{ident}` is left unchanged and must be updated manually"
                                ),
                            ),
                        ));
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
}

/// Apply non-overlapping byte-span replacements to `source`.
fn apply_span_edits(source: &str, edits: &BTreeMap<Span, String>) -> String {
    let mut out = String::with_capacity(source.len());
    let mut cursor = 0usize;
    for (span, replacement) in edits {
        let start = span.start as usize;
        let end = span.end as usize;
        if start < cursor || end > source.len() || start > end {
            continue;
        }
        out.push_str(&source[cursor..start]);
        out.push_str(replacement);
        cursor = end;
    }
    out.push_str(&source[cursor..]);
    out
}

/// Increment a non-negative Compact integer literal (`decimal`, `0b`, `0o`, or `0x`) by 1,
/// preserving its radix prefix with arbitrary precision (supports bounds exceeding `u128`).
pub fn increment_nat_literal(raw: &str) -> Option<String> {
    let (prefix, radix, digits) =
        if let Some(rest) = raw.strip_prefix("0b").or_else(|| raw.strip_prefix("0B")) {
            ("0b", 2u8, rest)
        } else if let Some(rest) = raw.strip_prefix("0o").or_else(|| raw.strip_prefix("0O")) {
            ("0o", 8u8, rest)
        } else if let Some(rest) = raw.strip_prefix("0x").or_else(|| raw.strip_prefix("0X")) {
            ("0x", 16u8, rest)
        } else {
            ("", 10u8, raw)
        };

    if digits.is_empty() {
        return None;
    }

    let mut vals: Vec<u8> = Vec::with_capacity(digits.len());
    for b in digits.bytes() {
        let d = match b {
            b'0'..=b'9' => b - b'0',
            b'a'..=b'f' => 10 + (b - b'a'),
            b'A'..=b'F' => 10 + (b - b'A'),
            _ => return None,
        };
        if d >= radix {
            return None;
        }
        vals.push(d);
    }

    let mut carry = 1u8;
    for slot in vals.iter_mut().rev() {
        let sum = *slot + carry;
        if sum >= radix {
            *slot = sum - radix;
            carry = 1;
        } else {
            *slot = sum;
            carry = 0;
            break;
        }
    }
    if carry > 0 {
        vals.insert(0, carry);
    }

    // Strip redundant leading zeros (keeping a single `0` if needed).
    let first_nonzero = vals.iter().position(|&d| d != 0).unwrap_or(vals.len() - 1);
    let mut out = String::with_capacity(prefix.len() + vals.len() - first_nonzero);
    out.push_str(prefix);
    for &d in &vals[first_nonzero..] {
        let ch = match d {
            0..=9 => (b'0' + d) as char,
            10..=15 => (b'a' + (d - 10)) as char,
            _ => unreachable!(),
        };
        out.push(ch);
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use compact_span::SourceMap;
    use compact_test_utils::assert_compact_snapshot;

    use super::*;

    fn run_fixup(src: &str, update_uint_ranges: bool) -> String {
        let mut sm = SourceMap::new();
        let id = sm.add_file("test.compact", src);
        let file = sm.get(id);
        let out = fixup_single_file(
            file,
            &FixupOptions {
                line_length: 100,
                update_uint_ranges,
            },
        )
        .unwrap_or_else(|e| panic!("fixup failed: {e:?}"));
        out.formatted
    }

    #[test]
    fn increment_nat_preserves_radices_and_handles_big_ints() {
        assert_eq!(increment_nat_literal("0").as_deref(), Some("1"));
        assert_eq!(increment_nat_literal("99").as_deref(), Some("100"));
        assert_eq!(increment_nat_literal("0b111").as_deref(), Some("0b1000"));
        assert_eq!(increment_nat_literal("0o77").as_deref(), Some("0o100"));
        assert_eq!(increment_nat_literal("0xff").as_deref(), Some("0x100"));
        assert_eq!(increment_nat_literal("0X1F").as_deref(), Some("0x20"));
        assert_eq!(
            increment_nat_literal("9999999999999999999999999999999999999999").as_deref(),
            Some("10000000000000000000000000000000000000000")
        );
    }

    #[test]
    fn fixup_include_std_and_stdlib_aliases() {
        assert_compact_snapshot!(
            r#"
            pragma language_version >= 0.14.0;
            include "std";

            export circuit hash_pair(a: Field, b: Bytes<32>): [Field, Bytes<32>, Bytes<32>] {
              const h1 = transient_hash<Field>(a);
              const h2 = persistent_hash<Bytes<32>>(b);
              const t = native_token();
              const pk = own_public_key();
              const back = upgrade_from_transient(degrade_to_transient(pk.bytes));
              return [h1, h2, back];
            }
            "#,
            |src| run_fixup(src, false)
        );
    }

    #[test]
    fn fixup_ledger_op_aliases() {
        assert_compact_snapshot!(
            r#"
            import CompactStandardLibrary;

            export ledger counter: Counter;
            export ledger items: Set<QualifiedShieldedCoinInfo>;
            export ledger map_items: Map<Field, QualifiedShieldedCoinInfo>;
            export ledger list_items: List<QualifiedShieldedCoinInfo>;
            export ledger hmt: HistoricMerkleTree<2, Field>;

            constructor() {
              kernel.claim_contract_call(default<Bytes<32>>, default<Bytes<32>>, default<Field>);
              kernel.claim_zswap_nullifier(default<Bytes<32>>);
              counter.less_than(10);
              counter.reset_to_default();
              items.insert_coin(default<ShieldedCoinInfo>, default<Either<ZswapCoinPublicKey, ContractAddress>>);
              items.is_empty();
              map_items.insert_coin(1 as Field, default<ShieldedCoinInfo>, default<Either<ZswapCoinPublicKey, ContractAddress>>);
              map_items.insert_default(2 as Field);
              list_items.push_front_coin(default<ShieldedCoinInfo>, default<Either<ZswapCoinPublicKey, ContractAddress>>);
              list_items.pop_front();
              hmt.check_root(default<MerkleTreeDigest>);
              hmt.insert_hash(default<Bytes<32>>);
              hmt.is_full();
              hmt.reset_history();
              hmt.reset_to_default();
            }
            "#,
            |src| run_fixup(src, false)
        );
    }

    #[test]
    fn fixup_update_uint_ranges_and_generic_warning() {
        let mut sm = SourceMap::new();
        let src = r#"
            circuit f<#N>(a: Uint<0..9>, b: Uint<0..0xff>, c: Uint<0..0b111>, d: Uint<0..N>): Uint<0..0o77> {
              return 1;
            }
            export circuit run(): Uint<0..0o77> {
              return f<10>(1, 2, 3, 4);
            }
        "#;
        let id = sm.add_file("ranges.compact", src);
        let out = fixup_single_file(
            sm.get(id),
            &FixupOptions {
                line_length: 100,
                update_uint_ranges: true,
            },
        )
        .expect("fixup should succeed");

        assert!(out.formatted.contains("Uint<0..10>"), "{}", out.formatted);
        assert!(
            out.formatted.contains("Uint<0..0x100>"),
            "{}",
            out.formatted
        );
        assert!(
            out.formatted.contains("Uint<0..0b1000>"),
            "{}",
            out.formatted
        );
        assert!(
            out.formatted.contains("Uint<0..0o100>"),
            "{}",
            out.formatted
        );
        assert!(out.formatted.contains("Uint<0..N>"), "{}", out.formatted);
        assert_eq!(out.warnings.len(), 1);
        assert!(out.warnings[0].message.contains("generic size `N`"));
    }

    #[test]
    fn fixup_respects_local_shadowing() {
        let mut sm = SourceMap::new();
        let src = r#"
            import CompactStandardLibrary;

            circuit native_token(): Field {
              return 42;
            }

            circuit transientHash(x: Field): Field {
              return x + 1;
            }

            export circuit run(x: Field): [Field, Field] {
              const a = native_token();
              const b = transient_hash<Field>(x);
              return [a, b];
            }
        "#;
        let id = sm.add_file("shadow.compact", src);
        let out = fixup_single_file(sm.get(id), &FixupOptions::default())
            .expect("fixup should succeed with warning");

        // User-defined `native_token` must NOT be renamed.
        assert!(
            out.formatted.contains("const a = native_token();"),
            "{}",
            out.formatted
        );
        // `transient_hash` must NOT be renamed because `transientHash` is shadowed by a local circuit.
        assert!(
            out.formatted
                .contains("const b = transient_hash<Field>(x);"),
            "{}",
            out.formatted
        );
        assert_eq!(out.warnings.len(), 1);
        assert!(out.warnings[0].message.contains("not renaming reference"));
    }
}
