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

use compact_ast::{Ast, NodeIndex, NodeTag, TokenTag};
use compact_diagnostics::{CompactDiagnostic, DiagnosticBag};
use compact_span::SourceFile;

pub const LANGUAGE_VERSION: (u32, u32, u32) = (0, 28, 0);
pub const COMPILER_VERSION: (u32, u32, u32) = (0, 36, 108);

/// Check a `pragma <name> <version_expr>;` declaration against the current language/compiler version.
pub fn check_pragma(
    file: &SourceFile,
    ast: &Ast,
    node: NodeIndex,
    diagnostics: &mut DiagnosticBag,
) {
    let decl = ast.pragma_decl(node);
    let name = ast.token_text(decl.name_token, file.text());
    let current = match name {
        "language_version" => LANGUAGE_VERSION,
        "compiler_version" => COMPILER_VERSION,
        other => {
            diagnostics.push(CompactDiagnostic::error(
                file,
                ast.token_span(decl.name_token),
                format!("unrecognized pragma setting `{other}`"),
            ));
            return;
        }
    };

    if let Some(ok) = eval_version_expr(file, ast, decl.expr, current, diagnostics)
        && !ok
    {
        let expr_text = ast.node_span(decl.expr).slice(file.text());
        diagnostics.push(CompactDiagnostic::error(
            file,
            ast.node_span(node),
            format!(
                "pragma `{name} {expr_text}` is not satisfied by current version {}.{}.{}",
                current.0, current.1, current.2
            ),
        ));
    }
}

#[derive(Debug, Clone, Copy)]
struct VersionPattern {
    major: u32,
    minor: Option<u32>,
    patch: Option<u32>,
}

impl VersionPattern {
    fn matches_exact(self, cur: (u32, u32, u32)) -> bool {
        if cur.0 != self.major {
            return false;
        }
        if let Some(m) = self.minor
            && cur.1 != m
        {
            return false;
        }
        if let Some(p) = self.patch
            && cur.2 != p
        {
            return false;
        }
        true
    }

    fn lower_bound(self) -> (u32, u32, u32) {
        (self.major, self.minor.unwrap_or(0), self.patch.unwrap_or(0))
    }

    fn upper_bound(self) -> (u32, u32, u32) {
        (
            self.major,
            self.minor.unwrap_or(u32::MAX),
            self.patch.unwrap_or(u32::MAX),
        )
    }
}

fn parse_version_atom(
    file: &SourceFile,
    ast: &Ast,
    node: NodeIndex,
    diagnostics: &mut DiagnosticBag,
) -> Option<VersionPattern> {
    let span = ast.node_span(node);
    let raw = span.slice(file.text());
    let parts: Result<Vec<u32>, _> = raw.split('.').map(str::parse::<u32>).collect();
    let Ok(parts) = parts else {
        diagnostics.push(CompactDiagnostic::error(
            file,
            span,
            format!("invalid version literal `{raw}`"),
        ));
        return None;
    };
    match parts.as_slice() {
        [major] => Some(VersionPattern {
            major: *major,
            minor: None,
            patch: None,
        }),
        [major, minor] => Some(VersionPattern {
            major: *major,
            minor: Some(*minor),
            patch: None,
        }),
        [major, minor, patch] => Some(VersionPattern {
            major: *major,
            minor: Some(*minor),
            patch: Some(*patch),
        }),
        _ => {
            diagnostics.push(CompactDiagnostic::error(
                file,
                span,
                format!("version `{raw}` has too many components"),
            ));
            None
        }
    }
}

fn eval_version_expr(
    file: &SourceFile,
    ast: &Ast,
    node: NodeIndex,
    cur: (u32, u32, u32),
    diagnostics: &mut DiagnosticBag,
) -> Option<bool> {
    let data = ast.node_data(node);
    match ast.node_tag(node) {
        NodeTag::VersionAtom => {
            let pat = parse_version_atom(file, ast, node, diagnostics)?;
            Some(pat.matches_exact(cur))
        }
        NodeTag::VersionUnary => {
            let op = ast.token_tag(ast.node_main_token(node));
            let pat = parse_version_atom(file, ast, NodeIndex(data.lhs), diagnostics)?;
            Some(match op {
                TokenTag::Bang => !pat.matches_exact(cur),
                TokenTag::LAngle => cur < pat.lower_bound(),
                TokenTag::LtEq => cur <= pat.upper_bound(),
                TokenTag::RAngle => cur > pat.upper_bound(),
                TokenTag::GtEq => cur >= pat.lower_bound(),
                _ => false,
            })
        }
        NodeTag::VersionBinary => {
            let op = ast.token_tag(ast.node_main_token(node));
            let lhs = eval_version_expr(file, ast, NodeIndex(data.lhs), cur, diagnostics)?;
            let rhs = eval_version_expr(file, ast, NodeIndex(data.rhs), cur, diagnostics)?;
            Some(match op {
                TokenTag::AmpAmp => lhs && rhs,
                TokenTag::PipePipe => lhs || rhs,
                _ => false,
            })
        }
        _ => None,
    }
}
