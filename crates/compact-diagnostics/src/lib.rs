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

use std::sync::Arc;

use compact_span::{SourceFile, Span};
use miette::{Diagnostic, LabeledSpan, NamedSource, Severity};
use thiserror::Error;

/// A structured compiler diagnostic renderable directly via `miette`.
#[derive(Debug, Clone, Error, Diagnostic)]
#[error("{message}")]
pub struct CompactDiagnostic {
    pub message: String,

    #[source_code]
    pub src: NamedSource<Arc<str>>,

    #[label(collection)]
    pub labels: Vec<LabeledSpan>,

    #[help]
    pub help: Option<String>,

    pub severity: Severity,
}

impl CompactDiagnostic {
    pub fn error(file: &SourceFile, span: Span, message: impl Into<String>) -> Self {
        Self {
            labels: vec![LabeledSpan::new_primary_with_span(None, span)],
            message: message.into(),
            src: file.named_source(),
            help: None,
            severity: Severity::Error,
        }
    }

    pub fn warning(file: &SourceFile, span: Span, message: impl Into<String>) -> Self {
        Self {
            labels: vec![LabeledSpan::new_primary_with_span(None, span)],
            message: message.into(),
            src: file.named_source(),
            help: None,
            severity: Severity::Warning,
        }
    }

    pub fn with_primary_label(mut self, label: impl Into<String>) -> Self {
        if let Some(first) = self.labels.first_mut() {
            let span = (first.offset(), first.len());
            *first = LabeledSpan::new_primary_with_span(Some(label.into()), span);
        }
        self
    }

    pub fn with_help(mut self, help: impl Into<String>) -> Self {
        self.help = Some(help.into());
        self
    }

    pub fn with_secondary_label(mut self, span: Span, label: impl Into<String>) -> Self {
        self.labels.push(LabeledSpan::at(span, label.into()));
        self
    }

    pub fn is_error(&self) -> bool {
        matches!(self.severity, Severity::Error)
    }
}

/// Collection of diagnostics accumulated during a compilation phase.
#[derive(Debug, Default, Error, Diagnostic)]
#[error("compilation failed with {} error(s)", self.error_count())]
pub struct DiagnosticBag {
    #[related]
    pub diagnostics: Vec<CompactDiagnostic>,
}

impl DiagnosticBag {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push(&mut self, diagnostic: CompactDiagnostic) {
        self.diagnostics.push(diagnostic);
    }

    pub fn extend(&mut self, other: Self) {
        self.diagnostics.extend(other.diagnostics);
    }

    pub fn error_count(&self) -> usize {
        self.diagnostics.iter().filter(|d| d.is_error()).count()
    }

    pub fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(|d| d.is_error())
    }

    pub fn is_empty(&self) -> bool {
        self.diagnostics.is_empty()
    }

    pub fn into_result<T>(self, value: T) -> Result<T, Self> {
        if self.has_errors() {
            return Err(self);
        }
        Ok(value)
    }
}
