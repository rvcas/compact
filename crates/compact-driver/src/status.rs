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

use std::io::{self, IsTerminal, Write};
use std::sync::Mutex;

/// Cargo-style status/progress reporter, cleanly separated from `miette` diagnostics.
pub trait StatusReporter: Send + Sync {
    fn status(&self, verb: &str, detail: &str);
}

/// Terminal reporter printing Cargo-style right-aligned 12-char verbs to stderr.
pub struct TermStatusReporter {
    color: bool,
    lock: Mutex<()>,
}

impl Default for TermStatusReporter {
    fn default() -> Self {
        Self::new()
    }
}

impl TermStatusReporter {
    pub fn new() -> Self {
        Self {
            color: io::stderr().is_terminal(),
            lock: Mutex::new(()),
        }
    }
}

impl StatusReporter for TermStatusReporter {
    fn status(&self, verb: &str, detail: &str) {
        let _guard = self.lock.lock().unwrap();
        let mut stderr = io::stderr().lock();
        if self.color {
            let _ = writeln!(stderr, "\x1b[1;32m{verb:>12}\x1b[0m {detail}");
        } else {
            let _ = writeln!(stderr, "{verb:>12} {detail}");
        }
    }
}

/// No-op status reporter for tests or quiet mode.
#[derive(Debug, Default, Clone, Copy)]
pub struct SilentStatusReporter;

impl StatusReporter for SilentStatusReporter {
    fn status(&self, _verb: &str, _detail: &str) {}
}
