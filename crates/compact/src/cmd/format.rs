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

use std::path::PathBuf;

use clap::Args;
use compact_driver::FormatFileOptions;

use super::DEFAULT_LINE_LENGTH;

#[derive(Debug, Clone, PartialEq, Eq, Args)]
pub struct FormatArgs {
    /// Path to the Compact source file
    pub source: PathBuf,

    /// Optional target file (writes to stdout when omitted)
    pub target: Option<PathBuf>,

    /// Target maximum line length
    #[arg(long, default_value_t = DEFAULT_LINE_LENGTH)]
    pub line_length: usize,
}

impl FormatArgs {
    pub fn exec(self) -> miette::Result<()> {
        format(self)
    }
}

pub fn format(args: FormatArgs) -> miette::Result<()> {
    let write_stdout = args.target.is_none();

    let formatted = compact_driver::format_file(&FormatFileOptions {
        source: args.source,
        target: args.target,
        line_length: args.line_length,
    })?;

    if write_stdout {
        print!("{formatted}");
    }

    Ok(())
}
