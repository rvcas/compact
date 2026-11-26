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

use clap::Subcommand;

pub mod build;
pub mod check;
pub mod fix;
pub mod format;

pub const DEFAULT_LINE_LENGTH: usize = 100;

#[derive(Debug, Clone, PartialEq, Eq, Subcommand)]
pub enum Cmd {
    /// Compile a Compact contract
    #[command(visible_alias = "compile", visible_alias = "c")]
    Build(build::BuildArgs),

    /// Parse and type-check a Compact contract without generating outputs
    Check(check::CheckArgs),

    /// Format a Compact source file
    #[command(visible_alias = "fmt")]
    Format(format::FormatArgs),

    /// Apply language migrations and format a Compact source file
    #[command(visible_alias = "fixup")]
    Fix(fix::FixArgs),
}

impl Cmd {
    pub fn exec(self) -> miette::Result<()> {
        match self {
            Self::Build(args) => args.exec(),
            Self::Check(args) => args.exec(),
            Self::Format(args) => args.exec(),
            Self::Fix(args) => args.exec(),
        }
    }
}
