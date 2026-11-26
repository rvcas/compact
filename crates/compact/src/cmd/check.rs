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
use compact_driver::CheckOptions;

#[derive(Debug, Clone, PartialEq, Eq, Args)]
pub struct CheckArgs {
    /// Path to the Compact source file
    pub source: PathBuf,
}

impl CheckArgs {
    pub fn exec(self) -> miette::Result<()> {
        check(self)
    }
}

pub fn check(args: CheckArgs) -> miette::Result<()> {
    compact_driver::check(&CheckOptions {
        source: args.source,
    })?;

    Ok(())
}
