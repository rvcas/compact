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
use compact_driver::BuildOptions;
use miette::miette;

#[derive(Debug, Clone, PartialEq, Eq, Args)]
pub struct BuildArgs {
    /// Path to the Compact source file
    pub source: PathBuf,

    /// Target output directory
    pub target: PathBuf,

    /// Skip ZK proving and verifier key generation
    #[arg(long)]
    pub skip_zk: bool,

    /// Maximum number of circuits to keygen concurrently (also reads COMPACT_JOBS)
    #[arg(short = 'j', long)]
    pub jobs: Option<usize>,
}

impl BuildArgs {
    pub fn exec(self) -> miette::Result<()> {
        build(self)
    }
}

pub fn build(args: BuildArgs) -> miette::Result<()> {
    let jobs = match args.jobs {
        Some(0) => return Err(miette!("--jobs must be at least 1")),
        Some(n) => Some(n),
        None => match std::env::var("COMPACT_JOBS") {
            Ok(raw) => {
                let parsed: usize = raw
                    .parse()
                    .map_err(|_| miette!("invalid COMPACT_JOBS value `{raw}`"))?;
                if parsed == 0 {
                    return Err(miette!("COMPACT_JOBS must be at least 1"));
                }
                Some(parsed)
            }
            Err(_) => None,
        },
    };

    compact_driver::build(&BuildOptions {
        source: args.source,
        target: args.target,
        skip_zk: args.skip_zk,
        jobs,
    })?;

    Ok(())
}
