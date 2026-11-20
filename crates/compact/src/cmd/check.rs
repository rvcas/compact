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
