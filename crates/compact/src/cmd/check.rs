use std::path::PathBuf;

use clap::Args;
use miette::miette;

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
    Err(miette!(
        "check is not yet implemented (source: {})",
        args.source.display()
    ))
}
