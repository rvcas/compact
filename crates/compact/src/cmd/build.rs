use std::path::PathBuf;

use clap::Args;
use compact_driver::BuildOptions;

#[derive(Debug, Clone, PartialEq, Eq, Args)]
pub struct BuildArgs {
    /// Path to the Compact source file
    pub source: PathBuf,

    /// Target output directory
    pub target: PathBuf,

    /// Skip ZK proving and verifier key generation
    #[arg(long)]
    pub skip_zk: bool,
}

impl BuildArgs {
    pub fn exec(self) -> miette::Result<()> {
        build(self)
    }
}

pub fn build(args: BuildArgs) -> miette::Result<()> {
    compact_driver::build(&BuildOptions {
        source: args.source,
        target: args.target,
        skip_zk: args.skip_zk,
    })?;

    Ok(())
}
