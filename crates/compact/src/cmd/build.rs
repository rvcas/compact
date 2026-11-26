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
