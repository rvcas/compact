use std::path::PathBuf;

use clap::Args;
use miette::miette;

use super::DEFAULT_LINE_LENGTH;

#[derive(Debug, Clone, PartialEq, Eq, Args)]
pub struct FixArgs {
    /// Path to the Compact source file
    pub source: PathBuf,

    /// Optional target file (writes to stdout when omitted)
    pub target: Option<PathBuf>,

    /// Target maximum line length
    #[arg(long, default_value_t = DEFAULT_LINE_LENGTH)]
    pub line_length: usize,
}

impl FixArgs {
    pub fn exec(self) -> miette::Result<()> {
        fix(self)
    }
}

pub fn fix(args: FixArgs) -> miette::Result<()> {
    Err(miette!(
        "fix is not yet implemented (source: {})",
        args.source.display()
    ))
}
