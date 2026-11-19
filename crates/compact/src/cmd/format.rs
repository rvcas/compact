use std::path::PathBuf;

use clap::Args;
use miette::miette;

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
    Err(miette!(
        "format is not yet implemented (source: {})",
        args.source.display()
    ))
}
