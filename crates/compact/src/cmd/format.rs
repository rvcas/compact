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
