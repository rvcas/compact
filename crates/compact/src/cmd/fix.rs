use std::path::PathBuf;

use clap::Args;
use compact_driver::{FixupFileOptions, fixup_file};
use miette::Report;

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

    /// Increment constant `Uint<0..N>` range upper bounds by 1 and warn on generic size bounds
    #[arg(long = "update-uint-ranges", visible_alias = "update-Uint-ranges")]
    pub update_uint_ranges: bool,

    /// Search path list for resolving `include` and external `import` files
    #[arg(long)]
    pub compact_path: Option<String>,
}

impl FixArgs {
    pub fn exec(self) -> miette::Result<()> {
        fix(self)
    }
}

pub fn fix(args: FixArgs) -> miette::Result<()> {
    let raw_compact_path = args
        .compact_path
        .or_else(|| std::env::var("COMPACT_PATH").ok());
    let compact_path = raw_compact_path
        .as_deref()
        .map(|raw| std::env::split_paths(raw).collect())
        .unwrap_or_default();

    let output = fixup_file(&FixupFileOptions {
        source: args.source,
        target: args.target.clone(),
        line_length: args.line_length,
        update_uint_ranges: args.update_uint_ranges,
        compact_path,
    })?;

    for warning in output.warnings {
        eprintln!("{:?}", Report::new(warning));
    }

    if args.target.is_none() {
        print!("{}", output.formatted);
    }
    Ok(())
}
