use clap::Subcommand;

pub mod build;
pub mod check;
pub mod fix;
pub mod format;

pub const DEFAULT_LINE_LENGTH: usize = 100;

#[derive(Debug, Clone, PartialEq, Eq, Subcommand)]
pub enum Cmd {
    /// Compile a Compact contract
    #[command(visible_alias = "compile", visible_alias = "c")]
    Build(build::BuildArgs),

    /// Parse and type-check a Compact contract without generating outputs
    Check(check::CheckArgs),

    /// Format a Compact source file
    #[command(visible_alias = "fmt")]
    Format(format::FormatArgs),

    /// Apply language migrations and format a Compact source file
    #[command(visible_alias = "fixup")]
    Fix(fix::FixArgs),
}

impl Cmd {
    pub fn exec(self) -> miette::Result<()> {
        match self {
            Self::Build(args) => args.exec(),
            Self::Check(args) => args.exec(),
            Self::Format(args) => args.exec(),
            Self::Fix(args) => args.exec(),
        }
    }
}
