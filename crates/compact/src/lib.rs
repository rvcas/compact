use clap::Parser;

pub mod cmd;

/// The Compact smart contract compiler toolchain.
#[derive(Debug, Clone, PartialEq, Eq, Parser)]
#[command(name = "compact", version, about)]
pub struct Cli {
    #[command(subcommand)]
    pub cmd: cmd::Cmd,
}

impl Default for Cli {
    fn default() -> Self {
        Self::parse()
    }
}

impl Cli {
    pub fn exec(self) -> miette::Result<()> {
        self.cmd.exec()
    }
}
