use compact::Cli;

fn main() -> miette::Result<()> {
    Cli::default().exec()
}
