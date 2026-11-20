use std::io::{self, IsTerminal, Write};
use std::sync::Mutex;

/// Cargo-style status/progress reporter, cleanly separated from `miette` diagnostics.
pub trait StatusReporter: Send + Sync {
    fn status(&self, verb: &str, detail: &str);
}

/// Terminal reporter printing Cargo-style right-aligned 12-char verbs to stderr.
pub struct TermStatusReporter {
    color: bool,
    lock: Mutex<()>,
}

impl Default for TermStatusReporter {
    fn default() -> Self {
        Self::new()
    }
}

impl TermStatusReporter {
    pub fn new() -> Self {
        Self {
            color: io::stderr().is_terminal(),
            lock: Mutex::new(()),
        }
    }
}

impl StatusReporter for TermStatusReporter {
    fn status(&self, verb: &str, detail: &str) {
        let _guard = self.lock.lock().unwrap();
        let mut stderr = io::stderr().lock();
        if self.color {
            let _ = writeln!(stderr, "\x1b[1;32m{verb:>12}\x1b[0m {detail}");
        } else {
            let _ = writeln!(stderr, "{verb:>12} {detail}");
        }
    }
}

/// No-op status reporter for tests or quiet mode.
#[derive(Debug, Default, Clone, Copy)]
pub struct SilentStatusReporter;

impl StatusReporter for SilentStatusReporter {
    fn status(&self, _verb: &str, _detail: &str) {}
}
