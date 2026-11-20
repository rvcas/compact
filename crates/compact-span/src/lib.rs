use std::path::{Path, PathBuf};
use std::sync::Arc;

use miette::{NamedSource, SourceSpan};

/// Compact handle identifying a loaded source file inside a [`SourceMap`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct FileId(pub u32);

/// Half-open byte offset range `[start, end)` within a single source file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub const EMPTY: Self = Self { start: 0, end: 0 };

    #[inline]
    pub const fn new(start: u32, end: u32) -> Self {
        Self { start, end }
    }

    #[inline]
    pub const fn len(self) -> u32 {
        self.end.saturating_sub(self.start)
    }

    #[inline]
    pub const fn is_empty(self) -> bool {
        self.start >= self.end
    }

    #[inline]
    pub const fn merge(self, other: Self) -> Self {
        let start = if self.start < other.start {
            self.start
        } else {
            other.start
        };
        let end = if self.end > other.end {
            self.end
        } else {
            other.end
        };
        Self { start, end }
    }

    #[inline]
    pub fn slice(self, source: &str) -> &str {
        &source[self.start as usize..self.end as usize]
    }
}

impl From<Span> for SourceSpan {
    #[inline]
    fn from(span: Span) -> Self {
        SourceSpan::new((span.start as usize).into(), span.len() as usize)
    }
}

/// 1-based line and column location.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LineCol {
    pub line: u32,
    pub col: u32,
}

/// A single source file with precomputed line-start byte offsets for O(log N)
/// byte-offset -> line/column lookups.
#[derive(Debug, Clone)]
pub struct SourceFile {
    pub id: FileId,
    pub name: String,
    pub path: Option<PathBuf>,
    pub text: Arc<str>,
    line_starts: Vec<u32>,
}

impl SourceFile {
    pub fn new(id: FileId, name: impl Into<String>, path: Option<PathBuf>, text: impl Into<Arc<str>>) -> Self {
        let text: Arc<str> = text.into();
        let line_starts = compute_line_starts(&text);
        Self {
            id,
            name: name.into(),
            path,
            text,
            line_starts,
        }
    }

    #[inline]
    pub fn text(&self) -> &str {
        &self.text
    }

    #[inline]
    pub fn slice(&self, span: Span) -> &str {
        span.slice(&self.text)
    }

    /// Convert a byte offset into a 1-based `(line, col)` pair.
    pub fn line_col(&self, offset: u32) -> LineCol {
        let line_idx = match self.line_starts.binary_search(&offset) {
            Ok(idx) => idx,
            Err(idx) => idx.saturating_sub(1),
        };
        let line_start = self.line_starts[line_idx];
        let col = self.text[line_start as usize..offset.min(self.text.len() as u32) as usize]
            .chars()
            .count() as u32
            + 1;
        LineCol {
            line: line_idx as u32 + 1,
            col,
        }
    }

    pub fn named_source(&self) -> NamedSource<Arc<str>> {
        NamedSource::new(&self.name, Arc::clone(&self.text))
    }
}

fn compute_line_starts(text: &str) -> Vec<u32> {
    let mut starts = vec![0];
    for (idx, byte) in text.bytes().enumerate() {
        if byte == b'\n' {
            starts.push((idx + 1) as u32);
        }
    }
    starts
}

/// Flat table of all source files loaded during a compilation session.
#[derive(Debug, Default, Clone)]
pub struct SourceMap {
    files: Vec<SourceFile>,
}

impl SourceMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_file(&mut self, name: impl Into<String>, text: impl Into<Arc<str>>) -> FileId {
        let id = FileId(self.files.len() as u32);
        self.files.push(SourceFile::new(id, name, None, text));
        id
    }

    pub fn add_disk_file(&mut self, path: &Path, text: impl Into<Arc<str>>) -> FileId {
        let id = FileId(self.files.len() as u32);
        let name = path.display().to_string();
        self.files
            .push(SourceFile::new(id, name, Some(path.to_path_buf()), text));
        id
    }

    #[inline]
    pub fn get(&self, id: FileId) -> &SourceFile {
        &self.files[id.0 as usize]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn line_col_lookup() {
        let mut sm = SourceMap::new();
        let id = sm.add_file("test.compact", "abc\ndef\nghi");
        let file = sm.get(id);
        assert_eq!(file.line_col(0), LineCol { line: 1, col: 1 });
        assert_eq!(file.line_col(2), LineCol { line: 1, col: 3 });
        assert_eq!(file.line_col(4), LineCol { line: 2, col: 1 });
        assert_eq!(file.line_col(8), LineCol { line: 3, col: 1 });
    }
}
