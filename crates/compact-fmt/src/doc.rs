//! Wadler-Lindig `Doc` intermediate representation and layout renderer for `compact-fmt`.

/// A pretty-printable document fragment.
#[derive(Debug, Clone)]
pub enum Doc {
    Nil,
    Text(String),
    /// Renders as `flat` in Flat mode, or a newline + current indent in Break mode.
    SoftLine {
        flat: &'static str,
    },
    /// Always renders as a newline + current indent (forces enclosing `Group` to break).
    HardLine,
    /// Renders as a single blank line (two newlines) + current indent (forces enclosing `Group` to break).
    BlankLine,
    Concat(Vec<Doc>),
    /// Increases indentation by `usize` spaces for line breaks inside the inner doc.
    Indent(usize, Box<Doc>),
    /// Tries rendering the inner doc in Flat mode if it fits on the remaining line;
    /// otherwise renders it in Break mode.
    Group(Box<Doc>),
    /// A `// ...` line comment. Forces enclosing groups to break so code is never placed after it
    /// on the same line.
    LineComment(String),
}

impl Doc {
    pub fn text(s: impl Into<String>) -> Self {
        let s = s.into();
        if s.is_empty() {
            Self::Nil
        } else {
            Self::Text(s)
        }
    }

    pub fn space_or_line() -> Self {
        Self::SoftLine { flat: " " }
    }

    pub fn soft_line() -> Self {
        Self::SoftLine { flat: "" }
    }

    pub fn concat(mut docs: Vec<Doc>) -> Self {
        docs.retain(|d| !matches!(d, Self::Nil));
        match docs.len() {
            0 => Self::Nil,
            1 => docs.pop().unwrap(),
            _ => Self::Concat(docs),
        }
    }

    pub fn indent(delta: usize, doc: Doc) -> Self {
        match doc {
            Self::Nil => Self::Nil,
            other => Self::Indent(delta, Box::new(other)),
        }
    }

    pub fn group(doc: Doc) -> Self {
        match doc {
            Self::Nil => Self::Nil,
            other => Self::Group(Box::new(other)),
        }
    }

    /// Format a delimited comma-separated list (`open`, items, `close`) that stays on one line
    /// when it fits within `line_length` and breaks to 2-space-indented lines when it overflows.
    ///
    /// `flat_pad` is placed inside `open`/`close` when rendered flat (e.g. `" "` for `{ a, b }`,
    /// `""` for `(a, b)` or `[a, b]`).
    pub fn delimited_list(
        open: &str,
        items: Vec<Doc>,
        close: &str,
        flat_pad: &'static str,
    ) -> Self {
        if items.is_empty() {
            return Self::text(format!("{open}{close}"));
        }
        let mut inner = Vec::with_capacity(items.len() * 3);
        inner.push(Self::SoftLine { flat: flat_pad });
        for (i, item) in items.into_iter().enumerate() {
            if i > 0 {
                inner.push(Self::text(","));
                inner.push(Self::space_or_line());
            }
            inner.push(item);
        }
        Self::group(Self::concat(vec![
            Self::text(open),
            Self::indent(2, Self::concat(inner)),
            Self::SoftLine { flat: flat_pad },
            Self::text(close),
        ]))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mode {
    Flat,
    Break,
}

/// Render `doc` to a formatted string targeting `line_length` columns.
pub fn render(doc: &Doc, line_length: usize) -> String {
    let mut out = String::new();
    let mut col: usize = 0;
    let mut at_line_start = true;
    let mut pending_indent: usize = 0;

    // Explicit worklist stack (top = next item to process).
    let mut stack: Vec<(usize, Mode, &Doc)> = vec![(0, Mode::Break, doc)];

    while let Some((indent, mode, cur)) = stack.pop() {
        match cur {
            Doc::Nil => {}
            Doc::Text(s) => {
                if at_line_start {
                    for _ in 0..pending_indent {
                        out.push(' ');
                    }
                    col = pending_indent;
                    at_line_start = false;
                }
                out.push_str(s);
                if let Some(last_nl) = s.rfind('\n') {
                    col = s[last_nl + 1..].chars().count();
                } else {
                    col += s.chars().count();
                }
            }
            Doc::LineComment(s) => {
                if at_line_start {
                    for _ in 0..pending_indent {
                        out.push(' ');
                    }
                    col = pending_indent;
                    at_line_start = false;
                }
                out.push_str(s);
                col += s.chars().count();
            }
            Doc::SoftLine { flat } => match mode {
                Mode::Flat => {
                    if !flat.is_empty() {
                        if at_line_start {
                            for _ in 0..pending_indent {
                                out.push(' ');
                            }
                            col = pending_indent;
                            at_line_start = false;
                        }
                        out.push_str(flat);
                        col += flat.len();
                    }
                }
                Mode::Break => {
                    out.push('\n');
                    at_line_start = true;
                    pending_indent = indent;
                    col = 0;
                }
            },
            Doc::HardLine => {
                if !out.is_empty() && (!out.ends_with('\n') || !at_line_start) {
                    out.push('\n');
                }
                at_line_start = true;
                pending_indent = indent;
                col = 0;
            }
            Doc::BlankLine => {
                if !out.is_empty() {
                    if out.ends_with("\n\n") {
                        // Already have a blank line; do not double up.
                    } else if out.ends_with('\n') {
                        out.push('\n');
                    } else {
                        out.push_str("\n\n");
                    }
                }
                at_line_start = true;
                pending_indent = indent;
                col = 0;
            }
            Doc::Concat(parts) => {
                for part in parts.iter().rev() {
                    stack.push((indent, mode, part));
                }
            }
            Doc::Indent(delta, inner) => {
                stack.push((indent + delta, mode, inner));
            }
            Doc::Group(inner) => {
                let effective_col = if at_line_start { pending_indent } else { col };
                let remaining = line_length as isize - effective_col as isize;
                if fits(remaining, inner, &stack) {
                    stack.push((indent, Mode::Flat, inner));
                } else {
                    stack.push((indent, Mode::Break, inner));
                }
            }
        }
    }

    if !out.is_empty() && !out.ends_with('\n') {
        out.push('\n');
    }
    out
}

/// Check whether `candidate` (in Flat mode), followed by any remaining flat tokens on `outer_stack`
/// up to the next line break, fits within `remaining` columns.
fn fits<'a>(
    mut remaining: isize,
    candidate: &'a Doc,
    outer_stack: &[(usize, Mode, &'a Doc)],
) -> bool {
    if remaining < 0 {
        return false;
    }
    let mut check: Vec<(Mode, &'a Doc)> = Vec::with_capacity(16);
    check.push((Mode::Flat, candidate));
    let mut outer_idx = outer_stack.len();

    while remaining >= 0 {
        let next = if let Some(item) = check.pop() {
            item
        } else if outer_idx > 0 {
            outer_idx -= 1;
            let (_, mode, doc) = outer_stack[outer_idx];
            (mode, doc)
        } else {
            return true;
        };

        let (mode, doc) = next;
        match doc {
            Doc::Nil => {}
            Doc::Text(s) => {
                if let Some(nl) = s.find('\n') {
                    // Multiline string literal or block comment forces enclosing groups to break
                    // if we are still checking the candidate group (Flat mode).
                    remaining -= s[..nl].chars().count() as isize;
                    if mode == Mode::Flat {
                        return false;
                    }
                    return remaining >= 0;
                }
                remaining -= s.chars().count() as isize;
            }
            Doc::LineComment(s) => match mode {
                // Inside a Flat group, a `//` comment forces the group to break so later code
                // inside the group is not swallowed into the comment.
                Mode::Flat => return false,
                // Outside the candidate group (trailing comment on the same line), it consumes
                // its width and terminates the line.
                Mode::Break => {
                    remaining -= s.chars().count() as isize;
                    return remaining >= 0;
                }
            },
            Doc::SoftLine { flat } => match mode {
                Mode::Flat => remaining -= flat.len() as isize,
                Mode::Break => return true,
            },
            Doc::HardLine | Doc::BlankLine => match mode {
                Mode::Flat => return false,
                Mode::Break => return true,
            },
            Doc::Concat(parts) => {
                for part in parts.iter().rev() {
                    check.push((mode, part));
                }
            }
            Doc::Indent(_, inner) => {
                check.push((mode, inner));
            }
            Doc::Group(inner) => {
                check.push((Mode::Flat, inner));
            }
        }
    }

    false
}
