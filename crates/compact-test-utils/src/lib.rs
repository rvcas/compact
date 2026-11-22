pub use indoc;
pub use insta;

/// Snapshot-test a Compact source snippet so the dedented Compact source renders
/// cleanly (multi-line, unescaped) directly inside the snapshot file instead of
/// capturing the inline Rust test expression.
#[macro_export]
macro_rules! assert_compact_snapshot {
    ($source:literal, $transform:expr $(,)?) => {{
        let __src: &str = $crate::indoc::indoc!($source);
        let __output = ($transform)(__src);
        let __rendered = format!("{}\n===\n{}", __src.trim_end(), __output.trim_end());
        $crate::insta::with_settings!({
            omit_expression => true,
        }, {
            $crate::insta::assert_snapshot!(__rendered);
        });
    }};
    (file: $source:expr, $transform:expr $(,)?) => {{
        let __src: &str = $source;
        let __output = ($transform)(__src);
        let __rendered = format!("{}\n===\n{}", __src.trim_end(), __output.trim_end());
        $crate::insta::with_settings!({
            omit_expression => true,
        }, {
            $crate::insta::assert_snapshot!(__rendered);
        });
    }};
    ($name:expr, $source:literal, $transform:expr $(,)?) => {{
        let __src: &str = $crate::indoc::indoc!($source);
        let __output = ($transform)(__src);
        let __rendered = format!("{}\n===\n{}", __src.trim_end(), __output.trim_end());
        $crate::insta::with_settings!({
            omit_expression => true,
        }, {
            $crate::insta::assert_snapshot!($name, __rendered);
        });
    }};
}
