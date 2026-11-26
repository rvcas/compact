// This file is part of Compact.
// Copyright (C) 2025 Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

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
