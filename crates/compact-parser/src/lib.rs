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

pub mod lexer;
pub mod parser;

pub use parser::{ParseResult, parse};

#[cfg(test)]
mod tests {
    use compact_span::SourceMap;
    use compact_test_utils::assert_compact_snapshot;

    use super::parse;

    fn parse_and_dump(src: &str) -> String {
        let mut sm = SourceMap::new();
        let file = sm.add_file("test.compact", src);
        let result = parse(sm.get(file));
        assert!(
            !result.diagnostics.has_errors(),
            "unexpected parse errors: {:?}",
            result.diagnostics
        );
        result.ast.dump(src)
    }

    #[test]
    fn parse_counter_contract() {
        assert_compact_snapshot!(
            r#"
            // Counter example
            import CompactStandardLibrary;

            export ledger round: Counter;

            export circuit increment(): [] {
              round.increment(1);
            }
            "#,
            parse_and_dump
        );
    }

    #[test]
    fn parse_pure_add_circuit() {
        assert_compact_snapshot!(
            r#"
            export circuit add(a: Field, b: Field): Field {
              return a + b;
            }
            "#,
            parse_and_dump
        );
    }
}
