# Compact Conformance Corpus

Vendored `.compact` contract suite imported from the upstream Midnight Compact repository at commit `32476c9b3eff131aaf60cf6bbe32a502d863a94f` (Apache-2.0; see [LICENSE](LICENSE)).

## Layout

- `test-contracts/`: Language conformance test contracts along with helper included/imported modules, indexed by `pass.txt` (188 positive entrypoints) and `fail.txt` (191 negative entrypoints).
- `test-center/`: Real-world reference contracts (`test-contracts/{bboard,coracle,counter,micro-dao,welcome}.compact`), composable cross-contract & event suites (`composable/`), and compiler test contract (`compact/test.compact`).
- `examples/`: ADT tests/exports, crypto/casts/commas/types/stdlib examples, and formatter idempotence inputs (`formatter/input/`).
- `fixup/`: Upstream migration test contracts (`camelCase/old/` and multi-file `fixup/bugs/structured/`).

Executed directly by `crates/compact-driver/tests/conformance.rs` as part of `cargo test`.
