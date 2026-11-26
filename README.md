# Compact (Rust)

A pure-Rust port of the [Midnight](https://midnight.network) Compact smart contract compiler toolchain (`build`/`check`, `format`, and `fix`/`fixup`), ported from the Chez Scheme Nanopass reference compiler with zero JavaScript/Node.js build dependencies.

## Highlights

- **Full compiler pipeline in pure Rust**:
  - Hand-written lexer & recursive-descent parser targeting a Zig-inspired Structure-of-Arrays (SoA) AST powered by `soa-rs`
  - Complete semantic analysis, module/include loading, generics, circuit overloading, embedded `CompactStandardLibrary`, and Witness Protection Pass (WPP / `disclose(...)`)
  - Flattened SSA circuit IR with fixed-point optimization passes (copy/constant propagation, native-field folding, boolean/`CondSelect` specialization, CSE, dead-code elimination, and dense variable compaction)
  - Direct `midnight-zkir` (v3.1) JSON + `.bzkir` codegen and pipelined, deduplicated, bounded-concurrency Halo2 proving/verifying key generation (`--jobs`)
  - Pure-Rust TypeScript/JavaScript/declaration/source-map emission via `oxc` (`index.js`, `index.d.ts`, `index.js.map`)
  - `contract-info.json` and `contract-manifest.json` artifact emission
- **Formatter & Migrator**:
  - Wadler-Lindig `Doc`-based pretty-printer (`compact format`) honoring `--line-length` with comment & blank-line fidelity
  - Upstream-parity code fixer/migrator (`compact fix`) handling `include "std";` rewrites, `--update-uint-ranges`, and scope-accurate stdlib/ledger camelCase migrations
- **First-class CLI & Diagnostics**:
  - `clap` CLI with `miette` source-annotated error & warning rendering and separate Cargo-style progress output
- **Conformance Suite**:
  - 100% pass/fail conformance against the vendored 468-contract upstream Compact corpus (`tests/conformance/`), plus multi-width formatter idempotence, upstream fixup migration parity, and Halo2 synthesis checks.

## CLI Usage

```sh
# Compile a contract (generates zkir/, keys/, contract/, and compiler/ artifacts)
cargo run -p compact -- build examples/counter.compact out/counter

# Compile without ZK proving/verifying key generation
cargo run -p compact -- build --skip-zk examples/counter.compact out/counter

# Control parallel keygen concurrency (also reads COMPACT_JOBS)
cargo run -p compact -- build --jobs 4 examples/election.compact out/election

# Type-check and run witness protection checks without emitting artifacts
cargo run -p compact -- check examples/counter.compact

# Format a Compact file (writes to stdout when target is omitted)
cargo run -p compact -- format --line-length 100 examples/counter.compact

# Migrate deprecated Compact syntax/names and format
cargo run -p compact -- fix examples/counter.compact
cargo run -p compact -- fix --update-uint-ranges path/to/old.compact path/to/fixed.compact
```

Aliases: `build` (`compile`, `c`), `format` (`fmt`), `fix` (`fixup`).

## Workspace Layout

```text
crates/
  compact/               CLI binary & clap command handlers
  compact-span/          SourceMap, FileId, Span, and line/column lookup
  compact-diagnostics/   Structured miette diagnostics & DiagnosticBag
  compact-ast/           Zig-inspired SoA AST (soa-rs) & literal utilities
  compact-parser/        Lexer & recursive-descent parser
  compact-hir/           Typed HIR, ledger ADTs, curves, and contract interfaces
  compact-sema/          Type checker, module loader, embedded stdlib, aliases & WPP
  compact-circuit/       HIR-to-SSA circuit lowering & fixed-point SSA optimizer
  compact-codegen-zkir/  ZKIR v3.1 JSON/bzkir emitter & pipelined parallel Halo2 keygen
  compact-codegen-ts/    oxc-powered JS, .d.ts, and VLQ source-map codegen
  compact-artifacts/     contract-info.json & contract-manifest.json emitters
  compact-fmt/           Wadler-Lindig Doc formatter with comment preservation
  compact-fixup/         Language migrator & code fixer
  compact-driver/        End-to-end compilation, check, format & fixup orchestration
  compact-test-utils/    Shared insta + indoc snapshot test macros

examples/                Curated showcase contracts used by snapshot & E2E tests
tests/conformance/       Vendored upstream Compact conformance, formatter & fixup corpus
compact-scheme/          (gitignored, read-only) Optional local Chez Scheme reference checkout
```

## Development

```sh
cargo fmt --all -- --check
cargo clippy --workspace --all-targets --locked -- -D warnings
cargo test --workspace --locked
```

Snapshot tests use [`cargo-insta`](https://insta.rs/):

```sh
cargo insta test
cargo insta review
```

See [AGENTS.md](./AGENTS.md) for engineering conventions and testing rules.
