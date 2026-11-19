# Compact (Rust)

A Rust port of the [Compact](https://midnight.network) smart contract compiler toolchain (`compactc`, `format`, and `fixup`), ported from the Chez Scheme Nanopass reference implementation.

## Goals & Design Principles

- **Holistic end-to-end architecture**: Build minimal vertical slices through the entire pipeline first so AST, IR, analysis, and codegen evolve together rather than in isolation.
- **Data-oriented design**: Use flat, cache-friendly representations where they fit—including a Zig-inspired Structure-of-Arrays (SoA) AST powered by `soa-rs`—without forcing DOD where ordinary Rust types are clearer.
- **Native Rust Midnight dependencies**: Link Midnight ecosystem dependencies (such as ZKIR/ledger crates) directly as Rust crates instead of shelling out to external binaries.
- **Parallel by default where reasonable**: Exploit parallelism across independent compiler work (module loading, circuit lowering/proving, code generation, etc.).
- **First-class UX**:
  - `clap` CLI covering compilation, formatting, and fixups
  - `miette` for structured, source-annotated compiler diagnostics
  - Cargo-style progress/status reporting, kept separate from diagnostics

## Workspace Layout

```text
crates/
  compact/         CLI & compiler entry point
compact-scheme/    (gitignored) Local Chez Scheme reference repo used for porting
```

## Development

```sh
cargo build
cargo test
```

Snapshot tests use [`cargo-insta`](https://insta.rs/):

```sh
cargo insta test
cargo insta review
```

See [AGENTS.md](./AGENTS.md) for engineering conventions and testing rules.
