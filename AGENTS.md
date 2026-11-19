# AGENTS.md

Engineering guide for porting the Compact compiler toolchain from Chez Scheme (`compact-scheme/`) to Rust.

## Reference Codebase

- `compact-scheme/` is a local, gitignored checkout of the upstream Compact repository. **Treat it as read-only.**
- The Scheme compiler lives in `compact-scheme/compiler/` (with pipeline overview in `compact-scheme/compiler/passes.ss`, IR definitions in `compact-scheme/compiler/langs.ss`, architecture notes in `compact-scheme/compiler.md`, and unit tests in `compact-scheme/compiler/test.ss`).
- Additional contracts and integration tests live in `compact-scheme/examples/`, `compact-scheme/test-contracts/`, and `compact-scheme/test-center/`.

## Scope

- Port the full compiler toolchain: **`compactc`** (compiler), **`format`** (formatter), and **`fixup`** (code fixer/migrator).
- Bring Midnight ecosystem dependencies (e.g., ZKIR/proving, ledger types) in directly as Rust crates rather than invoking external binaries.

## Development Approach

- **Vertical slices over big upfront design.** Do not over-plan or design the lexer/parser/AST in a vacuum without considering downstream stages. Start with a minimal end-to-end slice through the full pipeline and iterate, letting later stages inform earlier data structures.
- **Keep architecture holistic.** When introducing or revising AST/IR representations, consider how analysis, lowering, formatting, fixup, source maps, and codegen will consume them.

## Architecture & Crates

- **Rust workspace** (`Cargo.toml`, edition 2024, members under `crates/*`).
  - Hoist all external and internal dependencies into `[workspace.dependencies]` in the root `Cargo.toml` and reference them via `workspace = true` in member crates. Keep workspace-level feature sets minimal so individual crates opt into extra features (e.g., `miette`'s `fancy` feature only in crates that render diagnostics).
  - Inherit shared package metadata (`version`, `edition`, etc.) from `[workspace.package]`.
- **Data-oriented design (DOD):**
  - Lean into DOD aggressively where it pays off (flat arrays, typed index handles, SoA storage, minimal pointer chasing), while avoiding forcing it where standard Rust enums/structs are cleaner and simpler.
  - Use **`soa-rs`** for a Zig-inspired AST (Structure-of-Arrays node/token storage, compact indices, side/extra-data tables).
- **Parallelism:**
  - Design stages and data structures so naturally independent work can run in parallel (e.g., loading/parsing modules and includes, independent circuit compilation/optimization, independent artifact emission).
- **CLI (`clap`):**
  - Use `clap` for CLI parsing across `compactc`, `format`, and `fixup`.
  - CLI command handlers must be thin wrappers that call directly into testable library functions.
- **Diagnostics (`miette`):**
  - Use `miette` for rendering compiler errors, warnings, and source spans.
- **Progress / Status Output:**
  - Implement Cargo-style status/progress line printing (e.g., phase/file progress) as a separate concern from `miette` diagnostic rendering.

## Testing Rules

- Use **unit tests** and **snapshot tests** with **`cargo-insta`** (`insta`) + **`indoc`**.
- Provide custom snapshot test macros (combining `indoc` and `insta`) that render the Compact source directly into the snapshot file (e.g., via `insta` settings/info or structured snapshot formatting) rather than capturing the inline Rust test expression.
- **Never invoke the compiled CLI binary in `target/` from tests.** Tests must call the underlying library/handler functions directly—spawning the debug binary to test CLI behavior is forbidden.
