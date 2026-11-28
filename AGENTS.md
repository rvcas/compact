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
  - Use `miette` for rendering compiler errors, warnings, and source spans (`#[derive(miette::Diagnostic)]` on structured diagnostic/error types).
  - Keep `miette::Result` strictly at the CLI boundary (`crates/compact`). Library crates must return concrete typed `thiserror` error enums or `DiagnosticBag`.
- **Progress / Status Output:**
  - Implement Cargo-style status/progress line printing (e.g., phase/file progress) as a separate concern from `miette` diagnostic rendering.

## Testing Rules

- Use **unit tests** and **snapshot tests** with **`cargo-insta`** (`insta`) + **`indoc`**.
- Provide custom snapshot test macros (combining `indoc` and `insta`) that render the Compact source directly into the snapshot file (e.g., via `insta` settings/info or structured snapshot formatting) rather than capturing the inline Rust test expression.
- **Never invoke the compiled CLI binary in `target/` from Rust tests.** Rust tests must call the underlying library/handler functions directly—spawning the debug binary to test CLI behavior is forbidden. (JS compiler↔SDK integration tests under `packages/midnight/test/e2e/` are an explicit exception so compiler output and the SDK stay drift-proof.)

## JS/TS SDK & Vite+ (`vp`)

- **Toolchain:** Strictly **Node.js + `pnpm` + `vite-plus` (`vp`)**. **Never use Bun** in this repository. Invoke global `vp` directly.
- **Zero upstream `@midnight-ntwrk/*` npm packages:** Pull Midnight protocol libraries (`midnight-onchain-runtime`, `midnight-zkir`, `midnight-base-crypto`, `midnight-transient-crypto`, etc.) directly as Rust crates in `crates/midnight-core` and expose them via `napi-rs` (`crates/midnight-napi`) for Node.js and `wasm-bindgen` (`crates/midnight-wasm`) for browsers.
- **Auto-generated native bindings:** Never hand-write JS loaders or `.d.ts` files in `packages/native/`. `@napi-rs/cli` (`napi build --platform --esm`) generates `packages/native/index.js`, `index.d.ts`, and `*.node` directly from `crates/midnight-napi/src/lib.rs` (all gitignored).
- **Package layout & subpath exports:** `@rvcas/midnight` (`packages/midnight`) is pure ESM with `"sideEffects": false` and tree-shakable subpath exports:
  - `@rvcas/midnight` — Generic Midnight SDK (zero Compact language coupling).
  - `@rvcas/midnight/compact` — Compact smart contract runtime & codecs.
  - `@rvcas/midnight/node` — Node.js native `napi-rs` engine, embedded multi-core Halo2 prover, and FS artifact providers.
  - `@rvcas/midnight/wasm` — Browser fetch / WASM providers.
  - `@rvcas/midnight/testing` — In-memory contract simulator.
  - `@rvcas/midnight/vite` — Vite plugin shelling out to the `compact` CLI.
- **Formatting & linting (`vp check`):** Use **double quotes** in JS/TS (never set `singleQuote: true` in `vite.config.ts`). `vp check` runs Oxfmt + Oxlint across the workspace; ignore Rust/Cargo/autogenerated files in root `vite.config.ts`.
- **Vite+ Tasks over `package.json` scripts:** Define custom build steps in `run.tasks` inside `vite.config.ts` instead of `"scripts"` in `package.json`. Never wrap built-in `vp` commands (`vp check`, `vp test`, `vp pack`) as redundant scripts or tasks.
- **Running builds & tests:**
  - `vp run -r build` — runs `packages/native#build` (`napi build`) → `packages/midnight#build` (`vp pack`, powered by `tsdown`/Rolldown).
  - `vp run build:cli` — builds the `compact` CLI binary for compiler↔SDK e2e tests.
  - `vp test` — top-level built-in Vitest runner configured via `test.projects` (`unit` and `e2e`) in root `vite.config.ts`. Scope with `vp test --project unit` or `vp test --project e2e`.
  - **Explicit builds, no hidden `globalSetup`:** `vp test` assumes `vp run -r build` (and `vp run build:cli` for `e2e`) has already been run after Rust changes so TypeScript iteration stays fast and never silently tests stale native binaries.
  - `vp check` — format + lint check (`vp check --fix` to auto-format).
