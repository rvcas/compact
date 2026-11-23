pub mod status;

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU32, Ordering};
use std::time::Instant;

use compact_artifacts::{render_contract_info, render_contract_manifest};
use compact_ast::Ast;
use compact_circuit::lower_to_circuits;
use compact_codegen_ts::{TsCodegenError, TsCodegenInput, generate_ts};
use compact_codegen_zkir::{ZkirError, analyze_model, compile_keys_with_model, generate_zkir};
use compact_diagnostics::DiagnosticBag;
use compact_fmt::{FormatOptions, format_ast};
use compact_hir::Program as HirProgram;
use compact_parser::parse;
use compact_sema::{LoadError, ModuleLoader, check_with_loader};
use compact_span::{FileId, SourceFile, SourceMap};
use miette::Diagnostic;
use rayon::prelude::*;
use status::{StatusReporter, TermStatusReporter};
use thiserror::Error;

/// Filesystem-backed module & include loader resolving `.compact` files relative to the importer.
struct FsModuleLoader {
    next_file_id: AtomicU32,
}

impl FsModuleLoader {
    fn new() -> Self {
        Self {
            next_file_id: AtomicU32::new(1),
        }
    }
}

impl ModuleLoader for FsModuleLoader {
    fn load(
        &self,
        from_file: &SourceFile,
        specifier: &str,
    ) -> Result<(SourceFile, Ast), LoadError> {
        let base_dir = from_file
            .path
            .as_deref()
            .and_then(Path::parent)
            .unwrap_or_else(|| Path::new("."));
        let mut candidate = base_dir.join(specifier);
        if candidate.extension().is_none() {
            candidate.set_extension("compact");
        }
        let text = fs::read_to_string(&candidate).map_err(|_| {
            LoadError::NotFound(format!(
                "failed to locate file `{specifier}` (tried `{}`)",
                candidate.display()
            ))
        })?;
        let id = FileId(self.next_file_id.fetch_add(1, Ordering::Relaxed));
        let display = candidate.display().to_string();
        let sf = SourceFile::new(id, display, Some(candidate), text);
        let parsed = parse(&sf);
        if parsed.diagnostics.has_errors() {
            return Err(LoadError::ParseFailed(parsed.diagnostics));
        }
        Ok((sf, parsed.ast))
    }
}

pub const OUTPUT_SUBDIRECTORIES: &[&str] = &["compiler", "contract", "zkir", "keys"];

#[derive(Debug, Error, Diagnostic)]
pub enum DriverError {
    #[error("failed to read `{path}`")]
    ReadFile {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("failed to write `{path}`")]
    WriteFile {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("failed to prepare directory `{path}`")]
    PrepareDir {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("failed to build contract manifest")]
    Manifest(#[source] std::io::Error),
    #[error(transparent)]
    #[diagnostic(transparent)]
    Diagnostics(#[from] DiagnosticBag),
    #[error(transparent)]
    Zkir(#[from] ZkirError),
    #[error(transparent)]
    TsCodegen(#[from] TsCodegenError),
}

#[derive(Debug, Clone)]
pub struct BuildOptions {
    pub source: PathBuf,
    pub target: PathBuf,
    pub skip_zk: bool,
}

#[derive(Debug, Clone)]
pub struct CheckOptions {
    pub source: PathBuf,
}

#[derive(Debug, Clone)]
pub struct FormatFileOptions {
    pub source: PathBuf,
    pub target: Option<PathBuf>,
    pub line_length: usize,
}

#[derive(Debug, Clone)]
pub struct BuildReport {
    pub proof_circuits: Vec<String>,
    pub written_files: Vec<PathBuf>,
}

/// Compile a Compact contract from disk to `options.target`.
pub fn build(options: &BuildOptions) -> Result<BuildReport, DriverError> {
    let reporter = TermStatusReporter::new();
    build_with_reporter(options, &reporter)
}

pub fn build_with_reporter(
    options: &BuildOptions,
    reporter: &dyn StatusReporter,
) -> Result<BuildReport, DriverError> {
    let started = Instant::now();
    let source_display = options.source.display().to_string();

    reporter.status("Compiling", &source_display);

    let text = fs::read_to_string(&options.source).map_err(|source| DriverError::ReadFile {
        path: options.source.clone(),
        source,
    })?;
    let mut sm = SourceMap::new();
    let file_id = sm.add_disk_file(&options.source, text);
    let file = sm.get(file_id);

    // Parse & lower to checked HIR.
    let parsed = parse(file);
    let ast = parsed.diagnostics.into_result(parsed.ast)?;

    reporter.status("Checking", &source_display);
    let loader = FsModuleLoader::new();
    let checked = check_with_loader(file, &ast, &loader);
    let hir = checked.diagnostics.into_result(checked.program)?;

    // Lower proof circuits.
    let circuit_prog = lower_to_circuits(&hir);

    // Generate ZKIR circuits in parallel across all proof circuits.
    let zkir_outputs = circuit_prog
        .circuits
        .par_iter()
        .map(generate_zkir)
        .collect::<Result<Vec<_>, _>>()?;

    // Clean output subdirectories before writing new artifacts.
    for sub in OUTPUT_SUBDIRECTORIES {
        let dir = options.target.join(sub);
        if dir.exists() {
            fs::remove_dir_all(&dir)
                .map_err(|source| DriverError::PrepareDir { path: dir, source })?;
        }
    }

    let mut written_files = Vec::new();

    // Write ZKIR files and optionally compile ZK proving/verifier keys in parallel.
    let mut verifier_key_hashes = BTreeMap::new();
    if !zkir_outputs.is_empty() {
        let zkir_dir = options.target.join("zkir");
        fs::create_dir_all(&zkir_dir).map_err(|source| DriverError::PrepareDir {
            path: zkir_dir.clone(),
            source,
        })?;

        for zkir in &zkir_outputs {
            let zkir_path = zkir_dir.join(format!("{}.zkir", zkir.name));
            write_file(&zkir_path, &zkir.json)?;
            written_files.push(zkir_path);

            let bzkir_path = zkir_dir.join(format!("{}.bzkir", zkir.name));
            write_file(&bzkir_path, &zkir.bzkir)?;
            written_files.push(bzkir_path);
        }

        if !options.skip_zk {
            let compiled_keys = zkir_outputs
                .par_iter()
                .map(|z| {
                    let model = analyze_model(&z.ir);
                    reporter.status(
                        "Keygen",
                        &format!("{} (k={}, {} rows)", z.name, model.k, model.rows),
                    );
                    compile_keys_with_model(&z.ir, model).map(|keys| (z.name.clone(), keys))
                })
                .collect::<Result<Vec<_>, _>>()?;

            let keys_dir = options.target.join("keys");
            fs::create_dir_all(&keys_dir).map_err(|source| DriverError::PrepareDir {
                path: keys_dir.clone(),
                source,
            })?;

            for (name, keys) in compiled_keys {
                let pk_path = keys_dir.join(format!("{name}.prover"));
                write_file(&pk_path, &keys.prover_key)?;
                written_files.push(pk_path);

                let vk_path = keys_dir.join(format!("{name}.verifier"));
                write_file(&vk_path, &keys.verifier_key)?;
                written_files.push(vk_path);

                verifier_key_hashes.insert(name, keys.verifier_key_sha256);
            }
        }
    }

    // Generate contract-info.json and TypeScript/JS/.d.ts/sourcemap in parallel!
    let source_name = options
        .source
        .file_name()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_else(|| source_display.clone());

    let (contract_info_json, ts_result) = rayon::join(
        || render_contract_info(&hir),
        || {
            generate_ts(&TsCodegenInput {
                program: &hir,
                source_name: &source_name,
                source_text: file.text(),
                verifier_key_hashes: &verifier_key_hashes,
            })
        },
    );
    let ts_bundle = ts_result?;

    // Write compiler/contract-info.json
    let compiler_dir = options.target.join("compiler");
    fs::create_dir_all(&compiler_dir).map_err(|source| DriverError::PrepareDir {
        path: compiler_dir.clone(),
        source,
    })?;
    let info_path = compiler_dir.join("contract-info.json");
    write_file(&info_path, contract_info_json)?;
    written_files.push(info_path);

    // Write contract/index.js, contract/index.d.ts, contract/index.js.map
    let contract_dir = options.target.join("contract");
    fs::create_dir_all(&contract_dir).map_err(|source| DriverError::PrepareDir {
        path: contract_dir.clone(),
        source,
    })?;

    let js_path = contract_dir.join("index.js");
    write_file(&js_path, &ts_bundle.js)?;
    written_files.push(js_path);

    let dts_path = contract_dir.join("index.d.ts");
    write_file(&dts_path, &ts_bundle.dts)?;
    written_files.push(dts_path);

    let map_path = contract_dir.join("index.js.map");
    write_file(&map_path, &ts_bundle.source_map)?;
    written_files.push(map_path);

    // Write compiler/contract-manifest.json
    let manifest_json = render_contract_manifest(&options.target, OUTPUT_SUBDIRECTORIES)
        .map_err(DriverError::Manifest)?;
    let manifest_path = compiler_dir.join("contract-manifest.json");
    write_file(&manifest_path, manifest_json)?;
    written_files.push(manifest_path);

    let elapsed = started.elapsed();
    reporter.status(
        "Finished",
        &format!(
            "`{}` -> `{}` in {:.2}s",
            source_display,
            options.target.display(),
            elapsed.as_secs_f64()
        ),
    );

    Ok(BuildReport {
        proof_circuits: zkir_outputs.into_iter().map(|z| z.name).collect(),
        written_files,
    })
}

/// Parse and semantically check a Compact file without writing outputs.
pub fn check(options: &CheckOptions) -> Result<HirProgram, DriverError> {
    let reporter = TermStatusReporter::new();
    check_with_reporter(options, &reporter)
}

pub fn check_with_reporter(
    options: &CheckOptions,
    reporter: &dyn StatusReporter,
) -> Result<HirProgram, DriverError> {
    let started = Instant::now();
    let source_display = options.source.display().to_string();
    reporter.status("Checking", &source_display);

    let text = fs::read_to_string(&options.source).map_err(|source| DriverError::ReadFile {
        path: options.source.clone(),
        source,
    })?;
    let mut sm = SourceMap::new();
    let file_id = sm.add_disk_file(&options.source, text);
    let file = sm.get(file_id);

    let parsed = parse(file);
    let ast = parsed.diagnostics.into_result(parsed.ast)?;
    let loader = FsModuleLoader::new();
    let checked = check_with_loader(file, &ast, &loader);
    let hir = checked.diagnostics.into_result(checked.program)?;

    reporter.status(
        "Finished",
        &format!(
            "`{source_display}` in {:.2}s",
            started.elapsed().as_secs_f64()
        ),
    );
    Ok(hir)
}

/// Format a Compact file and either return or write the formatted output.
pub fn format_file(options: &FormatFileOptions) -> Result<String, DriverError> {
    let text = fs::read_to_string(&options.source).map_err(|source| DriverError::ReadFile {
        path: options.source.clone(),
        source,
    })?;
    let formatted = format_source(&options.source, &text, options.line_length)?;
    if let Some(target) = &options.target {
        write_file(target, &formatted)?;
    }
    Ok(formatted)
}

pub fn format_source(path: &Path, text: &str, line_length: usize) -> Result<String, DriverError> {
    let mut sm = SourceMap::new();
    let file_id = sm.add_disk_file(path, text);
    let file = sm.get(file_id);
    let parsed = parse(file);
    let ast = parsed.diagnostics.into_result(parsed.ast)?;
    Ok(format_ast(
        &ast,
        file.text(),
        &FormatOptions { line_length },
    ))
}

fn write_file(path: &Path, contents: impl AsRef<[u8]>) -> Result<(), DriverError> {
    fs::write(path, contents).map_err(|source| DriverError::WriteFile {
        path: path.to_path_buf(),
        source,
    })
}

#[cfg(test)]
mod tests {
    use std::sync::Mutex;

    use tempfile::tempdir;

    use super::*;

    struct CaptureReporter(Mutex<Vec<(String, String)>>);

    impl StatusReporter for CaptureReporter {
        fn status(&self, verb: &str, detail: &str) {
            self.0
                .lock()
                .unwrap()
                .push((verb.to_owned(), detail.to_owned()));
        }
    }

    #[test]
    fn end_to_end_build_and_check_counter() {
        let src_path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/counter.compact");
        let dir = tempdir().unwrap();
        let out_dir = dir.path().join("out");

        // Check command path
        let check_reporter = CaptureReporter(Mutex::new(Vec::new()));
        let hir = check_with_reporter(
            &CheckOptions {
                source: src_path.clone(),
            },
            &check_reporter,
        )
        .unwrap();
        assert_eq!(hir.ledger_fields.len(), 1);
        assert_eq!(hir.circuits.len(), 1);
        assert!(hir.circuits[0].proof);

        // Build command path (--skip-zk to avoid network trusted-setup download in unit tests)
        let build_reporter = CaptureReporter(Mutex::new(Vec::new()));
        let report = build_with_reporter(
            &BuildOptions {
                source: src_path.clone(),
                target: out_dir.clone(),
                skip_zk: true,
            },
            &build_reporter,
        )
        .unwrap();

        assert_eq!(report.proof_circuits, vec!["increment"]);
        assert!(out_dir.join("zkir/increment.zkir").is_file());
        assert!(out_dir.join("zkir/increment.bzkir").is_file());
        assert!(out_dir.join("contract/index.js").is_file());
        assert!(out_dir.join("contract/index.d.ts").is_file());
        assert!(out_dir.join("contract/index.js.map").is_file());
        assert!(out_dir.join("compiler/contract-info.json").is_file());
        assert!(out_dir.join("compiler/contract-manifest.json").is_file());

        // Verify source map JSON references counter.compact
        let map_json: serde_json::Value = serde_json::from_str(
            &fs::read_to_string(out_dir.join("contract/index.js.map")).unwrap(),
        )
        .unwrap();
        assert_eq!(map_json["version"], 3);
        assert_eq!(map_json["sources"][0], "counter.compact");

        // Verify manifest inventories emitted subdirectories
        let manifest: serde_json::Value = serde_json::from_str(
            &fs::read_to_string(out_dir.join("compiler/contract-manifest.json")).unwrap(),
        )
        .unwrap();
        assert_eq!(manifest["contract"]["index.js"]["type"], "file");
        assert_eq!(manifest["zkir"]["increment.zkir"]["type"], "file");
        assert_eq!(manifest["compiler"]["contract-info.json"]["type"], "file");

        // Verify Cargo-style status lines fired
        let verbs: Vec<_> = build_reporter
            .0
            .lock()
            .unwrap()
            .iter()
            .map(|(v, _)| v.clone())
            .collect();
        assert_eq!(verbs, vec!["Compiling", "Checking", "Finished"]);
    }

    #[test]
    fn end_to_end_build_and_check_tiny() {
        let src_path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/tiny.compact");
        let dir = tempdir().unwrap();
        let out_dir = dir.path().join("out");

        let check_reporter = CaptureReporter(Mutex::new(Vec::new()));
        let hir = check_with_reporter(
            &CheckOptions {
                source: src_path.clone(),
            },
            &check_reporter,
        )
        .unwrap();
        assert_eq!(hir.ledger_fields.len(), 3);
        assert_eq!(hir.witnesses.len(), 1);
        assert!(hir.constructor.is_some());
        assert_eq!(hir.circuits.len(), 5);

        let build_reporter = CaptureReporter(Mutex::new(Vec::new()));
        let report = build_with_reporter(
            &BuildOptions {
                source: src_path.clone(),
                target: out_dir.clone(),
                skip_zk: true,
            },
            &build_reporter,
        )
        .unwrap();

        assert_eq!(report.proof_circuits, vec!["set", "get", "clear"]);
        for name in ["set", "get", "clear"] {
            assert!(out_dir.join(format!("zkir/{name}.zkir")).is_file());
            assert!(out_dir.join(format!("zkir/{name}.bzkir")).is_file());
        }
        assert!(!out_dir.join("zkir/public_key.zkir").exists());
        assert!(!out_dir.join("zkir/in_state.zkir").exists());
        assert!(out_dir.join("contract/index.js").is_file());
        assert!(out_dir.join("contract/index.d.ts").is_file());
        assert!(out_dir.join("contract/index.js.map").is_file());
        assert!(out_dir.join("compiler/contract-info.json").is_file());
        assert!(out_dir.join("compiler/contract-manifest.json").is_file());

        let info: serde_json::Value = serde_json::from_str(
            &fs::read_to_string(out_dir.join("compiler/contract-info.json")).unwrap(),
        )
        .unwrap();
        assert_eq!(info["circuits"].as_array().unwrap().len(), 4);
        assert_eq!(info["witnesses"].as_array().unwrap().len(), 1);
        assert_eq!(info["ledger"].as_array().unwrap().len(), 3);
    }

    #[test]
    fn end_to_end_build_and_check_election() {
        let src_path =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/election.compact");
        let dir = tempdir().unwrap();
        let out_dir = dir.path().join("out");

        let check_reporter = CaptureReporter(Mutex::new(Vec::new()));
        let hir = check_with_reporter(
            &CheckOptions {
                source: src_path.clone(),
            },
            &check_reporter,
        )
        .unwrap();
        assert_eq!(hir.enums.len(), 3);
        assert_eq!(hir.ledger_fields.len(), 9);
        assert_eq!(hir.witnesses.len(), 7);
        assert_eq!(hir.circuits.len(), 11);

        let build_reporter = CaptureReporter(Mutex::new(Vec::new()));
        let report = build_with_reporter(
            &BuildOptions {
                source: src_path.clone(),
                target: out_dir.clone(),
                skip_zk: true,
            },
            &build_reporter,
        )
        .unwrap();

        assert_eq!(
            report.proof_circuits,
            vec![
                "vote$commit",
                "vote$reveal",
                "advance",
                "set_topic",
                "add_voter",
            ]
        );
        for name in [
            "vote$commit",
            "vote$reveal",
            "advance",
            "set_topic",
            "add_voter",
        ] {
            assert!(out_dir.join(format!("zkir/{name}.zkir")).is_file());
            assert!(out_dir.join(format!("zkir/{name}.bzkir")).is_file());
        }
        assert!(!out_dir.join("zkir/ballot_repr.zkir").exists());
        assert!(!out_dir.join("zkir/successor.zkir").exists());
        assert!(!out_dir.join("zkir/public_key.zkir").exists());
        assert!(out_dir.join("contract/index.js").is_file());
        assert!(out_dir.join("contract/index.d.ts").is_file());
        assert!(out_dir.join("contract/index.js.map").is_file());
        assert!(out_dir.join("compiler/contract-info.json").is_file());
        assert!(out_dir.join("compiler/contract-manifest.json").is_file());

        let info: serde_json::Value = serde_json::from_str(
            &fs::read_to_string(out_dir.join("compiler/contract-info.json")).unwrap(),
        )
        .unwrap();
        assert_eq!(info["circuits"].as_array().unwrap().len(), 5);
        assert_eq!(info["witnesses"].as_array().unwrap().len(), 7);
        assert_eq!(info["ledger"].as_array().unwrap().len(), 9);
    }

    #[test]
    fn end_to_end_build_and_check_zerocash() {
        let src_path =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/zerocash.compact");
        let dir = tempdir().unwrap();
        let out_dir = dir.path().join("out");

        let check_reporter = CaptureReporter(Mutex::new(Vec::new()));
        let hir = check_with_reporter(
            &CheckOptions {
                source: src_path.clone(),
            },
            &check_reporter,
        )
        .unwrap();
        assert_eq!(hir.structs.len(), 8);
        assert_eq!(hir.ledger_fields.len(), 3);
        assert_eq!(hir.witnesses.len(), 7);
        assert_eq!(hir.circuits.len(), 5);

        let build_reporter = CaptureReporter(Mutex::new(Vec::new()));
        let report = build_with_reporter(
            &BuildOptions {
                source: src_path.clone(),
                target: out_dir.clone(),
                skip_zk: true,
            },
            &build_reporter,
        )
        .unwrap();

        assert_eq!(report.proof_circuits, vec!["spend", "zerocash_mint"]);
        for name in ["spend", "zerocash_mint"] {
            assert!(out_dir.join(format!("zkir/{name}.zkir")).is_file());
            assert!(out_dir.join(format!("zkir/{name}.bzkir")).is_file());
        }
        assert!(!out_dir.join("zkir/derive_nullifier.zkir").exists());
        assert!(!out_dir.join("zkir/derive_zk_public_key.zkir").exists());
        assert!(!out_dir.join("zkir/commitment_from_coin_info.zkir").exists());
        assert!(out_dir.join("contract/index.js").is_file());
        assert!(out_dir.join("contract/index.d.ts").is_file());
        assert!(out_dir.join("contract/index.js.map").is_file());
        assert!(out_dir.join("compiler/contract-info.json").is_file());
        assert!(out_dir.join("compiler/contract-manifest.json").is_file());

        let info: serde_json::Value = serde_json::from_str(
            &fs::read_to_string(out_dir.join("compiler/contract-info.json")).unwrap(),
        )
        .unwrap();
        assert_eq!(info["circuits"].as_array().unwrap().len(), 2);
        assert_eq!(info["witnesses"].as_array().unwrap().len(), 7);
        assert_eq!(info["ledger"].as_array().unwrap().len(), 3);
    }

    #[test]
    fn end_to_end_build_and_check_adt_showcase() {
        let src_path =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/adt_showcase.compact");
        let dir = tempdir().unwrap();
        let out_dir = dir.path().join("out");

        let check_reporter = CaptureReporter(Mutex::new(Vec::new()));
        let hir = check_with_reporter(
            &CheckOptions {
                source: src_path.clone(),
            },
            &check_reporter,
        )
        .unwrap();
        assert_eq!(hir.ledger_fields.len(), 5);
        assert_eq!(hir.circuits.len(), 6);

        let build_reporter = CaptureReporter(Mutex::new(Vec::new()));
        let report = build_with_reporter(
            &BuildOptions {
                source: src_path.clone(),
                target: out_dir.clone(),
                skip_zk: true,
            },
            &build_reporter,
        )
        .unwrap();

        assert_eq!(
            report.proof_circuits,
            vec![
                "init_nested",
                "enqueue_batch",
                "seed_range",
                "manage_queue",
                "reset_all",
            ]
        );
        for name in [
            "init_nested",
            "enqueue_batch",
            "seed_range",
            "manage_queue",
            "reset_all",
        ] {
            assert!(out_dir.join(format!("zkir/{name}.zkir")).is_file());
            assert!(out_dir.join(format!("zkir/{name}.bzkir")).is_file());
        }
        // `check_bounds` is pure -> no proof circuit generated.
        assert!(!out_dir.join("zkir/check_bounds.zkir").exists());
        assert!(out_dir.join("contract/index.js").is_file());
        assert!(out_dir.join("contract/index.d.ts").is_file());
        assert!(out_dir.join("contract/index.js.map").is_file());
        assert!(out_dir.join("compiler/contract-info.json").is_file());
        assert!(out_dir.join("compiler/contract-manifest.json").is_file());

        let info: serde_json::Value = serde_json::from_str(
            &fs::read_to_string(out_dir.join("compiler/contract-info.json")).unwrap(),
        )
        .unwrap();
        assert_eq!(info["circuits"].as_array().unwrap().len(), 6);
        assert_eq!(info["ledger"].as_array().unwrap().len(), 5);
        assert_eq!(info["ledger"][1]["storage"], "Map");
        assert_eq!(info["ledger"][1]["value"]["type-name"], "Map");
        assert_eq!(info["ledger"][1]["value"]["value"]["type-name"], "Counter");
    }

    #[test]
    fn end_to_end_build_and_check_modular() {
        let src_path =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/modular/main.compact");
        let dir = tempdir().unwrap();
        let out_dir = dir.path().join("out");

        let check_reporter = CaptureReporter(Mutex::new(Vec::new()));
        let hir = check_with_reporter(
            &CheckOptions {
                source: src_path.clone(),
            },
            &check_reporter,
        )
        .unwrap();
        assert_eq!(hir.ledger_fields.len(), 2);
        assert!(hir.new_types.iter().any(|nt| nt.name == "AccountId"));
        assert!(hir.new_types.iter().any(|nt| nt.name == "Tag_4"));

        let build_reporter = CaptureReporter(Mutex::new(Vec::new()));
        let report = build_with_reporter(
            &BuildOptions {
                source: src_path.clone(),
                target: out_dir.clone(),
                skip_zk: true,
            },
            &build_reporter,
        )
        .unwrap();

        assert_eq!(
            report.proof_circuits,
            vec!["V_init_key", "bump_three", "deposit"]
        );
        for name in ["V_init_key", "bump_three", "deposit"] {
            assert!(out_dir.join(format!("zkir/{name}.zkir")).is_file());
            assert!(out_dir.join(format!("zkir/{name}.bzkir")).is_file());
        }
        assert!(out_dir.join("contract/index.js").is_file());
        assert!(out_dir.join("contract/index.d.ts").is_file());
        assert!(out_dir.join("contract/index.js.map").is_file());
        assert!(out_dir.join("compiler/contract-info.json").is_file());
        assert!(out_dir.join("compiler/contract-manifest.json").is_file());

        let info: serde_json::Value = serde_json::from_str(
            &fs::read_to_string(out_dir.join("compiler/contract-info.json")).unwrap(),
        )
        .unwrap();
        assert_eq!(info["circuits"].as_array().unwrap().len(), 3);
        assert_eq!(info["ledger"].as_array().unwrap().len(), 2);
    }

    #[test]
    fn end_to_end_build_and_check_functional_patterns() {
        let src_path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../examples/functional_patterns.compact");
        let dir = tempdir().unwrap();
        let out_dir = dir.path().join("out");

        let check_reporter = CaptureReporter(Mutex::new(Vec::new()));
        let hir = check_with_reporter(
            &CheckOptions {
                source: src_path.clone(),
            },
            &check_reporter,
        )
        .unwrap();
        assert_eq!(hir.ledger_fields.len(), 3);
        assert_eq!(hir.witnesses.len(), 3);
        assert_eq!(hir.circuits.len(), 2);

        let build_reporter = CaptureReporter(Mutex::new(Vec::new()));
        let report = build_with_reporter(
            &BuildOptions {
                source: src_path.clone(),
                target: out_dir.clone(),
                skip_zk: true,
            },
            &build_reporter,
        )
        .unwrap();

        assert_eq!(report.proof_circuits, vec!["transform_and_commit"]);
        assert!(out_dir.join("zkir/transform_and_commit.zkir").is_file());
        assert!(out_dir.join("zkir/transform_and_commit.bzkir").is_file());
        assert!(out_dir.join("contract/index.js").is_file());
        assert!(out_dir.join("contract/index.d.ts").is_file());
        assert!(out_dir.join("contract/index.js.map").is_file());
        assert!(out_dir.join("compiler/contract-info.json").is_file());
        assert!(out_dir.join("compiler/contract-manifest.json").is_file());

        let info: serde_json::Value = serde_json::from_str(
            &fs::read_to_string(out_dir.join("compiler/contract-info.json")).unwrap(),
        )
        .unwrap();
        assert_eq!(info["circuits"].as_array().unwrap().len(), 1);
        assert_eq!(info["witnesses"].as_array().unwrap().len(), 3);
        assert_eq!(info["ledger"].as_array().unwrap().len(), 3);
    }

    #[test]
    fn end_to_end_build_and_check_token_vault() {
        let src_path =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/token_vault.compact");
        let dir = tempdir().unwrap();
        let out_dir = dir.path().join("out");

        let check_reporter = CaptureReporter(Mutex::new(Vec::new()));
        let hir = check_with_reporter(
            &CheckOptions {
                source: src_path.clone(),
            },
            &check_reporter,
        )
        .unwrap();
        // 2 user ledger fields + implicit `kernel: Kernel`
        assert_eq!(hir.ledger_fields.len(), 3);
        assert!(hir.constructor.is_some());

        let build_reporter = CaptureReporter(Mutex::new(Vec::new()));
        let report = build_with_reporter(
            &BuildOptions {
                source: src_path.clone(),
                target: out_dir.clone(),
                skip_zk: true,
            },
            &build_reporter,
        )
        .unwrap();

        assert_eq!(
            report.proof_circuits,
            vec![
                "check_time_window",
                "mint_shielded_reward",
                "manage_unshielded",
                "inspect_caller",
            ]
        );
        for name in &report.proof_circuits {
            assert!(out_dir.join(format!("zkir/{name}.zkir")).is_file());
            assert!(out_dir.join(format!("zkir/{name}.bzkir")).is_file());
        }
        assert!(out_dir.join("contract/index.js").is_file());
        assert!(out_dir.join("contract/index.d.ts").is_file());
        assert!(out_dir.join("contract/index.js.map").is_file());
        assert!(out_dir.join("compiler/contract-info.json").is_file());
        assert!(out_dir.join("compiler/contract-manifest.json").is_file());

        let info: serde_json::Value = serde_json::from_str(
            &fs::read_to_string(out_dir.join("compiler/contract-info.json")).unwrap(),
        )
        .unwrap();
        assert_eq!(info["circuits"].as_array().unwrap().len(), 4);
        // `Kernel` is not a public contract state slot in `contract-info.json`.
        assert_eq!(info["ledger"].as_array().unwrap().len(), 2);
    }
}
