use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use compact_driver::{
    BuildOptions, FixupFileOptions, FixupOptions, FormatFileOptions, build_with_reporter,
    fixup_file, fixup_source, format_file, status::StatusReporter,
};
use rayon::prelude::*;
use tempfile::tempdir;

struct SilentReporter;
impl StatusReporter for SilentReporter {
    fn status(&self, _verb: &str, _detail: &str) {}
}

fn collect_compact_files(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let entries = std::fs::read_dir(dir).unwrap_or_else(|e| {
        panic!(
            "failed to read conformance directory {}: {e}",
            dir.display()
        )
    });
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            out.extend(collect_compact_files(&path));
        } else if path.extension().and_then(|e| e.to_str()) == Some("compact") {
            out.push(path);
        }
    }
    out.sort();
    out
}

fn corpus_root() -> PathBuf {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/conformance");
    assert!(
        root.is_dir(),
        "conformance corpus directory missing: {}",
        root.display()
    );
    root
}

fn read_manifest(dir: &Path, name: &str) -> Vec<PathBuf> {
    let manifest_path = dir.join(name);
    let content = std::fs::read_to_string(&manifest_path)
        .unwrap_or_else(|e| panic!("failed to read manifest {}: {e}", manifest_path.display()));
    let mut out = Vec::new();
    for line in content.lines() {
        let rel = line.trim();
        if rel.is_empty() || rel.starts_with('#') {
            continue;
        }
        let path = dir.join(rel);
        assert!(
            path.is_file(),
            "manifest entry missing on disk: {}",
            path.display()
        );
        out.push(path);
    }
    out
}

fn first_error_line(err: &compact_driver::DriverError) -> String {
    match err {
        compact_driver::DriverError::Diagnostics(bag) => bag
            .diagnostics
            .iter()
            .find(|d| d.is_error())
            .map(|d| d.message.clone())
            .unwrap_or_else(|| err.to_string()),
        other => other.to_string(),
    }
}

#[test]
fn conformance_positive_corpus() {
    let root = corpus_root();
    let mut targets: Vec<PathBuf> = Vec::new();

    // 1. Real-world test contracts
    targets.extend(collect_compact_files(
        &root.join("test-center/test-contracts"),
    ));
    // 2. Composable cross-contract & event suites
    targets.extend(collect_compact_files(&root.join("test-center/composable")));
    // 3. ADT tests & exports
    targets.extend(collect_compact_files(&root.join("examples/adt/tests")));
    targets.extend(collect_compact_files(&root.join("examples/adt/exports")));
    // 4. Core standalone & crypto & cast & comma & stdlib & type examples
    for rel in [
        "examples/counter.compact",
        "examples/election.compact",
        "examples/tiny.compact",
        "examples/zerocash.compact",
        "examples/ecdsa/example_one.compact",
        "examples/jubjubpoint/examples.compact",
        "examples/secp256k1/arithmetic.compact",
        "examples/std_lib/block_time.compact",
        "examples/casts/advanced_casts.compact",
        "examples/casts/vector_to_bytes.compact",
        "examples/casts/zkir_generation.compact",
        "examples/commas/commas.compact",
        "examples/commas/more_commas.compact",
        "examples/commas/test.compact",
        "examples/types/examples.compact",
        "test-center/compact/test.compact",
    ] {
        let p = root.join(rel);
        assert!(
            p.is_file(),
            "expected conformance contract: {}",
            p.display()
        );
        targets.push(p);
    }

    assert_eq!(
        targets.len(),
        75,
        "unexpected positive corpus contract count"
    );

    let results: Vec<_> = targets
        .par_iter()
        .map(|path| {
            let rel = path
                .strip_prefix(&root)
                .unwrap_or(path)
                .display()
                .to_string();
            let dir = tempdir().unwrap();
            let out_dir = dir.path().join("out");
            let build_res = build_with_reporter(
                &BuildOptions {
                    source: path.clone(),
                    target: out_dir,
                    skip_zk: true,
                },
                &SilentReporter,
            )
            .map(|r| r.proof_circuits.len())
            .map_err(|e| first_error_line(&e));

            let fmt_res = format_file(&FormatFileOptions {
                source: path.clone(),
                target: None,
                line_length: 80,
            })
            .map(|_| ())
            .map_err(|e| first_error_line(&e));

            (rel, build_res, fmt_res)
        })
        .collect();

    let total = results.len();
    let passed = results.iter().filter(|(_, b, _)| b.is_ok()).count();
    let fmt_passed = results.iter().filter(|(_, _, f)| f.is_ok()).count();

    for (rel, build_res, fmt_res) in &results {
        if let Err(err) = build_res {
            eprintln!("BUILD FAIL: {rel} -> {err}");
        }
        if let Err(err) = fmt_res {
            eprintln!("FMT FAIL: {rel} -> {err}");
        }
    }
    assert_eq!(
        passed, total,
        "expected all {total} conformance positive corpus contracts to build"
    );
    assert_eq!(
        fmt_passed, total,
        "expected all {total} conformance positive corpus contracts to format"
    );
}

#[test]
fn conformance_test_contracts() {
    let tc_root = corpus_root().join("test-contracts");
    let pos = read_manifest(&tc_root, "pass.txt");
    let neg = read_manifest(&tc_root, "fail.txt");
    assert_eq!(pos.len(), 188, "unexpected pass test-contracts count");
    assert_eq!(neg.len(), 191, "unexpected fail test-contracts count");

    let pos_res: Vec<(String, Result<usize, String>)> = pos
        .par_iter()
        .map(|path| {
            let rel = path
                .strip_prefix(&tc_root)
                .unwrap_or(path)
                .display()
                .to_string();
            let dir = tempdir().unwrap();
            let res = build_with_reporter(
                &BuildOptions {
                    source: path.clone(),
                    target: dir.path().join("out"),
                    skip_zk: true,
                },
                &SilentReporter,
            )
            .map(|r| r.proof_circuits.len())
            .map_err(|e| first_error_line(&e));
            (rel, res)
        })
        .collect();

    let neg_res: Vec<(String, bool)> = neg
        .par_iter()
        .map(|path| {
            let rel = path
                .strip_prefix(&tc_root)
                .unwrap_or(path)
                .display()
                .to_string();
            let dir = tempdir().unwrap();
            let ok = build_with_reporter(
                &BuildOptions {
                    source: path.clone(),
                    target: dir.path().join("out"),
                    skip_zk: true,
                },
                &SilentReporter,
            )
            .is_err();
            (rel, ok)
        })
        .collect();

    let pos_ok = pos_res.iter().filter(|(_, r)| r.is_ok()).count();
    let neg_ok = neg_res.iter().filter(|(_, ok)| *ok).count();

    let mut by_err: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (rel, res) in &pos_res {
        if let Err(err) = res {
            by_err.entry(err.clone()).or_default().push(rel.clone());
        }
    }
    for (err, files) in &by_err {
        eprintln!("PASS FAIL [{}x]: {err} (e.g. {})", files.len(), files[0]);
    }
    for (rel, ok) in &neg_res {
        if !*ok {
            eprintln!("NEGATIVE MISSED (should fail): {rel}");
        }
    }

    assert_eq!(
        pos_ok,
        pos_res.len(),
        "expected all compile.pass test-contracts to succeed"
    );
    assert_eq!(
        neg_ok,
        neg_res.len(),
        "expected all compile.fail test-contracts to fail"
    );
}

#[test]
fn conformance_formatter_corpus_idempotent() {
    let inputs = collect_compact_files(&corpus_root().join("examples/formatter/input"));
    assert_eq!(inputs.len(), 14, "unexpected formatter corpus input count");
    for path in &inputs {
        let first = format_file(&FormatFileOptions {
            source: path.clone(),
            target: None,
            line_length: 80,
        })
        .unwrap_or_else(|e| panic!("failed to format {}: {e}", path.display()));
        let second = compact_driver::format_source(path, &first, 80).unwrap_or_else(|e| {
            panic!(
                "formatted output failed to re-parse {}: {e}",
                path.display()
            )
        });
        assert_eq!(
            first,
            second,
            "formatter not idempotent on {}",
            path.display()
        );
    }
}

#[test]
fn conformance_real_world_contracts_halo2_analyze_model() {
    let root = corpus_root();
    let contracts = [
        "test-center/test-contracts/bboard.compact",
        "test-center/test-contracts/counter.compact",
        "test-center/test-contracts/coracle.compact",
        "test-center/test-contracts/micro-dao.compact",
        "test-center/test-contracts/welcome.compact",
    ];
    for rel in contracts {
        let path = root.join(rel);
        let hir = compact_driver::check_with_reporter(
            &compact_driver::CheckOptions { source: path },
            &SilentReporter,
        )
        .unwrap_or_else(|e| panic!("check failed for {rel}: {e}"));
        let circuit_prog = compact_circuit::lower_to_circuits(&hir);
        assert!(
            !circuit_prog.circuits.is_empty(),
            "expected proof circuits for {rel}"
        );
        for c in &circuit_prog.circuits {
            let zkir = compact_codegen_zkir::generate_zkir(c)
                .unwrap_or_else(|e| panic!("ZKIR gen failed for {rel}::{}: {e}", c.name));
            let model = compact_codegen_zkir::analyze_model(&zkir.ir);
            assert!(
                model.rows > 0 && model.k >= 4,
                "invalid Halo2 model for {rel}::{}: k={}, rows={}",
                c.name,
                model.k,
                model.rows
            );
        }
    }
}

#[test]
fn conformance_fixup_corpus() {
    let root = corpus_root().join("fixup");
    let cases: &[(&str, bool)] = &[
        ("camelCase/old/coracle.compact", true),
        ("camelCase/old/counter.compact", false),
        ("camelCase/old/ledger.compact", true),
        ("camelCase/old/standard.compact", true),
        ("fixup/bugs/structured/main.compact", false),
    ];

    for &(rel, expect_edits) in cases {
        let path = root.join(rel);
        assert!(path.is_file(), "missing fixup case: {}", path.display());

        let first = fixup_file(&FixupFileOptions {
            source: path.clone(),
            target: None,
            line_length: 100,
            update_uint_ranges: false,
            compact_path: Vec::new(),
        })
        .unwrap_or_else(|e| panic!("fixup failed for {rel}: {e:?}"));

        if expect_edits {
            assert!(
                first.edits_applied > 0,
                "expected migration edits for {rel}, got 0"
            );
        }

        // Fixup must be idempotent: running again produces zero edits and identical output.
        let second = fixup_source(&path, &first.formatted, &FixupOptions::default(), &[])
            .unwrap_or_else(|e| panic!("second fixup pass failed for {rel}: {e:?}"));
        assert_eq!(
            second.edits_applied, 0,
            "second fixup pass unexpectedly applied {} edits on {rel}",
            second.edits_applied
        );
        assert_eq!(
            first.formatted, second.formatted,
            "fixup not idempotent on {rel}"
        );

        // Fixed output must contain zero deprecated names when checked in normal compiler mode.
        if rel.starts_with("fixup/bugs/structured/") {
            continue;
        }
        let dir = tempdir().unwrap();
        let fixed_path = dir.path().join("fixed.compact");
        std::fs::write(&fixed_path, &first.formatted).unwrap();
        let check_res = compact_driver::check_with_reporter(
            &compact_driver::CheckOptions { source: fixed_path },
            &SilentReporter,
        );
        if rel == "camelCase/old/coracle.compact" {
            // `coracle.compact` is an older pre-WPP contract (lacks `disclose(...)` annotations),
            // so assert no deprecated-name errors remain even when WPP diagnostics fire.
            if let Err(compact_driver::DriverError::Diagnostics(bag)) = check_res {
                assert!(
                    bag.diagnostics
                        .iter()
                        .all(|d| !d.message.contains("old standard-library")),
                    "deprecated names remained after fixup of {rel}: {bag:?}"
                );
            }
        } else {
            check_res
                .unwrap_or_else(|e| panic!("fixed output failed normal check for {rel}: {e:?}"));
        }
    }
}
