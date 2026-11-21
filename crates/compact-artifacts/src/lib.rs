use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use compact_hir::{LedgerAdt, LedgerField, Program, Type};
use serde::Serialize;
use serde_json::{Map, Value};
use sha2::{Digest, Sha256};

pub const COMPILER_VERSION: &str = "0.36.108-dev";
pub const COMPILER_COMMIT: &str = "";
pub const LANGUAGE_VERSION: &str = "0.28.0";
pub const RUNTIME_VERSION: &str = "0.15.0";
pub const MANIFEST_VERSION: &str = "1";

#[derive(Debug, Serialize)]
struct ContractInfo<'a> {
    #[serde(rename = "compiler-version")]
    compiler_version: &'a str,
    #[serde(rename = "compiler-commit")]
    compiler_commit: &'a str,
    #[serde(rename = "language-version")]
    language_version: &'a str,
    #[serde(rename = "runtime-version")]
    runtime_version: &'a str,
    circuits: Vec<CircuitInfo>,
    witnesses: Vec<WitnessInfo>,
    contracts: Vec<Value>,
    ledger: Vec<Value>,
}

#[derive(Debug, Serialize)]
struct CircuitInfo {
    name: String,
    pure: bool,
    proof: bool,
    arguments: Vec<ArgInfo>,
    #[serde(rename = "result-type")]
    result_type: Value,
}

#[derive(Debug, Serialize)]
struct WitnessInfo {
    name: String,
    arguments: Vec<ArgInfo>,
    #[serde(rename = "result type")]
    result_type: Value,
}

#[derive(Debug, Serialize)]
struct ArgInfo {
    name: String,
    #[serde(rename = "type")]
    ty: Value,
}

fn type_to_json(program: &Program, ty: &Type) -> Value {
    let mut map = Map::new();
    match ty {
        Type::Field => {
            map.insert("type-name".into(), Value::String("Field".into()));
        }
        Type::Boolean => {
            map.insert("type-name".into(), Value::String("Boolean".into()));
        }
        Type::Uint(bits) => {
            map.insert("type-name".into(), Value::String("Uint".into()));
            map.insert("maxval".into(), Value::String(((1u128 << bits) - 1).to_string()));
        }
        Type::Bytes(len) => {
            map.insert("type-name".into(), Value::String("Bytes".into()));
            map.insert("length".into(), Value::Number((*len as u64).into()));
        }
        Type::Vector(len, elem) => {
            map.insert("type-name".into(), Value::String("Vector".into()));
            map.insert("length".into(), Value::Number((*len as u64).into()));
            map.insert("type".into(), type_to_json(program, elem));
        }
        Type::Tuple(elems) => {
            map.insert("type-name".into(), Value::String("Tuple".into()));
            map.insert(
                "types".into(),
                Value::Array(elems.iter().map(|e| type_to_json(program, e)).collect()),
            );
        }
        Type::Enum(id) => {
            let decl = program.enum_decl(*id);
            map.insert("type-name".into(), Value::String("Enum".into()));
            map.insert("name".into(), Value::String(decl.name.clone()));
            map.insert(
                "elements".into(),
                Value::Array(decl.variants.iter().cloned().map(Value::String).collect()),
            );
        }
        Type::Maybe(inner) => {
            let mut is_some = Map::new();
            is_some.insert("name".into(), Value::String("is_some".into()));
            is_some.insert("type".into(), type_to_json(program, &Type::Boolean));

            let mut value = Map::new();
            value.insert("name".into(), Value::String("value".into()));
            value.insert("type".into(), type_to_json(program, inner));

            map.insert("type-name".into(), Value::String("Struct".into()));
            map.insert("name".into(), Value::String("Maybe".into()));
            map.insert(
                "elements".into(),
                Value::Array(vec![Value::Object(is_some), Value::Object(value)]),
            );
        }
    }
    Value::Object(map)
}

fn ledger_field_to_json(program: &Program, field: &LedgerField) -> Value {
    let mut map = Map::new();
    map.insert("name".into(), Value::String(field.name.clone()));
    let index = if field.path.len() == 1 {
        Value::Number((field.path[0] as u64).into())
    } else {
        Value::Array(
            field
                .path
                .iter()
                .map(|&p| Value::Number((p as u64).into()))
                .collect(),
        )
    };
    map.insert("index".into(), index);
    map.insert("exported".into(), Value::Bool(field.exported));
    match field.adt {
        LedgerAdt::Counter => {
            map.insert("storage".into(), Value::String("Counter".into()));
        }
        LedgerAdt::Cell => {
            map.insert("storage".into(), Value::String("Cell".into()));
            map.insert("type".into(), type_to_json(program, &field.value_type));
        }
    }
    Value::Object(map)
}

/// Serialize `compiler/contract-info.json` from a checked HIR program.
pub fn render_contract_info(program: &Program) -> String {
    let circuits = program
        .circuits
        .iter()
        .filter(|c| c.exported)
        .map(|c| CircuitInfo {
            name: c.name.clone(),
            pure: c.pure,
            proof: c.proof,
            arguments: c
                .params
                .iter()
                .map(|p| ArgInfo {
                    name: p.name.clone(),
                    ty: type_to_json(program, &p.ty),
                })
                .collect(),
            result_type: type_to_json(program, &c.ret_type),
        })
        .collect();

    let witnesses = program
        .witnesses
        .iter()
        .map(|w| WitnessInfo {
            name: w.name.clone(),
            arguments: w
                .params
                .iter()
                .map(|p| ArgInfo {
                    name: p.name.clone(),
                    ty: type_to_json(program, &p.ty),
                })
                .collect(),
            result_type: type_to_json(program, &w.ret_type),
        })
        .collect();

    let ledger = program
        .ledger_fields
        .iter()
        .map(|f| ledger_field_to_json(program, f))
        .collect();

    let info = ContractInfo {
        compiler_version: COMPILER_VERSION,
        compiler_commit: COMPILER_COMMIT,
        language_version: LANGUAGE_VERSION,
        runtime_version: RUNTIME_VERSION,
        circuits,
        witnesses,
        contracts: Vec::new(),
        ledger,
    };

    let mut json = serde_json::to_string_pretty(&info).unwrap();
    json.push('\n');
    json
}

/// Generate `compiler/contract-manifest.json` inventorying the output directories
/// with file sizes and SHA-256 hashes (matching upstream `save-manifest.ss`).
pub fn render_contract_manifest(output_dir: &Path, subdirs: &[&str]) -> std::io::Result<String> {
    let mut root = Map::new();
    root.insert("manifest-version".into(), Value::String(MANIFEST_VERSION.into()));
    root.insert("compiler-version".into(), Value::String(COMPILER_VERSION.into()));
    root.insert("compiler-commit".into(), Value::String(COMPILER_COMMIT.into()));
    root.insert("language-version".into(), Value::String(LANGUAGE_VERSION.into()));
    root.insert("runtime-version".into(), Value::String(RUNTIME_VERSION.into()));

    for &subdir in subdirs {
        let dir_path = output_dir.join(subdir);
        if dir_path.is_dir() {
            root.insert(subdir.into(), dir_entry(&dir_path)?);
        }
    }

    let mut json = serde_json::to_string_pretty(&Value::Object(root)).unwrap();
    json.push('\n');
    Ok(json)
}

fn dir_entry(dir: &Path) -> std::io::Result<Value> {
    let mut files = BTreeMap::new();
    let mut dirs = BTreeMap::new();

    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let name = entry.file_name().to_string_lossy().into_owned();
        if name == "contract-manifest.json" {
            continue;
        }
        let path = entry.path();
        if path.is_dir() {
            dirs.insert(name, dir_entry(&path)?);
        } else {
            let bytes = fs::read(&path)?;
            let mut file_obj = Map::new();
            file_obj.insert("type".into(), Value::String("file".into()));
            file_obj.insert("size".into(), Value::Number((bytes.len() as u64).into()));
            file_obj.insert("hash".into(), Value::String(hex::encode(Sha256::digest(&bytes))));
            files.insert(name, Value::Object(file_obj));
        }
    }

    let mut map = Map::new();
    map.insert("type".into(), Value::String("directory".into()));
    for (k, v) in files {
        map.insert(k, v);
    }
    for (k, v) in dirs {
        map.insert(k, v);
    }
    Ok(Value::Object(map))
}

#[cfg(test)]
mod tests {
    use compact_parser::parse;
    use compact_sema::check;
    use compact_span::SourceMap;
    use compact_test_utils::assert_compact_snapshot;

    use super::render_contract_info;

    fn contract_info_for(src: &str) -> String {
        let mut sm = SourceMap::new();
        let id = sm.add_file("counter.compact", src);
        let file = sm.get(id);
        let parsed = parse(file);
        assert!(!parsed.diagnostics.has_errors());
        let checked = check(file, &parsed.ast);
        assert!(!checked.diagnostics.has_errors());
        render_contract_info(&checked.program)
    }

    #[test]
    fn contract_info_counter() {
        assert_compact_snapshot!(
            r#"
            import CompactStandardLibrary;

            export ledger round: Counter;

            export circuit increment(): [] {
              round.increment(1);
            }
            "#,
            contract_info_for
        );
    }

    #[test]
    fn contract_info_tiny() {
        assert_compact_snapshot!(
            r#"
            export {Maybe}
            export {set, get, clear, public_key}

            import CompactStandardLibrary;

            enum STATE { unset, set }

            ledger authority: Bytes<32>;
            export ledger value: Field;
            ledger state: STATE;

            constructor(v: Field) {
              const sk = private$secret_key();
              authority = public_key(sk);
              value = disclose(v);
              state = STATE.set;
            }

            witness private$secret_key(): Bytes<32>;

            circuit in_state(s: STATE): Boolean {
              return state == s;
            }

            circuit set(v: Field): [] {
              assert(in_state(STATE.unset), "set: attempted to overwrite recorded value");
              const sk = private$secret_key();
              const apk = public_key(sk);
              authority = apk;
              value = disclose(v);
              state = STATE.set;
            }

            circuit get(): Maybe<Field> {
              return in_state(STATE.set) ? some<Field>(value) : none<Field>();
            }

            circuit clear(): [] {
              assert(in_state(STATE.set), "clear: no value is currently recorded");
              const sk = private$secret_key();
              const apk = public_key(sk);
              assert(apk == authority, "clear: attempted clear without proper authorization");
              authority = default<Bytes<32>>;
              value = default<Field>;
              state = STATE.unset;
            }

            circuit public_key(sk: Bytes<32>): Bytes<32> {
              return disclose(persistentHash<Vector<2, Bytes<32>>>([pad(32, "lares:tiny:pk:"), sk]));
            }
            "#,
            contract_info_for
        );
    }
}
