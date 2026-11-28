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

//! Pure-Rust Midnight protocol core (Impact VM, Ledger v9, crypto, and native ZKIR proving).
//!
//! Shared foundation for the native Rust SDK, Node.js `napi-rs` bindings (`midnight-napi`),
//! and browser WASM bindings (`midnight-wasm`).

pub mod crypto;
pub mod error;
pub mod prover;
pub mod vm;

pub use error::MidnightError;

#[cfg(test)]
mod tests {
    use midnight_base_crypto::fab::{Aligned, AlignedValue, Value};
    use midnight_onchain_runtime::ops::{Key, Op, expect_checked};
    use midnight_transient_crypto::curve::{EmbeddedFr, Fr};

    use crate::crypto;
    use crate::prover::{
        ContractProofData, build_contract_proof_preimage, check_preimage, ir_k, serialize_preimage,
    };
    use crate::vm::{query_gather, read_counter_at, state_value_array, state_value_counter};

    #[test]
    fn crypto_primitives_round_trip() {
        // Poseidon transient hash is deterministic.
        let h1 = crypto::transient_hash(&[Fr::from(1u64), Fr::from(2u64)]);
        let h2 = crypto::transient_hash(&[Fr::from(1u64), Fr::from(2u64)]);
        assert_eq!(h1, h2);
        assert_ne!(
            h1,
            crypto::transient_hash(&[Fr::from(2u64), Fr::from(1u64)])
        );

        // Embedded curve arithmetic: 2*G == G + G.
        let g = crypto::ec_mul_generator(EmbeddedFr::from(1u64));
        let g2_mul = crypto::ec_mul_generator(EmbeddedFr::from(2u64));
        let g2_add = crypto::ec_add(g, g).unwrap();
        assert_eq!(g2_mul, g2_add);

        // Schnorr BIP-340 sign + verify.
        let sk = crypto::sample_signing_key().unwrap();
        let vk = crypto::signature_verifying_key(&sk).unwrap();
        let sig = crypto::sign_data(&sk, b"midnight-core").unwrap();
        assert!(crypto::verify_signature(&vk, b"midnight-core", &sig).unwrap());
        assert!(!crypto::verify_signature(&vk, b"tampered", &sig).unwrap());
    }

    #[test]
    fn impact_vm_counter_increment_and_zkir_preimage_check() {
        // 1. Initialize contract state with a single Counter at slot 0 initialized to 0.
        let initial = state_value_array(vec![state_value_counter(0)]);
        assert_eq!(read_counter_at(&initial, 0).unwrap(), 0);

        // 2. Run Impact VM ops mirroring `round.increment(1)` in counter.compact.
        let ops = vec![
            Op::Idx {
                cached: false,
                push_path: true,
                path: vec![Key::Value(expect_checked(0u8))].into(),
            },
            Op::Addi { immediate: 1 },
            Op::Ins { cached: true, n: 1 },
        ];
        let out = query_gather(&initial, [0u8; 32], &ops).unwrap();
        assert_eq!(read_counter_at(&out.state, 0).unwrap(), 1);
        assert!(out.gas.compute_time_ps > 0);

        // Increment a second time to verify state persistence.
        let out2 = query_gather(&out.state, [0u8; 32], &ops).unwrap();
        assert_eq!(read_counter_at(&out2.state, 0).unwrap(), 2);

        // 3. Compile `examples/counter.compact` through our compiler and check the ProofPreimage
        //    against the real compiled `.bzkir` using `midnight-zkir`!
        let src = include_str!("../../../examples/counter.compact");
        let file =
            compact_span::SourceFile::new(compact_span::FileId(0), "counter.compact", None, src);
        let parsed = compact_parser::parse(&file);
        assert!(!parsed.diagnostics.has_errors());
        let checked = compact_sema::check(&file, &parsed.ast);
        assert!(!checked.diagnostics.has_errors());
        let circuits = compact_circuit::lower_to_circuits(&checked.program).circuits;
        let inc = circuits
            .iter()
            .find(|c| c.name == "increment")
            .expect("increment circuit");
        let zkir = compact_codegen_zkir::generate_zkir(inc).unwrap();

        let k = ir_k(&zkir.bzkir).unwrap();
        assert!((1..=14).contains(&k), "unexpected k={k}");

        let empty_val = AlignedValue {
            value: Value(vec![]),
            alignment: <()>::alignment(),
        };
        let preimage = build_contract_proof_preimage(&ContractProofData {
            input: empty_val.clone(),
            output: empty_val,
            private_transcript_outputs: vec![],
            public_transcript_ops: out.verified_ops,
            binding_input: Fr::from(0u64),
            comm_comm_rand: crypto::sample_communication_commitment_randomness(),
            key_location: "increment".into(),
        });
        let preimage_bytes = serialize_preimage(&preimage).unwrap();
        let skips = check_preimage(&preimage_bytes, &zkir.bzkir).unwrap();
        assert!(
            skips.iter().all(Option::is_none),
            "expected no skipped public inputs for counter.increment, got {skips:?}"
        );
    }
}
