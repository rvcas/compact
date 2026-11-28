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

//! Native in-process Halo2 ZKIR prover, verifier, and zero-copy KZG SRS cache.
//!
//! Eliminates the need for an external Docker proof server: Node.js (`midnight-napi`) and
//! native Rust apps prove directly in-process at full multi-core Rayon + SIMD speed.

use std::borrow::Cow;
use std::collections::HashMap;
use std::future::Future;
use std::io;
use std::pin::pin;
use std::sync::{Arc, RwLock};
use std::task::{Context, Poll, Waker};

use midnight_base_crypto::data_provider::{FetchMode, MidnightDataProvider, OutputMode};
use midnight_base_crypto::fab::AlignedValue;
use midnight_onchain_runtime::ops::Op;
use midnight_serialize::{tagged_deserialize, tagged_serialize};
use midnight_transient_crypto::curve::Fr;
use midnight_transient_crypto::fab::{AlignedValueExt, ValueReprAlignedValue};
use midnight_transient_crypto::proofs::{
    KeyLocation, PARAMS_VERIFIER, ParamsProver, ParamsProverProvider, Proof, ProofPreimage,
    ProverKey, ProvingKeyMaterial, VerifierKey, Zkir,
};
use midnight_transient_crypto::repr::FieldRepr;
use midnight_zkir::IrSource;
use rand::rngs::OsRng;

use crate::MidnightError;
use crate::crypto::communication_commitment;
use crate::vm::VerifyOp;

/// Result of proving a [`ProofPreimage`] against a circuit's ZKIR + prover key.
#[derive(Debug, Clone)]
pub struct ProveOutput {
    /// Tagged-serialized [`Proof`] bytes.
    pub proof_bytes: Vec<u8>,
    /// Public statement field elements (`pis`) bound into the proof.
    pub public_inputs: Vec<Fr>,
    /// Public-input skip mask computed by ZKIR preprocessing.
    pub pi_skips: Vec<Option<usize>>,
}

/// Inputs for building a canonical contract-call [`ProofPreimage`].
#[derive(Debug, Clone)]
pub struct ContractProofData {
    pub input: AlignedValue,
    pub output: AlignedValue,
    pub private_transcript_outputs: Vec<AlignedValue>,
    pub public_transcript_ops: Vec<VerifyOp>,
    pub binding_input: Fr,
    pub comm_comm_rand: Fr,
    pub key_location: String,
}

/// Build the canonical Midnight [`ProofPreimage`] for a contract circuit call.
///
/// Mirrors `midnight-ledger-v9`'s `ContractCallExt::construct_proof`.
pub fn build_contract_proof_preimage(data: &ContractProofData) -> ProofPreimage {
    let inputs = ValueReprAlignedValue(data.input.clone()).field_vec();

    let mut private_transcript = Vec::with_capacity(
        data.private_transcript_outputs
            .iter()
            .map(|o| o.value_only_field_size())
            .sum(),
    );
    for out in &data.private_transcript_outputs {
        out.value_only_field_repr(&mut private_transcript);
    }

    let mut public_transcript_inputs = Vec::with_capacity(
        data.public_transcript_ops
            .iter()
            .map(|op| op.field_size())
            .sum(),
    );
    for op in &data.public_transcript_ops {
        op.field_repr(&mut public_transcript_inputs);
    }

    let mut public_transcript_outputs = Vec::new();
    for op in &data.public_transcript_ops {
        if let Op::Popeq { result, .. } = op {
            result.value_only_field_repr(&mut public_transcript_outputs);
        }
    }

    let comm_comm =
        communication_commitment(data.input.clone(), data.output.clone(), data.comm_comm_rand);

    ProofPreimage {
        inputs,
        private_transcript,
        public_transcript_inputs,
        public_transcript_outputs,
        binding_input: data.binding_input,
        communications_commitment: Some((comm_comm, data.comm_comm_rand)),
        key_location: KeyLocation(Cow::Owned(data.key_location.clone())),
    }
}

/// Tagged-serialize a [`ProofPreimage`] to canonical bytes.
pub fn serialize_preimage(preimage: &ProofPreimage) -> Result<Vec<u8>, MidnightError> {
    let mut buf = Vec::new();
    tagged_serialize(preimage, &mut buf)
        .map_err(|e| MidnightError::Serialization(e.to_string()))?;
    Ok(buf)
}

/// Tagged-deserialize a [`ProofPreimage`] from canonical bytes.
pub fn deserialize_preimage(bytes: &[u8]) -> Result<ProofPreimage, MidnightError> {
    tagged_deserialize(&mut &bytes[..]).map_err(|e| MidnightError::Serialization(e.to_string()))
}

/// Return the optimal Halo2 `k` parameter (`2^k` rows) for tagged-serialized `.bzkir` bytes.
pub fn ir_k(ir_bytes: &[u8]) -> Result<u8, MidnightError> {
    let ir: IrSource = tagged_deserialize(&mut &ir_bytes[..])
        .map_err(|e| MidnightError::Serialization(e.to_string()))?;
    Ok(ir.k())
}

/// Convert `.zkir` JSON text into canonical tagged `.bzkir` bytes.
pub fn json_ir_to_binary(json: &str) -> Result<Vec<u8>, MidnightError> {
    let ir =
        IrSource::load(json.as_bytes()).map_err(|e| MidnightError::Serialization(e.to_string()))?;
    let mut buf = Vec::new();
    tagged_serialize(&ir, &mut buf).map_err(|e| MidnightError::Serialization(e.to_string()))?;
    Ok(buf)
}

/// Check witness satisfaction for a serialized [`ProofPreimage`] against `.bzkir` bytes without
/// generating a Halo2 proof. Returns the public-input skip mask.
pub fn check_preimage(
    preimage_bytes: &[u8],
    ir_bytes: &[u8],
) -> Result<Vec<Option<usize>>, MidnightError> {
    let preimage = deserialize_preimage(preimage_bytes)?;
    let ir: IrSource = tagged_deserialize(&mut &ir_bytes[..])
        .map_err(|e| MidnightError::Serialization(e.to_string()))?;
    preimage
        .check(&ir)
        .map_err(|e| MidnightError::Proving(e.to_string()))
}

/// Verify a tagged-serialized [`Proof`] against a tagged-serialized [`VerifierKey`] and statement
/// using Midnight's embedded `PARAMS_VERIFIER` (completely offline).
pub fn verify_proof(
    proof_bytes: &[u8],
    vk_bytes: &[u8],
    public_inputs: &[Fr],
) -> Result<(), MidnightError> {
    let proof: Proof = tagged_deserialize(&mut &proof_bytes[..])
        .map_err(|e| MidnightError::Serialization(e.to_string()))?;
    let vk: VerifierKey = tagged_deserialize(&mut &vk_bytes[..])
        .map_err(|e| MidnightError::Serialization(e.to_string()))?;
    vk.verify(&PARAMS_VERIFIER, &proof, public_inputs.iter().copied())
        .map_err(|e| MidnightError::Verification(e.to_string()))
}

#[derive(Clone)]
struct SingleParamProvider {
    k: u8,
    params: ParamsProver,
}

impl ParamsProverProvider for SingleParamProvider {
    async fn get_params(&self, k: u8) -> io::Result<ParamsProver> {
        if k == self.k {
            Ok(self.params.clone())
        } else {
            Err(io::Error::new(
                io::ErrorKind::NotFound,
                format!("unexpected k={k}, cached provider holds k={}", self.k),
            ))
        }
    }
}

fn poll_ready_now<F: Future>(fut: F) -> Result<F::Output, MidnightError> {
    let waker = Waker::noop();
    let mut cx = Context::from_waker(waker);
    let fut = pin!(fut);
    match fut.poll(&mut cx) {
        Poll::Ready(out) => Ok(out),
        Poll::Pending => Err(MidnightError::Proving(
            "proving future unexpectedly yielded Pending with preloaded SRS".into(),
        )),
    }
}

/// Thread-safe, zero-copy-SRS native in-process Halo2 prover.
///
/// Caches deserialized KZG `ParamsProver` (`Arc<ParamsKZG<Bls12>>`) by `k` and optional circuit
/// `ProvingKeyMaterial` by key location, running Halo2 proving on the caller's thread (sharing
/// Halo2's global Rayon pool with zero Tokio executor blocking).
#[derive(Clone, Default)]
pub struct NativeProver {
    params_cache: Arc<RwLock<HashMap<u8, ParamsProver>>>,
    keys_cache: Arc<RwLock<HashMap<String, ProvingKeyMaterial>>>,
}

impl NativeProver {
    /// Create a new empty native prover.
    pub fn new() -> Self {
        Self::default()
    }

    /// Preload raw KZG SRS bytes for degree `k` into the in-memory cache.
    pub fn insert_params(&self, k: u8, raw_bytes: &[u8]) -> Result<(), MidnightError> {
        let params = ParamsProver::read(raw_bytes)
            .map_err(|e| MidnightError::DataProvider(format!("k={k}: {e}")))?;
        self.params_cache
            .write()
            .expect("params_cache lock not poisoned")
            .insert(k, params);
        Ok(())
    }

    /// Register circuit key material (`.prover`, `.verifier`, `.bzkir`) for `key_location`.
    pub fn register_key(
        &self,
        key_location: impl Into<String>,
        prover_key: Vec<u8>,
        verifier_key: Vec<u8>,
        ir_source: Vec<u8>,
    ) {
        self.keys_cache
            .write()
            .expect("keys_cache lock not poisoned")
            .insert(
                key_location.into(),
                ProvingKeyMaterial {
                    prover_key,
                    verifier_key,
                    ir_source,
                },
            );
    }

    /// Fetch (if not cached) and return the zero-copy `ParamsProver` for degree `k`.
    ///
    /// Uses Midnight's `MidnightDataProvider` (local disk cache + SHA-256 verification) inside a
    /// short-lived `current_thread` Tokio runtime that is dropped immediately after loading.
    pub fn get_or_fetch_params(&self, k: u8) -> Result<ParamsProver, MidnightError> {
        if let Some(cached) = self
            .params_cache
            .read()
            .expect("params_cache lock not poisoned")
            .get(&k)
            .cloned()
        {
            return Ok(cached);
        }

        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()?;
        let params = rt.block_on(async {
            let provider = MidnightDataProvider::new(FetchMode::OnDemand, OutputMode::Log, vec![])
                .map_err(|e| MidnightError::DataProvider(e.to_string()))?;
            provider
                .get_params(k)
                .await
                .map_err(|e| MidnightError::DataProvider(format!("k={k}: {e}")))
        })?;
        drop(rt);

        self.params_cache
            .write()
            .expect("params_cache lock not poisoned")
            .insert(k, params.clone());
        Ok(params)
    }

    /// Prove a serialized [`ProofPreimage`] using explicit `.prover` + `.bzkir` bytes.
    pub fn prove_with_material(
        &self,
        preimage_bytes: &[u8],
        prover_key_bytes: &[u8],
        ir_bytes: &[u8],
        overwrite_binding_input: Option<Fr>,
    ) -> Result<ProveOutput, MidnightError> {
        let mut preimage = deserialize_preimage(preimage_bytes)?;
        if let Some(bi) = overwrite_binding_input {
            preimage.binding_input = bi;
        }

        let ir: IrSource = tagged_deserialize(&mut &ir_bytes[..])
            .map_err(|e| MidnightError::Serialization(e.to_string()))?;
        let pk: ProverKey<IrSource> =
            IrSource::load_prover_key_from_tagged(std::io::Cursor::new(prover_key_bytes))
                .map_err(|e| MidnightError::Serialization(e.to_string()))?;

        let k = pk
            .init()
            .map_err(|e| MidnightError::Proving(e.to_string()))?
            .k();
        let params = self.get_or_fetch_params(k)?;
        let provider = SingleParamProvider { k, params };

        let (proof, public_inputs, pi_skips) =
            poll_ready_now(ir.prove(OsRng, &provider, pk, &preimage))?
                .map_err(|e| MidnightError::Proving(e.to_string()))?;

        let mut proof_bytes = Vec::new();
        tagged_serialize(&proof, &mut proof_bytes)
            .map_err(|e| MidnightError::Serialization(e.to_string()))?;

        Ok(ProveOutput {
            proof_bytes,
            public_inputs,
            pi_skips,
        })
    }

    /// Prove a serialized [`ProofPreimage`] by resolving its `key_location` from registered keys.
    pub fn prove_registered(
        &self,
        preimage_bytes: &[u8],
        key_location: &str,
        overwrite_binding_input: Option<Fr>,
    ) -> Result<ProveOutput, MidnightError> {
        let material = self
            .keys_cache
            .read()
            .expect("keys_cache lock not poisoned")
            .get(key_location)
            .cloned()
            .ok_or_else(|| {
                MidnightError::DataProvider(format!(
                    "no proving key material registered for '{key_location}'"
                ))
            })?;
        self.prove_with_material(
            preimage_bytes,
            &material.prover_key,
            &material.ir_source,
            overwrite_binding_input,
        )
    }

    /// Compile proving and verifier keys directly from `.bzkir` bytes using the cached SRS.
    pub fn compile_keys(&self, ir_bytes: &[u8]) -> Result<(Vec<u8>, Vec<u8>, u8), MidnightError> {
        let ir: IrSource = tagged_deserialize(&mut &ir_bytes[..])
            .map_err(|e| MidnightError::Serialization(e.to_string()))?;
        let k = ir.k();
        let params = self.get_or_fetch_params(k)?;
        let provider = SingleParamProvider { k, params };
        let (pk, vk) = poll_ready_now(ir.keygen(&provider))?
            .map_err(|e| MidnightError::Proving(e.to_string()))?;

        let mut pk_bytes = Vec::new();
        tagged_serialize(&pk, &mut pk_bytes)
            .map_err(|e| MidnightError::Serialization(e.to_string()))?;
        let mut vk_bytes = Vec::new();
        tagged_serialize(&vk, &mut vk_bytes)
            .map_err(|e| MidnightError::Serialization(e.to_string()))?;
        Ok((pk_bytes, vk_bytes, k))
    }
}
