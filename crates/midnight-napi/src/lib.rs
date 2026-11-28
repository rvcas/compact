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

//! Native Node.js (`napi-rs`) bindings for `midnight-core`.
//!
//! Exposes Midnight's Impact VM, cryptographic primitives, and multi-core native Halo2 ZKIR
//! prover/verifier directly to JavaScript without a Docker proof server.

use midnight_base_crypto::fab::{Aligned, AlignedValue};
use midnight_core::MidnightError;
use midnight_core::crypto;
use midnight_core::prover::{
    self, ContractProofData, NativeProver, ProveOutput, build_contract_proof_preimage,
    serialize_preimage,
};
use midnight_core::vm::{
    self, VerifyOp, deserialize_state_value, empty_state_value, read_counter_at,
    serialize_state_value, state_value_array, state_value_counter,
};
use napi::bindgen_prelude::{AsyncTask, BigInt, Uint8Array};
use napi::{Env, Error, Result, Status, Task};
use napi_derive::napi;

fn to_napi_err(err: MidnightError) -> Error {
    Error::new(Status::GenericFailure, err.to_string())
}

fn to_32_bytes(slice: &[u8], label: &str) -> Result<[u8; 32]> {
    slice.try_into().map_err(|_| {
        Error::new(
            Status::InvalidArg,
            format!("expected 32 bytes for {label}, got {}", slice.len()),
        )
    })
}

/// Affine point on Midnight's embedded JubJub curve, coordinates encoded as 32-byte LE `Fr`.
#[napi(object)]
pub struct EcPointJs {
    pub x: Uint8Array,
    pub y: Uint8Array,
}

/// Gas cost summary from Impact VM execution.
#[napi(object)]
pub struct GasSummaryJs {
    pub read_time_ps: BigInt,
    pub compute_time_ps: BigInt,
    pub bytes_written: BigInt,
    pub bytes_deleted: BigInt,
}

/// Result of executing gather-mode Impact VM ops against a contract state.
#[napi(object)]
pub struct VmQueryResultJs {
    pub state_bytes: Uint8Array,
    pub verified_ops_json: String,
    pub reads_json: String,
    pub gas: GasSummaryJs,
}

/// Input payload for constructing a canonical contract-call `ProofPreimage`.
#[napi(object)]
pub struct BuildPreimageInputJs {
    /// JSON-serialized `AlignedValue` for circuit input (default empty tuple if omitted).
    pub input_json: Option<String>,
    /// JSON-serialized `AlignedValue` for circuit output (default empty tuple if omitted).
    pub output_json: Option<String>,
    /// JSON-serialized `Vec<AlignedValue>` for private transcript outputs (witness results).
    pub private_transcript_outputs_json: Option<String>,
    /// JSON-serialized `Vec<Op<ResultModeVerify>>` (from `VmQueryResultJs.verifiedOpsJson`).
    pub verified_ops_json: String,
    /// Optional 32-byte LE `Fr` binding input (defaults to 0).
    pub binding_input: Option<Uint8Array>,
    /// Optional 32-byte LE `Fr` communication commitment randomness (sampled if omitted).
    pub comm_comm_rand: Option<Uint8Array>,
    /// Circuit key location name (e.g. `"increment"`).
    pub key_location: String,
}

/// Result of native Halo2 proof generation.
#[napi(object)]
pub struct ProveResultJs {
    pub proof_bytes: Uint8Array,
    pub public_inputs: Vec<Uint8Array>,
    pub pi_skips: Vec<Option<u32>>,
}

/// Result of compiling `.prover` and `.verifier` keys from `.bzkir`.
#[napi(object)]
pub struct CompiledKeysJs {
    pub prover_key: Uint8Array,
    pub verifier_key: Uint8Array,
    pub k: u32,
}

fn convert_prove_output(out: ProveOutput) -> ProveResultJs {
    ProveResultJs {
        proof_bytes: Uint8Array::new(out.proof_bytes),
        public_inputs: out
            .public_inputs
            .into_iter()
            .map(|f| Uint8Array::new(crypto::fr_to_le_bytes(f).to_vec()))
            .collect(),
        pi_skips: out
            .pi_skips
            .into_iter()
            .map(|opt| opt.map(|v| v as u32))
            .collect(),
    }
}

// ---------------------------------------------------------------------------
// Crypto primitives
// ---------------------------------------------------------------------------

#[napi]
pub fn transient_hash(elems: Vec<Uint8Array>) -> Result<Uint8Array> {
    let frs = elems
        .iter()
        .map(|b| crypto::fr_from_le_bytes(b.as_ref()).map_err(to_napi_err))
        .collect::<Result<Vec<_>>>()?;
    let h = crypto::transient_hash(&frs);
    Ok(Uint8Array::new(crypto::fr_to_le_bytes(h).to_vec()))
}

#[napi]
pub fn hash_to_field(data: Uint8Array) -> Uint8Array {
    let h = crypto::hash_to_field(data.as_ref());
    Uint8Array::new(crypto::fr_to_le_bytes(h).to_vec())
}

#[napi]
pub fn ec_add(ax: Uint8Array, ay: Uint8Array, bx: Uint8Array, by: Uint8Array) -> Result<EcPointJs> {
    let a = (
        crypto::fr_from_le_bytes(ax.as_ref()).map_err(to_napi_err)?,
        crypto::fr_from_le_bytes(ay.as_ref()).map_err(to_napi_err)?,
    );
    let b = (
        crypto::fr_from_le_bytes(bx.as_ref()).map_err(to_napi_err)?,
        crypto::fr_from_le_bytes(by.as_ref()).map_err(to_napi_err)?,
    );
    let (x, y) = crypto::ec_add(a, b).map_err(to_napi_err)?;
    Ok(EcPointJs {
        x: Uint8Array::new(crypto::fr_to_le_bytes(x).to_vec()),
        y: Uint8Array::new(crypto::fr_to_le_bytes(y).to_vec()),
    })
}

#[napi]
pub fn ec_mul(px: Uint8Array, py: Uint8Array, scalar: Uint8Array) -> Result<EcPointJs> {
    let p = (
        crypto::fr_from_le_bytes(px.as_ref()).map_err(to_napi_err)?,
        crypto::fr_from_le_bytes(py.as_ref()).map_err(to_napi_err)?,
    );
    let s = crypto::embedded_fr_from_le_bytes(scalar.as_ref()).map_err(to_napi_err)?;
    let (x, y) = crypto::ec_mul(p, s).map_err(to_napi_err)?;
    Ok(EcPointJs {
        x: Uint8Array::new(crypto::fr_to_le_bytes(x).to_vec()),
        y: Uint8Array::new(crypto::fr_to_le_bytes(y).to_vec()),
    })
}

#[napi]
pub fn ec_mul_generator(scalar: Uint8Array) -> Result<EcPointJs> {
    let s = crypto::embedded_fr_from_le_bytes(scalar.as_ref()).map_err(to_napi_err)?;
    let (x, y) = crypto::ec_mul_generator(s);
    Ok(EcPointJs {
        x: Uint8Array::new(crypto::fr_to_le_bytes(x).to_vec()),
        y: Uint8Array::new(crypto::fr_to_le_bytes(y).to_vec()),
    })
}

#[napi]
pub fn sample_comm_comm_rand() -> Uint8Array {
    let r = crypto::sample_communication_commitment_randomness();
    Uint8Array::new(crypto::fr_to_le_bytes(r).to_vec())
}

#[napi]
pub fn sample_signing_key() -> Result<Uint8Array> {
    let sk = crypto::sample_signing_key().map_err(to_napi_err)?;
    Ok(Uint8Array::new(sk.to_vec()))
}

#[napi]
pub fn signature_verifying_key(signing_key: Uint8Array) -> Result<Uint8Array> {
    let vk = crypto::signature_verifying_key(signing_key.as_ref()).map_err(to_napi_err)?;
    Ok(Uint8Array::new(vk))
}

#[napi]
pub fn sign_data(signing_key: Uint8Array, message: Uint8Array) -> Result<Uint8Array> {
    let sig = crypto::sign_data(signing_key.as_ref(), message.as_ref()).map_err(to_napi_err)?;
    Ok(Uint8Array::new(sig))
}

#[napi]
pub fn verify_signature(
    verifying_key: Uint8Array,
    message: Uint8Array,
    signature: Uint8Array,
) -> Result<bool> {
    crypto::verify_signature(verifying_key.as_ref(), message.as_ref(), signature.as_ref())
        .map_err(to_napi_err)
}

// ---------------------------------------------------------------------------
// Impact VM & StateValue
// ---------------------------------------------------------------------------

#[napi]
pub fn empty_state_value_bytes() -> Result<Uint8Array> {
    let bytes = serialize_state_value(&empty_state_value()).map_err(to_napi_err)?;
    Ok(Uint8Array::new(bytes))
}

#[napi]
pub fn state_value_counter_bytes(value: BigInt) -> Result<Uint8Array> {
    let (sign_bit, val, lossless) = value.get_u64();
    if sign_bit || !lossless {
        return Err(Error::new(
            Status::InvalidArg,
            "counter value must be an unsigned 64-bit integer",
        ));
    }
    let bytes = serialize_state_value(&state_value_counter(val)).map_err(to_napi_err)?;
    Ok(Uint8Array::new(bytes))
}

#[napi]
pub fn state_value_array_bytes(items: Vec<Uint8Array>) -> Result<Uint8Array> {
    let decoded = items
        .iter()
        .map(|b| deserialize_state_value(b.as_ref()).map_err(to_napi_err))
        .collect::<Result<Vec<_>>>()?;
    let bytes = serialize_state_value(&state_value_array(decoded)).map_err(to_napi_err)?;
    Ok(Uint8Array::new(bytes))
}

#[napi]
pub fn read_counter_at_bytes(state_bytes: Uint8Array, index: u32) -> Result<BigInt> {
    let state = deserialize_state_value(state_bytes.as_ref()).map_err(to_napi_err)?;
    let val = read_counter_at(&state, index as usize).map_err(to_napi_err)?;
    Ok(BigInt::from(val))
}

#[napi]
pub fn query_gather_json(
    state_bytes: Uint8Array,
    address: Uint8Array,
    ops_json: String,
) -> Result<VmQueryResultJs> {
    let addr = to_32_bytes(address.as_ref(), "contract address")?;
    let out = vm::query_gather_json(state_bytes.as_ref(), addr, &ops_json).map_err(to_napi_err)?;
    let reads_json = serde_json::to_string(&out.reads)
        .map_err(|e| Error::new(Status::GenericFailure, e.to_string()))?;
    Ok(VmQueryResultJs {
        state_bytes: Uint8Array::new(out.state_bytes),
        verified_ops_json: out.verified_ops_json,
        reads_json,
        gas: GasSummaryJs {
            read_time_ps: BigInt::from(out.gas.read_time_ps),
            compute_time_ps: BigInt::from(out.gas.compute_time_ps),
            bytes_written: BigInt::from(out.gas.bytes_written),
            bytes_deleted: BigInt::from(out.gas.bytes_deleted),
        },
    })
}

// ---------------------------------------------------------------------------
// ZKIR Prover & Verifier
// ---------------------------------------------------------------------------

#[napi]
pub fn ir_k(ir_bytes: Uint8Array) -> Result<u32> {
    let k = prover::ir_k(ir_bytes.as_ref()).map_err(to_napi_err)?;
    Ok(u32::from(k))
}

#[napi]
pub fn json_ir_to_binary(json: String) -> Result<Uint8Array> {
    let bytes = prover::json_ir_to_binary(&json).map_err(to_napi_err)?;
    Ok(Uint8Array::new(bytes))
}

#[napi]
pub fn build_contract_proof_preimage_bytes(input: BuildPreimageInputJs) -> Result<Uint8Array> {
    let empty_aligned = || AlignedValue {
        value: Default::default(),
        alignment: <()>::alignment(),
    };
    let arg_in: AlignedValue = match input.input_json {
        Some(s) => serde_json::from_str(&s)
            .map_err(|e| Error::new(Status::InvalidArg, format!("invalid inputJson: {e}")))?,
        None => empty_aligned(),
    };
    let arg_out: AlignedValue = match input.output_json {
        Some(s) => serde_json::from_str(&s)
            .map_err(|e| Error::new(Status::InvalidArg, format!("invalid outputJson: {e}")))?,
        None => empty_aligned(),
    };
    let private_outputs: Vec<AlignedValue> = match input.private_transcript_outputs_json {
        Some(s) => serde_json::from_str(&s).map_err(|e| {
            Error::new(
                Status::InvalidArg,
                format!("invalid privateTranscriptOutputsJson: {e}"),
            )
        })?,
        None => Vec::new(),
    };
    let verified_ops: Vec<VerifyOp> = serde_json::from_str(&input.verified_ops_json)
        .map_err(|e| Error::new(Status::InvalidArg, format!("invalid verifiedOpsJson: {e}")))?;
    let binding_input = match input.binding_input {
        Some(b) => crypto::fr_from_le_bytes(b.as_ref()).map_err(to_napi_err)?,
        None => Default::default(),
    };
    let comm_comm_rand = match input.comm_comm_rand {
        Some(b) => crypto::fr_from_le_bytes(b.as_ref()).map_err(to_napi_err)?,
        None => crypto::sample_communication_commitment_randomness(),
    };

    let preimage = build_contract_proof_preimage(&ContractProofData {
        input: arg_in,
        output: arg_out,
        private_transcript_outputs: private_outputs,
        public_transcript_ops: verified_ops,
        binding_input,
        comm_comm_rand,
        key_location: input.key_location,
    });
    let bytes = serialize_preimage(&preimage).map_err(to_napi_err)?;
    Ok(Uint8Array::new(bytes))
}

#[napi]
pub fn check_preimage(
    preimage_bytes: Uint8Array,
    ir_bytes: Uint8Array,
) -> Result<Vec<Option<u32>>> {
    let skips =
        prover::check_preimage(preimage_bytes.as_ref(), ir_bytes.as_ref()).map_err(to_napi_err)?;
    Ok(skips.into_iter().map(|v| v.map(|n| n as u32)).collect())
}

#[napi]
pub fn verify_proof(
    proof_bytes: Uint8Array,
    vk_bytes: Uint8Array,
    public_inputs: Vec<Uint8Array>,
) -> Result<bool> {
    let pis = public_inputs
        .iter()
        .map(|b| crypto::fr_from_le_bytes(b.as_ref()).map_err(to_napi_err))
        .collect::<Result<Vec<_>>>()?;
    match prover::verify_proof(proof_bytes.as_ref(), vk_bytes.as_ref(), &pis) {
        Ok(()) => Ok(true),
        Err(MidnightError::Verification(_)) => Ok(false),
        Err(other) => Err(to_napi_err(other)),
    }
}

pub struct ProveMaterialTask {
    prover: NativeProver,
    preimage_bytes: Vec<u8>,
    prover_key_bytes: Vec<u8>,
    ir_bytes: Vec<u8>,
    overwrite_binding_input: Option<Vec<u8>>,
}

#[napi]
impl Task for ProveMaterialTask {
    type Output = ProveOutput;
    type JsValue = ProveResultJs;

    fn compute(&mut self) -> Result<Self::Output> {
        let bi = self
            .overwrite_binding_input
            .as_deref()
            .map(crypto::fr_from_le_bytes)
            .transpose()
            .map_err(to_napi_err)?;
        self.prover
            .prove_with_material(
                &self.preimage_bytes,
                &self.prover_key_bytes,
                &self.ir_bytes,
                bi,
            )
            .map_err(to_napi_err)
    }

    fn resolve(&mut self, _env: Env, output: Self::Output) -> Result<Self::JsValue> {
        Ok(convert_prove_output(output))
    }
}

pub struct ProveRegisteredTask {
    prover: NativeProver,
    preimage_bytes: Vec<u8>,
    key_location: String,
    overwrite_binding_input: Option<Vec<u8>>,
}

#[napi]
impl Task for ProveRegisteredTask {
    type Output = ProveOutput;
    type JsValue = ProveResultJs;

    fn compute(&mut self) -> Result<Self::Output> {
        let bi = self
            .overwrite_binding_input
            .as_deref()
            .map(crypto::fr_from_le_bytes)
            .transpose()
            .map_err(to_napi_err)?;
        self.prover
            .prove_registered(&self.preimage_bytes, &self.key_location, bi)
            .map_err(to_napi_err)
    }

    fn resolve(&mut self, _env: Env, output: Self::Output) -> Result<Self::JsValue> {
        Ok(convert_prove_output(output))
    }
}

pub struct CompileKeysTask {
    prover: NativeProver,
    ir_bytes: Vec<u8>,
}

#[napi]
impl Task for CompileKeysTask {
    type Output = (Vec<u8>, Vec<u8>, u8);
    type JsValue = CompiledKeysJs;

    fn compute(&mut self) -> Result<Self::Output> {
        self.prover
            .compile_keys(&self.ir_bytes)
            .map_err(to_napi_err)
    }

    fn resolve(&mut self, _env: Env, (pk, vk, k): Self::Output) -> Result<Self::JsValue> {
        Ok(CompiledKeysJs {
            prover_key: Uint8Array::new(pk),
            verifier_key: Uint8Array::new(vk),
            k: u32::from(k),
        })
    }
}

/// Native in-process Halo2 prover handle with zero-copy SRS caching and off-event-loop proving.
#[derive(Default)]
#[napi]
pub struct NativeProverHandle {
    inner: NativeProver,
}

#[napi]
impl NativeProverHandle {
    #[napi(constructor)]
    pub fn new() -> Self {
        Self {
            inner: NativeProver::new(),
        }
    }

    #[napi]
    pub fn insert_params(&self, k: u32, raw_bytes: Uint8Array) -> Result<()> {
        let k_u8 = u8::try_from(k)
            .map_err(|_| Error::new(Status::InvalidArg, format!("k out of range: {k}")))?;
        self.inner
            .insert_params(k_u8, raw_bytes.as_ref())
            .map_err(to_napi_err)
    }

    #[napi]
    pub fn register_key(
        &self,
        key_location: String,
        prover_key: Uint8Array,
        verifier_key: Uint8Array,
        ir_source: Uint8Array,
    ) {
        self.inner.register_key(
            key_location,
            prover_key.to_vec(),
            verifier_key.to_vec(),
            ir_source.to_vec(),
        );
    }

    #[napi(ts_return_type = "Promise<ProveResultJs>")]
    pub fn prove_with_material(
        &self,
        preimage_bytes: Uint8Array,
        prover_key_bytes: Uint8Array,
        ir_bytes: Uint8Array,
        overwrite_binding_input: Option<Uint8Array>,
    ) -> AsyncTask<ProveMaterialTask> {
        AsyncTask::new(ProveMaterialTask {
            prover: self.inner.clone(),
            preimage_bytes: preimage_bytes.to_vec(),
            prover_key_bytes: prover_key_bytes.to_vec(),
            ir_bytes: ir_bytes.to_vec(),
            overwrite_binding_input: overwrite_binding_input.map(|b| b.to_vec()),
        })
    }

    #[napi(ts_return_type = "Promise<ProveResultJs>")]
    pub fn prove_registered(
        &self,
        preimage_bytes: Uint8Array,
        key_location: String,
        overwrite_binding_input: Option<Uint8Array>,
    ) -> AsyncTask<ProveRegisteredTask> {
        AsyncTask::new(ProveRegisteredTask {
            prover: self.inner.clone(),
            preimage_bytes: preimage_bytes.to_vec(),
            key_location,
            overwrite_binding_input: overwrite_binding_input.map(|b| b.to_vec()),
        })
    }

    #[napi(ts_return_type = "Promise<CompiledKeysJs>")]
    pub fn compile_keys(&self, ir_bytes: Uint8Array) -> AsyncTask<CompileKeysTask> {
        AsyncTask::new(CompileKeysTask {
            prover: self.inner.clone(),
            ir_bytes: ir_bytes.to_vec(),
        })
    }
}
