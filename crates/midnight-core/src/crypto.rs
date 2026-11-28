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

//! Protocol-exact Midnight field, hash, commitment, embedded curve, and Schnorr primitives.

use midnight_base_crypto::fab::AlignedValue;
use midnight_base_crypto::hash::{
    HashOutput, persistent_commit as base_persistent_commit,
    persistent_hash as base_persistent_hash,
};
use midnight_base_crypto::schnorr::{Signature, SigningKey, VerifyingKey};
use midnight_serialize::{Deserializable, Serializable};
use midnight_transient_crypto::curve::{EmbeddedFr, EmbeddedGroupAffine, Fr};
use midnight_transient_crypto::fab::ValueReprAlignedValue;
use midnight_transient_crypto::hash::{
    hash_to_curve as tc_hash_to_curve, hash_to_field as tc_hash_to_field,
    transient_commit as tc_transient_commit, transient_hash as tc_transient_hash,
};
use rand::Rng;
use rand::rngs::OsRng;

use crate::MidnightError;

/// Parse a field element `Fr` from little-endian bytes (up to 32 bytes; short slices are zero-padded).
pub fn fr_from_le_bytes(bytes: &[u8]) -> Result<Fr, MidnightError> {
    if bytes.len() > 32 {
        return Err(MidnightError::InvalidField(format!(
            "expected at most 32 bytes, got {}",
            bytes.len()
        )));
    }
    Fr::from_le_bytes(bytes).ok_or_else(|| {
        MidnightError::InvalidField("value exceeds BLS12-381 scalar field modulus".into())
    })
}

/// Encode a field element `Fr` as 32 little-endian bytes.
pub fn fr_to_le_bytes(fr: Fr) -> [u8; 32] {
    let mut out = [0u8; 32];
    let raw = fr.as_le_bytes();
    out[..raw.len()].copy_from_slice(&raw);
    out
}

/// Parse an embedded scalar `EmbeddedFr` from little-endian bytes (up to 32 bytes).
pub fn embedded_fr_from_le_bytes(bytes: &[u8]) -> Result<EmbeddedFr, MidnightError> {
    if bytes.len() > 32 {
        return Err(MidnightError::InvalidField(format!(
            "expected at most 32 bytes for embedded scalar, got {}",
            bytes.len()
        )));
    }
    EmbeddedFr::from_le_bytes(bytes).ok_or_else(|| {
        MidnightError::InvalidField("value exceeds JubJub scalar field modulus".into())
    })
}

/// Poseidon transient hash over field elements.
pub fn transient_hash(elems: &[Fr]) -> Fr {
    tc_transient_hash(elems)
}

/// Poseidon transient commitment to an aligned value with opening scalar `opening`.
pub fn transient_commit(value: &AlignedValue, opening: Fr) -> Fr {
    tc_transient_commit(&ValueReprAlignedValue(value.clone()), opening)
}

/// Persistent SHA-256 hash over raw bytes.
pub fn persistent_hash(data: &[u8]) -> [u8; 32] {
    base_persistent_hash(data).0
}

/// Persistent SHA-256 commitment to raw bytes with 32-byte opening.
pub fn persistent_commit(data: &[u8], opening: [u8; 32]) -> [u8; 32] {
    base_persistent_commit(data, HashOutput(opening)).0
}

/// Hash arbitrary bytes to a single field element (`midnight:field_hash` domain).
pub fn hash_to_field(data: &[u8]) -> Fr {
    tc_hash_to_field(data)
}

/// Compute the canonical communication commitment for a circuit call's `(input, output, rand)`.
pub fn communication_commitment(input: AlignedValue, output: AlignedValue, rand: Fr) -> Fr {
    midnight_onchain_runtime::communication_commitment(input, output, rand)
}

/// Sample cryptographically secure randomness for a communication commitment.
pub fn sample_communication_commitment_randomness() -> Fr {
    OsRng.r#gen()
}

/// Add two affine points `(x, y)` on the embedded JubJub curve.
pub fn ec_add(a: (Fr, Fr), b: (Fr, Fr)) -> Result<(Fr, Fr), MidnightError> {
    let pa = EmbeddedGroupAffine::new(a.0, a.1).ok_or_else(|| {
        MidnightError::InvalidPoint("first point is not on JubJub subgroup".into())
    })?;
    let pb = EmbeddedGroupAffine::new(b.0, b.1).ok_or_else(|| {
        MidnightError::InvalidPoint("second point is not on JubJub subgroup".into())
    })?;
    let sum = pa + pb;
    Ok((sum.x().unwrap_or_default(), sum.y().unwrap_or_default()))
}

/// Multiply an affine point `(x, y)` on the embedded JubJub curve by a scalar.
pub fn ec_mul(point: (Fr, Fr), scalar: EmbeddedFr) -> Result<(Fr, Fr), MidnightError> {
    let p = EmbeddedGroupAffine::new(point.0, point.1)
        .ok_or_else(|| MidnightError::InvalidPoint("point is not on JubJub subgroup".into()))?;
    let prod = p * scalar;
    Ok((prod.x().unwrap_or_default(), prod.y().unwrap_or_default()))
}

/// Multiply the canonical JubJub generator by a scalar.
pub fn ec_mul_generator(scalar: EmbeddedFr) -> (Fr, Fr) {
    let prod = EmbeddedGroupAffine::generator() * scalar;
    (prod.x().unwrap_or_default(), prod.y().unwrap_or_default())
}

/// Hash an aligned value to an affine point `(x, y)` on the embedded JubJub curve.
pub fn hash_to_curve(value: &AlignedValue) -> (Fr, Fr) {
    let p = tc_hash_to_curve(&ValueReprAlignedValue(value.clone()));
    (p.x().unwrap_or_default(), p.y().unwrap_or_default())
}

/// Sample a fresh 32-byte BIP-340 Schnorr signing key.
pub fn sample_signing_key() -> Result<[u8; 32], MidnightError> {
    let sk = SigningKey::sample(OsRng);
    let mut buf = Vec::with_capacity(32);
    sk.serialize(&mut buf)
        .map_err(|e| MidnightError::Serialization(e.to_string()))?;
    buf.try_into()
        .map_err(|_| MidnightError::Serialization("unexpected signing key length".into()))
}

/// Derive the BIP-340 Schnorr verifying key bytes from a 32-byte signing key.
pub fn signature_verifying_key(signing_key_bytes: &[u8]) -> Result<Vec<u8>, MidnightError> {
    let sk = SigningKey::from_bytes(signing_key_bytes)
        .map_err(|e| MidnightError::InvalidKey(e.to_string()))?;
    let vk = sk.verifying_key();
    let mut out = Vec::new();
    vk.serialize(&mut out)
        .map_err(|e| MidnightError::Serialization(e.to_string()))?;
    Ok(out)
}

/// Sign `message` with a 32-byte BIP-340 Schnorr signing key.
pub fn sign_data(signing_key_bytes: &[u8], message: &[u8]) -> Result<Vec<u8>, MidnightError> {
    let sk = SigningKey::from_bytes(signing_key_bytes)
        .map_err(|e| MidnightError::InvalidKey(e.to_string()))?;
    let sig = sk.sign(&mut OsRng, message);
    let mut out = Vec::new();
    sig.serialize(&mut out)
        .map_err(|e| MidnightError::Serialization(e.to_string()))?;
    Ok(out)
}

/// Verify a BIP-340 Schnorr signature against verifying key bytes and message.
pub fn verify_signature(
    verifying_key_bytes: &[u8],
    message: &[u8],
    signature_bytes: &[u8],
) -> Result<bool, MidnightError> {
    let mut vk_slice = verifying_key_bytes;
    let vk = VerifyingKey::deserialize(&mut vk_slice, 0)
        .map_err(|e| MidnightError::InvalidKey(e.to_string()))?;
    let mut sig_slice = signature_bytes;
    let sig = Signature::deserialize(&mut sig_slice, 0)
        .map_err(|e| MidnightError::InvalidKey(e.to_string()))?;
    Ok(vk.verify(message, &sig))
}
