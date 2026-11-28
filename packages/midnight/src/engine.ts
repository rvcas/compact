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

/** Affine point on Midnight's embedded JubJub curve (32-byte little-endian coordinates). */
export interface EcPoint {
  readonly x: Uint8Array;
  readonly y: Uint8Array;
}

/** Gas summary measured by the Impact VM cost model. */
export interface GasSummary {
  readonly readTimePs: bigint;
  readonly computeTimePs: bigint;
  readonly bytesWritten: bigint;
  readonly bytesDeleted: bigint;
}

/** Result of executing gather-mode Impact VM ops against a contract state. */
export interface VmQueryResult {
  readonly stateBytes: Uint8Array;
  readonly verifiedOpsJson: string;
  readonly readsJson: string;
  readonly gas: GasSummary;
}

/** Parameters for building a canonical contract-call ProofPreimage. */
export interface BuildPreimageInput {
  readonly inputJson?: string;
  readonly outputJson?: string;
  readonly privateTranscriptOutputsJson?: string;
  readonly verifiedOpsJson: string;
  readonly bindingInput?: Uint8Array;
  readonly commCommRand?: Uint8Array;
  readonly keyLocation: string;
}

/** Result of generating a Halo2 proof. */
export interface ProveResult {
  readonly proofBytes: Uint8Array;
  readonly publicInputs: Uint8Array[];
  readonly piSkips: Array<number | null>;
}

/** Result of compiling proving and verifier keys from `.bzkir`. */
export interface CompiledKeys {
  readonly proverKey: Uint8Array;
  readonly verifierKey: Uint8Array;
  readonly k: number;
}

/**
 * Low-level protocol engine interface implemented by `@rvcas/midnight/node` (native `napi-rs`)
 * and `@rvcas/midnight/wasm` (browser WebAssembly).
 */
export interface MidnightEngine {
  transientHash(elems: Uint8Array[]): Uint8Array;
  hashToField(data: Uint8Array): Uint8Array;
  ecAdd(a: EcPoint, b: EcPoint): EcPoint;
  ecMul(point: EcPoint, scalar: Uint8Array): EcPoint;
  ecMulGenerator(scalar: Uint8Array): EcPoint;
  sampleCommCommRand(): Uint8Array;
  sampleSigningKey(): Uint8Array;
  signatureVerifyingKey(signingKey: Uint8Array): Uint8Array;
  signData(signingKey: Uint8Array, message: Uint8Array): Uint8Array;
  verifySignature(verifyingKey: Uint8Array, message: Uint8Array, signature: Uint8Array): boolean;

  emptyStateValueBytes(): Uint8Array;
  stateValueCounterBytes(value: bigint): Uint8Array;
  stateValueArrayBytes(items: Uint8Array[]): Uint8Array;
  readCounterAtBytes(stateBytes: Uint8Array, index: number): bigint;
  queryGatherJson(stateBytes: Uint8Array, address: Uint8Array, opsJson: string): VmQueryResult;

  irK(irBytes: Uint8Array): number;
  jsonIrToBinary(json: string): Uint8Array;
  buildContractProofPreimageBytes(input: BuildPreimageInput): Uint8Array;
  checkPreimage(preimageBytes: Uint8Array, irBytes: Uint8Array): Array<number | null>;
  verifyProof(proofBytes: Uint8Array, vkBytes: Uint8Array, publicInputs: Uint8Array[]): boolean;
}

let activeEngine: MidnightEngine | null = null;

/** Register the active runtime engine (called automatically by `@rvcas/midnight/node` or `/wasm`). */
export function setDefaultEngine(engine: MidnightEngine): void {
  activeEngine = engine;
}

/** Return the currently registered runtime engine, or throw a helpful setup error. */
export function getDefaultEngine(): MidnightEngine {
  if (!activeEngine) {
    throw new Error(
      "No Midnight engine is registered. Import `@rvcas/midnight/node` (Node.js) or `@rvcas/midnight/wasm` (browser), or call `setDefaultEngine(...)`.",
    );
  }
  return activeEngine;
}
