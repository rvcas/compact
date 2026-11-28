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

/**
 * `@rvcas/midnight/node` — Node.js native `napi-rs` engine, embedded multi-core Halo2
 * prover, and filesystem artifact providers (zero Docker proof server required).
 */

import { readFile } from "node:fs/promises";
import { join } from "node:path";
import * as native from "@rvcas/midnight-native";

import {
  setDefaultEngine,
  type BuildPreimageInput,
  type CompiledKeys,
  type EcPoint,
  type MidnightEngine,
  type ProveResult,
  type VmQueryResult,
} from "./engine.js";
import type { ProofProvider, ProvingKeyMaterial, ZKConfigProvider } from "./providers.js";

/** Native Rust (`napi-rs`) implementation of `MidnightEngine` for Node.js. */
export const nativeEngine: MidnightEngine = {
  transientHash(elems: Uint8Array[]): Uint8Array {
    return native.transientHash(elems);
  },
  hashToField(data: Uint8Array): Uint8Array {
    return native.hashToField(data);
  },
  ecAdd(a: EcPoint, b: EcPoint): EcPoint {
    return native.ecAdd(a.x, a.y, b.x, b.y);
  },
  ecMul(point: EcPoint, scalar: Uint8Array): EcPoint {
    return native.ecMul(point.x, point.y, scalar);
  },
  ecMulGenerator(scalar: Uint8Array): EcPoint {
    return native.ecMulGenerator(scalar);
  },
  sampleCommCommRand(): Uint8Array {
    return native.sampleCommCommRand();
  },
  sampleSigningKey(): Uint8Array {
    return native.sampleSigningKey();
  },
  signatureVerifyingKey(signingKey: Uint8Array): Uint8Array {
    return native.signatureVerifyingKey(signingKey);
  },
  signData(signingKey: Uint8Array, message: Uint8Array): Uint8Array {
    return native.signData(signingKey, message);
  },
  verifySignature(verifyingKey: Uint8Array, message: Uint8Array, signature: Uint8Array): boolean {
    return native.verifySignature(verifyingKey, message, signature);
  },
  emptyStateValueBytes(): Uint8Array {
    return native.emptyStateValueBytes();
  },
  stateValueCounterBytes(value: bigint): Uint8Array {
    return native.stateValueCounterBytes(value);
  },
  stateValueArrayBytes(items: Uint8Array[]): Uint8Array {
    return native.stateValueArrayBytes(items);
  },
  readCounterAtBytes(stateBytes: Uint8Array, index: number): bigint {
    return native.readCounterAtBytes(stateBytes, index);
  },
  queryGatherJson(stateBytes: Uint8Array, address: Uint8Array, opsJson: string): VmQueryResult {
    return native.queryGatherJson(stateBytes, address, opsJson);
  },
  irK(irBytes: Uint8Array): number {
    return native.irK(irBytes);
  },
  jsonIrToBinary(json: string): Uint8Array {
    return native.jsonIrToBinary(json);
  },
  buildContractProofPreimageBytes(input: BuildPreimageInput): Uint8Array {
    return native.buildContractProofPreimageBytes(input);
  },
  checkPreimage(preimageBytes: Uint8Array, irBytes: Uint8Array): Array<number | null> {
    return native.checkPreimage(preimageBytes, irBytes).map((v) => v ?? null);
  },
  verifyProof(proofBytes: Uint8Array, vkBytes: Uint8Array, publicInputs: Uint8Array[]): boolean {
    return native.verifyProof(proofBytes, vkBytes, publicInputs);
  },
};

/** Register `nativeEngine` as the default engine for `@rvcas/midnight/compact`. */
export function useNativeEngine(): MidnightEngine {
  setDefaultEngine(nativeEngine);
  return nativeEngine;
}

/**
 * Load `.bzkir`, `.prover`, and `.verifier` circuit artifacts directly from a `compact build`
 * output directory (`<dir>/zkir/<circuit>.bzkir`, `<dir>/keys/<circuit>.{prover,verifier}`).
 */
export function createFsZkConfigProvider(buildDir: string): ZKConfigProvider {
  const getProverKey = async (circuitId: string): Promise<Uint8Array> =>
    new Uint8Array(await readFile(join(buildDir, "keys", `${circuitId}.prover`)));

  const getVerifierKey = async (circuitId: string): Promise<Uint8Array> =>
    new Uint8Array(await readFile(join(buildDir, "keys", `${circuitId}.verifier`)));

  const getIr = async (circuitId: string): Promise<Uint8Array> =>
    new Uint8Array(await readFile(join(buildDir, "zkir", `${circuitId}.bzkir`)));

  const getZkConfig = async (circuitId: string): Promise<ProvingKeyMaterial> => {
    const [proverKey, verifierKey, ir] = await Promise.all([
      getProverKey(circuitId),
      getVerifierKey(circuitId),
      getIr(circuitId),
    ]);
    return { proverKey, verifierKey, ir };
  };

  return { getZkConfig, getProverKey, getVerifierKey, getIr };
}

/**
 * Embedded native multi-core Halo2 `ProofProvider` backed by `midnight-napi`.
 *
 * Runs Halo2 proving off the JS event loop via libuv worker threads with zero-copy SRS caching —
 * zero Docker proof server required.
 */
export function createNativeProver(zkConfigProvider: ZKConfigProvider): ProofProvider & {
  insertParams(k: number, rawBytes: Uint8Array): void;
} {
  const handle = new native.NativeProverHandle();

  return {
    insertParams(k: number, rawBytes: Uint8Array): void {
      handle.insertParams(k, rawBytes);
    },

    async check(preimageBytes: Uint8Array, circuitId: string): Promise<Array<number | null>> {
      const ir = await zkConfigProvider.getIr(circuitId);
      return native.checkPreimage(preimageBytes, ir).map((v) => v ?? null);
    },

    async prove(
      preimageBytes: Uint8Array,
      circuitId: string,
      overwriteBindingInput?: Uint8Array,
    ): Promise<ProveResult> {
      const { proverKey, ir } = await zkConfigProvider.getZkConfig(circuitId);
      const res = await handle.proveWithMaterial(
        preimageBytes,
        proverKey,
        ir,
        overwriteBindingInput,
      );
      return {
        proofBytes: res.proofBytes,
        publicInputs: res.publicInputs,
        piSkips: res.piSkips.map((v) => v ?? null),
      };
    },

    async verify(
      proofBytes: Uint8Array,
      circuitId: string,
      publicInputs: Uint8Array[],
    ): Promise<boolean> {
      const vk = await zkConfigProvider.getVerifierKey(circuitId);
      return native.verifyProof(proofBytes, vk, publicInputs);
    },

    async compileKeys(irBytes: Uint8Array): Promise<CompiledKeys> {
      return handle.compileKeys(irBytes);
    },
  };
}
