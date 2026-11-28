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
 * `@rvcas/midnight/wasm` — Browser-safe fetch artifact providers and Web Worker WASM prover.
 */

import type { ProvingKeyMaterial, ZKConfigProvider } from "./providers.js";

/**
 * Browser-safe `ZKConfigProvider` fetching `zkir/<circuit>.bzkir` and
 * `keys/<circuit>.{prover,verifier}` over HTTP(S).
 */
export function createFetchZkConfigProvider(baseUrl: string): ZKConfigProvider {
  const root = baseUrl.endsWith("/") ? baseUrl.slice(0, -1) : baseUrl;

  async function fetchBytes(relPath: string): Promise<Uint8Array> {
    const res = await fetch(`${root}/${relPath}`);
    if (!res.ok) {
      throw new Error(`Failed to fetch ZK artifact ${relPath}: HTTP ${res.status}`);
    }
    return new Uint8Array(await res.arrayBuffer());
  }

  const getProverKey = (circuitId: string): Promise<Uint8Array> =>
    fetchBytes(`keys/${circuitId}.prover`);

  const getVerifierKey = (circuitId: string): Promise<Uint8Array> =>
    fetchBytes(`keys/${circuitId}.verifier`);

  const getIr = (circuitId: string): Promise<Uint8Array> => fetchBytes(`zkir/${circuitId}.bzkir`);

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
