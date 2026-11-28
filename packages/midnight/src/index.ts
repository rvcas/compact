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
 * `@rvcas/midnight` — Generic Midnight protocol SDK (zero Compact coupling).
 *
 * For Compact smart contract execution & generated contract bindings, import from
 * `@rvcas/midnight/compact`. For Node.js native proving and filesystem adapters,
 * import from `@rvcas/midnight/node`. For browser WASM proving, import from
 * `@rvcas/midnight/wasm`.
 */

export {
  getDefaultEngine,
  setDefaultEngine,
  type BuildPreimageInput,
  type CompiledKeys,
  type EcPoint,
  type GasSummary,
  type MidnightEngine,
  type ProveResult,
  type VmQueryResult,
} from "./engine.js";

export {
  bytesToHex,
  createIndexerPublicDataProvider,
  createMemoryPrivateStateProvider,
  hexToBytes,
  type FinalizedTxData,
  type IndexerProviderConfig,
  type MidnightProvider,
  type MidnightProviders,
  type NetworkId,
  type PrivateStateProvider,
  type ProofProvider,
  type ProvingKeyMaterial,
  type PublicDataProvider,
  type WalletProvider,
  type ZKConfigProvider,
} from "./providers.js";
