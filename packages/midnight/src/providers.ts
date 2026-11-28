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

import type { CompiledKeys, ProveResult } from "./engine.js";

/** Target Midnight network environment. */
export type NetworkId = "undeployed" | "preview" | "preprod" | "mainnet";

/** Public circuit artifacts emitted by `compact build` (or built-in Zswap/Dust circuits). */
export interface ProvingKeyMaterial {
  readonly proverKey: Uint8Array;
  readonly verifierKey: Uint8Array;
  readonly ir: Uint8Array;
}

/** Loads `.bzkir`, `.prover`, and `.verifier` circuit artifacts by circuit ID. */
export interface ZKConfigProvider {
  getZkConfig(circuitId: string): Promise<ProvingKeyMaterial>;
  getProverKey(circuitId: string): Promise<Uint8Array>;
  getVerifierKey(circuitId: string): Promise<Uint8Array>;
  getIr(circuitId: string): Promise<Uint8Array>;
}

/** Embedded or remote ZK proof provider (replaces the legacy Docker proof server). */
export interface ProofProvider {
  check(preimageBytes: Uint8Array, circuitId: string): Promise<Array<number | null>>;
  prove(
    preimageBytes: Uint8Array,
    circuitId: string,
    overwriteBindingInput?: Uint8Array,
  ): Promise<ProveResult>;
  verify(proofBytes: Uint8Array, circuitId: string, publicInputs: Uint8Array[]): Promise<boolean>;
  compileKeys?(irBytes: Uint8Array): Promise<CompiledKeys>;
}

/** Local storage provider for private contract state and contract signing keys. */
export interface PrivateStateProvider<PS = unknown> {
  get(privateStateId: string): Promise<PS | null>;
  set(privateStateId: string, state: PS): Promise<void>;
  remove(privateStateId: string): Promise<void>;
  clear(): Promise<void>;
  getSigningKey(contractAddress: string): Promise<Uint8Array | null>;
  setSigningKey(contractAddress: string, signingKey: Uint8Array): Promise<void>;
  removeSigningKey(contractAddress: string): Promise<void>;
}

/** Finalized transaction metadata returned by the Midnight Indexer. */
export interface FinalizedTxData {
  readonly txHash: string;
  readonly blockHeight: bigint;
  readonly blockHash: string;
  readonly status: "succeed" | "partial" | "fail";
}

/** Read-only query & subscription provider targeting a Midnight Indexer (GraphQL). */
export interface PublicDataProvider {
  queryContractState(contractAddress: string): Promise<Uint8Array | null>;
  watchForTxData(txHash: string): Promise<FinalizedTxData>;
}

/** Wallet adapter for balancing, signing, and exposing public keys. */
export interface WalletProvider {
  readonly coinPublicKey: string;
  readonly encryptionPublicKey: string;
  balanceTx(txBytes: Uint8Array): Promise<Uint8Array>;
}

/** Network submission adapter. */
export interface MidnightProvider {
  submitTx(txBytes: Uint8Array): Promise<string>;
}

/** Full bundle of providers required for live network interactions. */
export interface MidnightProviders<PS = unknown> {
  readonly publicDataProvider: PublicDataProvider;
  readonly privateStateProvider: PrivateStateProvider<PS>;
  readonly zkConfigProvider: ZKConfigProvider;
  readonly proofProvider: ProofProvider;
  readonly walletProvider: WalletProvider;
  readonly midnightProvider: MidnightProvider;
}

/** Zero-dependency in-memory private state provider (ideal for tests and ephemeral scripts). */
export function createMemoryPrivateStateProvider<PS = unknown>(): PrivateStateProvider<PS> {
  const states = new Map<string, PS>();
  const signingKeys = new Map<string, Uint8Array>();

  return {
    async get(id: string): Promise<PS | null> {
      return states.has(id) ? (states.get(id) as PS) : null;
    },
    async set(id: string, state: PS): Promise<void> {
      states.set(id, state);
    },
    async remove(id: string): Promise<void> {
      states.delete(id);
    },
    async clear(): Promise<void> {
      states.clear();
      signingKeys.clear();
    },
    async getSigningKey(address: string): Promise<Uint8Array | null> {
      const key = signingKeys.get(address);
      return key ? new Uint8Array(key) : null;
    },
    async setSigningKey(address: string, key: Uint8Array): Promise<void> {
      signingKeys.set(address, new Uint8Array(key));
    },
    async removeSigningKey(address: string): Promise<void> {
      signingKeys.delete(address);
    },
  };
}

/** Configuration for the zero-dependency Midnight Indexer GraphQL provider. */
export interface IndexerProviderConfig {
  readonly httpUrl: string;
  readonly wsUrl?: string;
  readonly headers?: Record<string, string>;
}

/** Decode a lowercase/uppercase hex string (with optional `0x` prefix) to bytes. */
export function hexToBytes(hex: string): Uint8Array {
  const clean = hex.startsWith("0x") || hex.startsWith("0X") ? hex.slice(2) : hex;
  if (clean.length % 2 !== 0) {
    throw new Error(`Invalid hex string length: ${clean.length}`);
  }
  const out = new Uint8Array(clean.length / 2);
  for (let i = 0; i < out.length; i++) {
    const byte = Number.parseInt(clean.slice(i * 2, i * 2 + 2), 16);
    if (Number.isNaN(byte)) {
      throw new Error(`Invalid hex character at offset ${i * 2}`);
    }
    out[i] = byte;
  }
  return out;
}

/** Encode bytes as lowercase hex without `0x` prefix. */
export function bytesToHex(bytes: Uint8Array): string {
  let out = "";
  for (let i = 0; i < bytes.length; i++) {
    out += bytes[i]!.toString(16).padStart(2, "0");
  }
  return out;
}

/**
 * Runtime-agnostic GraphQL HTTP `PublicDataProvider` using native `fetch` (zero external deps).
 */
export function createIndexerPublicDataProvider(config: IndexerProviderConfig): PublicDataProvider {
  async function graphql<T>(query: string, variables: Record<string, unknown>): Promise<T> {
    const res = await fetch(config.httpUrl, {
      method: "POST",
      headers: {
        "content-type": "application/json",
        ...config.headers,
      },
      body: JSON.stringify({ query, variables }),
    });
    if (!res.ok) {
      throw new Error(`Indexer GraphQL HTTP ${res.status}: ${await res.text()}`);
    }
    const payload = (await res.json()) as { data?: T; errors?: Array<{ message: string }> };
    if (payload.errors && payload.errors.length > 0) {
      throw new Error(`Indexer GraphQL error: ${payload.errors.map((e) => e.message).join("; ")}`);
    }
    if (!payload.data) {
      throw new Error("Indexer GraphQL response missing data");
    }
    return payload.data;
  }

  return {
    async queryContractState(contractAddress: string): Promise<Uint8Array | null> {
      const data = await graphql<{
        contractAction: { state: string } | null;
      }>(
        `
          query ContractState($address: HexEncoded!) {
            contractAction(address: $address) {
              state
            }
          }
        `,
        { address: contractAddress },
      );
      return data.contractAction ? hexToBytes(data.contractAction.state) : null;
    },

    async watchForTxData(txHash: string): Promise<FinalizedTxData> {
      const data = await graphql<{
        transactions: Array<{
          hash: string;
          block: { height: number; hash: string };
          applyStage: string;
        }>;
      }>(
        `
          query TransactionByHash($hash: HexEncoded!) {
            transactions(offset: { hash: $hash }) {
              hash
              applyStage
              block {
                height
                hash
              }
            }
          }
        `,
        { hash: txHash },
      );
      const tx = data.transactions[0];
      if (!tx) {
        throw new Error(`Transaction ${txHash} not found on indexer`);
      }
      const status =
        tx.applyStage === "SucceedEntirely"
          ? "succeed"
          : tx.applyStage === "SucceedPartially"
            ? "partial"
            : "fail";
      return {
        txHash: tx.hash,
        blockHeight: BigInt(tx.block.height),
        blockHash: tx.block.hash,
        status,
      };
    },
  };
}
