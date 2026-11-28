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

import { describe, expect, test } from "vite-plus/test";

import { bytesToHex, createMemoryPrivateStateProvider, hexToBytes } from "../../src/index.js";
import {
  CompactTypeBoolean,
  CompactTypeBytes,
  CompactTypeField,
  CompactTypeOpaqueString,
  CompactTypeUnsignedInteger,
  CompactTypeVector,
  assert,
  decodeCounter,
  ecAdd,
  ecMulGenerator,
  emptyContractState,
  equal,
  queryLedger,
  transientHash,
  type CircuitContext,
  type CircuitResults,
  type ConstructorContext,
  type ConstructorResult,
  type StateValue,
} from "../../src/compact.js";
import { nativeEngine, useNativeEngine } from "../../src/node.js";
import { createContractSimulator } from "../../src/testing.js";

describe("@rvcas/midnight core", () => {
  test("hex codecs and memory private state provider", async () => {
    const raw = new Uint8Array([0x00, 0xde, 0xad, 0xbe, 0xef]);
    const hex = bytesToHex(raw);
    expect(hex).toBe("00deadbeef");
    expect(hexToBytes(`0x${hex}`)).toEqual(raw);

    const store = createMemoryPrivateStateProvider<{ secret: bigint }>();
    expect(await store.get("alice")).toBeNull();
    await store.set("alice", { secret: 42n });
    expect(await store.get("alice")).toEqual({ secret: 42n });

    const sk = nativeEngine.sampleSigningKey();
    await store.setSigningKey("0x1234", sk);
    expect(await store.getSigningKey("0x1234")).toEqual(sk);
    await store.clear();
    expect(await store.get("alice")).toBeNull();
  });

  test("native crypto primitives (Poseidon, JubJub, Schnorr)", () => {
    useNativeEngine();

    const h1 = transientHash([1n, 2n]);
    const h2 = transientHash([1n, 2n]);
    const h3 = transientHash([2n, 1n]);
    expect(h1).toBe(h2);
    expect(h1).not.toBe(h3);

    const g1 = ecMulGenerator(1n);
    const g2Mul = ecMulGenerator(2n);
    const g2Add = ecAdd(g1, g1);
    expect(g2Mul).toEqual(g2Add);

    const sk = nativeEngine.sampleSigningKey();
    const vk = nativeEngine.signatureVerifyingKey(sk);
    const msg = new TextEncoder().encode("midnight-sdk");
    const sig = nativeEngine.signData(sk, msg);
    expect(nativeEngine.verifySignature(vk, msg, sig)).toBe(true);
    expect(nativeEngine.verifySignature(vk, new TextEncoder().encode("other"), sig)).toBe(false);
  });
});

describe("@rvcas/midnight/compact", () => {
  test("round-trips Field, Boolean, Uint, Bytes, Vector, and OpaqueString codecs", () => {
    expect(CompactTypeField.fromValue(CompactTypeField.toValue(123456789n))).toBe(123456789n);
    expect(CompactTypeField.fromValue(CompactTypeField.toValue(0n))).toBe(0n);

    expect(CompactTypeBoolean.fromValue(CompactTypeBoolean.toValue(true))).toBe(true);
    expect(CompactTypeBoolean.fromValue(CompactTypeBoolean.toValue(false))).toBe(false);

    const u64 = new CompactTypeUnsignedInteger((1n << 64n) - 1n, 8);
    expect(u64.fromValue(u64.toValue(0x1234_5678_9abc_defn))).toBe(0x1234_5678_9abc_defn);

    const b4 = new CompactTypeBytes(4);
    const bytes = new Uint8Array([1, 2, 3, 4]);
    expect(b4.fromValue(b4.toValue(bytes))).toEqual(bytes);

    const vec = new CompactTypeVector(3, u64);
    expect(vec.fromValue(vec.toValue([10n, 20n, 30n]))).toEqual([10n, 20n, 30n]);

    expect(CompactTypeOpaqueString.fromValue(CompactTypeOpaqueString.toValue("hello"))).toBe(
      "hello",
    );

    expect(equal({ a: 1n, b: new Uint8Array([9, 8]) }, { a: 1n, b: new Uint8Array([9, 8]) })).toBe(
      true,
    );
    expect(() => assert(false, "boom")).toThrow("failed assert: boom");
  });

  test("executes Impact VM counter increments via ContractSimulator", () => {
    const contract = {
      witnesses: {},
      impureCircuits: {
        increment(
          context: CircuitContext<Record<string, never>>,
        ): CircuitResults<Record<string, never>, []> {
          queryLedger(context, [
            { idx: { cached: false, pushPath: true, path: 0 } },
            { addi: { immediate: 1 } },
            { ins: { cached: true, n: 1 } },
          ]);
          return { result: [], context };
        },
      },
      initialState(
        context: ConstructorContext<Record<string, never>>,
      ): ConstructorResult<Record<string, never>> {
        return emptyContractState(context);
      },
    };

    const sim = createContractSimulator({
      contract,
      ledger: (state: StateValue) => ({ round: decodeCounter(state, 0) }),
      initialPrivateState: {},
      engine: nativeEngine,
    });

    expect(sim.getLedger().round).toBe(0n);
    const s1 = sim.call("increment");
    expect(s1.ledger.round).toBe(1n);
    expect(s1.gas.computeTimePs).toBeGreaterThan(0n);
    expect(s1.preimageBytes.length).toBeGreaterThan(0);

    const s2 = sim.call("increment");
    expect(s2.ledger.round).toBe(2n);
  });
});
