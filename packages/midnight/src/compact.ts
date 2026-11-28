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
 * `@rvcas/midnight/compact` — Compact smart contract runtime.
 *
 * Everything specific to the Compact language lives here so `@rvcas/midnight` stays
 * completely decoupled from Compact. Compiled `.compact` contracts import this module.
 */

import { getDefaultEngine, type EcPoint, type GasSummary, type MidnightEngine } from "./engine.js";

/** Runtime error thrown by Compact contract assertions and type guards. */
export class CompactError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "CompactError";
  }
}

/** BLS12-381 scalar field modulus `r` used by Compact `Field` values. */
export const MAX_FIELD: bigint =
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000n;

/** Compact `assert(condition, message)` builtin. */
export function assert(condition: boolean, message: string): void {
  if (!condition) {
    throw new CompactError(`failed assert: ${message}`);
  }
}

/** Structural deep equality for Compact values (`bigint`, `Uint8Array`, arrays, records). */
export function equal(a: unknown, b: unknown): boolean {
  if (Object.is(a, b)) return true;
  if (a instanceof Uint8Array && b instanceof Uint8Array) {
    if (a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) {
      if (a[i] !== b[i]) return false;
    }
    return true;
  }
  if (Array.isArray(a) && Array.isArray(b)) {
    if (a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) {
      if (!equal(a[i], b[i])) return false;
    }
    return true;
  }
  if (
    typeof a === "object" &&
    a !== null &&
    typeof b === "object" &&
    b !== null &&
    Object.getPrototypeOf(a) === Object.getPrototypeOf(b)
  ) {
    const ka = Object.keys(a as Record<string, unknown>);
    const kb = Object.keys(b as Record<string, unknown>);
    if (ka.length !== kb.length) return false;
    for (const k of ka) {
      if (
        !Object.prototype.hasOwnProperty.call(b, k) ||
        !equal((a as Record<string, unknown>)[k], (b as Record<string, unknown>)[k])
      ) {
        return false;
      }
    }
    return true;
  }
  return false;
}

/** Encode a non-negative `bigint` into a fixed-length little-endian `Uint8Array`. */
export function bigIntToLeBytes(value: bigint, length: number): Uint8Array {
  if (value < 0n) {
    throw new CompactError(`expected non-negative bigint, got ${value}`);
  }
  const out = new Uint8Array(length);
  let cur = value;
  for (let i = 0; i < length; i++) {
    out[i] = Number(cur & 0xffn);
    cur >>= 8n;
  }
  if (cur !== 0n) {
    throw new CompactError(`bigint ${value} does not fit in ${length} bytes`);
  }
  return out;
}

/** Decode a little-endian `Uint8Array` into a non-negative `bigint`. */
export function leBytesToBigInt(bytes: Uint8Array): bigint {
  let out = 0n;
  for (let i = bytes.length - 1; i >= 0; i--) {
    out = (out << 8n) | BigInt(bytes[i]!);
  }
  return out;
}

/** Canonical Midnight FAB value atom sequence (arrays of byte chunks). */
export type Value = Uint8Array[];

/** Canonical Midnight FAB alignment atom. */
export type AlignmentAtom =
  | { readonly tag: "field" }
  | { readonly tag: "bytes"; readonly length: number }
  | { readonly tag: "compress" };

/** Canonical Midnight FAB alignment segment. */
export type AlignmentSegment = { readonly tag: "atom"; readonly value: AlignmentAtom };

/** Canonical Midnight FAB alignment descriptor. */
export type Alignment = AlignmentSegment[];

/** Field-aligned binary value pairing raw atoms with their alignment. */
export interface AlignedValue {
  readonly value: Value;
  readonly alignment: Alignment;
}

/** Runtime codec descriptor for a Compact type `A`. */
export interface CompactType<A> {
  alignment(): Alignment;
  toValue(value: A): Value;
  fromValue(value: Value): A;
}

function trimTrailingZeros(bytes: Uint8Array): Uint8Array {
  let end = bytes.length;
  while (end > 0 && bytes[end - 1] === 0) {
    end--;
  }
  return bytes.slice(0, end);
}

/** Runtime codec for Compact `Field`. */
export const CompactTypeField: CompactType<bigint> = {
  alignment(): Alignment {
    return [{ tag: "atom", value: { tag: "field" } }];
  },
  toValue(value: bigint): Value {
    if (value < 0n || value > MAX_FIELD) {
      throw new CompactError(`Field value out of range: ${value}`);
    }
    return [trimTrailingZeros(bigIntToLeBytes(value, 32))];
  },
  fromValue(value: Value): bigint {
    const atom = value.shift();
    if (!atom) throw new CompactError("Expected Field atom");
    return leBytesToBigInt(atom);
  },
};

/** Runtime codec for Compact `Boolean`. */
export const CompactTypeBoolean: CompactType<boolean> = {
  alignment(): Alignment {
    return [{ tag: "atom", value: { tag: "bytes", length: 1 } }];
  },
  toValue(value: boolean): Value {
    return [value ? new Uint8Array([1]) : new Uint8Array([])];
  },
  fromValue(value: Value): boolean {
    const atom = value.shift();
    if (!atom) throw new CompactError("Expected Boolean atom");
    return atom.length > 0 && atom[0] !== 0;
  },
};

/** Runtime codec for Compact `Uint<0..max>` / `Uint<n>`. */
export class CompactTypeUnsignedInteger implements CompactType<bigint> {
  readonly maxVal: bigint;
  readonly bytesLength: number;

  constructor(maxVal: bigint, bytesLength: number) {
    this.maxVal = maxVal;
    this.bytesLength = bytesLength;
  }

  alignment(): Alignment {
    return [{ tag: "atom", value: { tag: "bytes", length: this.bytesLength } }];
  }

  toValue(value: bigint): Value {
    if (value < 0n || value > this.maxVal) {
      throw new CompactError(`Uint value ${value} out of range 0..${this.maxVal}`);
    }
    return [trimTrailingZeros(bigIntToLeBytes(value, this.bytesLength))];
  }

  fromValue(value: Value): bigint {
    const atom = value.shift();
    if (!atom) throw new CompactError("Expected Uint atom");
    const decoded = leBytesToBigInt(atom);
    if (decoded > this.maxVal) {
      throw new CompactError(`Decoded Uint ${decoded} exceeds max ${this.maxVal}`);
    }
    return decoded;
  }
}

/** Runtime codec for Compact `Bytes<n>`. */
export class CompactTypeBytes implements CompactType<Uint8Array> {
  readonly length: number;

  constructor(length: number) {
    this.length = length;
  }

  alignment(): Alignment {
    return [{ tag: "atom", value: { tag: "bytes", length: this.length } }];
  }

  toValue(value: Uint8Array): Value {
    if (value.length !== this.length) {
      throw new CompactError(`Expected Bytes<${this.length}>, got length ${value.length}`);
    }
    return [new Uint8Array(value)];
  }

  fromValue(value: Value): Uint8Array {
    const atom = value.shift();
    if (!atom) throw new CompactError(`Expected Bytes<${this.length}> atom`);
    const out = new Uint8Array(this.length);
    out.set(atom.subarray(0, this.length));
    return out;
  }
}

/** Runtime codec for Compact `Vector<n, T>`. */
export class CompactTypeVector<T> implements CompactType<T[]> {
  readonly length: number;
  readonly innerType: CompactType<T>;

  constructor(length: number, innerType: CompactType<T>) {
    this.length = length;
    this.innerType = innerType;
  }

  alignment(): Alignment {
    const out: AlignmentSegment[] = [];
    const inner = this.innerType.alignment();
    for (let i = 0; i < this.length; i++) {
      out.push(...inner);
    }
    return out;
  }

  toValue(value: T[]): Value {
    if (value.length !== this.length) {
      throw new CompactError(`Expected Vector<${this.length}>, got length ${value.length}`);
    }
    const out: Value = [];
    for (const item of value) {
      out.push(...this.innerType.toValue(item));
    }
    return out;
  }

  fromValue(value: Value): T[] {
    const out: T[] = [];
    for (let i = 0; i < this.length; i++) {
      out.push(this.innerType.fromValue(value));
    }
    return out;
  }
}

/** Runtime codec for Compact `Opaque<"string">`. */
export const CompactTypeOpaqueString: CompactType<string> = {
  alignment(): Alignment {
    return [{ tag: "atom", value: { tag: "compress" } }];
  },
  toValue(value: string): Value {
    return [new TextEncoder().encode(value)];
  },
  fromValue(value: Value): string {
    const atom = value.shift();
    if (!atom) throw new CompactError('Expected Opaque<"string"> atom');
    return new TextDecoder().decode(atom);
  },
};

/** Runtime codec for Compact `Opaque<"Uint8Array">`. */
export const CompactTypeOpaqueUint8Array: CompactType<Uint8Array> = {
  alignment(): Alignment {
    return [{ tag: "atom", value: { tag: "compress" } }];
  },
  toValue(value: Uint8Array): Value {
    return [new Uint8Array(value)];
  },
  fromValue(value: Value): Uint8Array {
    const atom = value.shift();
    if (!atom) throw new CompactError('Expected Opaque<"Uint8Array"> atom');
    return atom;
  },
};

/** Tagged-serialized Impact VM `StateValue` handle backed by a `MidnightEngine`. */
export class StateValue {
  readonly bytes: Uint8Array;
  readonly engine: MidnightEngine;

  constructor(bytes: Uint8Array, engine: MidnightEngine = getDefaultEngine()) {
    this.bytes = bytes;
    this.engine = engine;
  }

  static empty(engine: MidnightEngine = getDefaultEngine()): StateValue {
    return new StateValue(engine.emptyStateValueBytes(), engine);
  }

  static counter(value: bigint = 0n, engine: MidnightEngine = getDefaultEngine()): StateValue {
    return new StateValue(engine.stateValueCounterBytes(value), engine);
  }

  static array(items: StateValue[], engine: MidnightEngine = getDefaultEngine()): StateValue {
    return new StateValue(engine.stateValueArrayBytes(items.map((item) => item.bytes)), engine);
  }
}

/** Accumulated proof transcript data produced while executing a Compact circuit. */
export interface PartialProofData {
  readonly inputJson?: string;
  readonly outputJson?: string;
  readonly privateTranscriptOutputsJson: string[];
  readonly verifiedOpsJson: string[];
  readonly gas: GasSummary;
}

/** Execution context passed into compiled Compact impure circuits. */
export interface CircuitContext<PS = unknown> {
  currentPrivateState: PS;
  currentState: StateValue;
  readonly contractAddress: Uint8Array;
  readonly engine: MidnightEngine;
  proofData: PartialProofData;
}

/** Return envelope of a compiled Compact impure circuit. */
export interface CircuitResults<PS = unknown, R = unknown> {
  readonly result: R;
  readonly context: CircuitContext<PS>;
}

/** Input context passed into a compiled Compact contract's `initialState`. */
export interface ConstructorContext<PS = unknown> {
  readonly initialPrivateState: PS;
  readonly initialState?: StateValue;
  readonly contractAddress?: Uint8Array;
  readonly engine?: MidnightEngine;
}

/** Return envelope of a compiled Compact contract's `initialState`. */
export interface ConstructorResult<PS = unknown> {
  readonly currentContractState: StateValue;
  readonly currentPrivateState: PS;
}

/** Create a fresh `CircuitContext` for executing a compiled Compact circuit. */
export function createCircuitContext<PS>(options: {
  privateState: PS;
  state: StateValue;
  contractAddress?: Uint8Array;
  engine?: MidnightEngine;
}): CircuitContext<PS> {
  const engine = options.engine ?? options.state.engine ?? getDefaultEngine();
  return {
    currentPrivateState: options.privateState,
    currentState: options.state,
    contractAddress: options.contractAddress ?? new Uint8Array(32),
    engine,
    proofData: {
      privateTranscriptOutputsJson: [],
      verifiedOpsJson: [],
      gas: {
        readTimePs: 0n,
        computeTimePs: 0n,
        bytesWritten: 0n,
        bytesDeleted: 0n,
      },
    },
  };
}

/** Initialize a contract's ledger state (called by `Contract.initialState`). */
export function emptyContractState<PS>(
  context: ConstructorContext<PS>,
  slotCount: number = 1,
): ConstructorResult<PS> {
  const engine = context.engine ?? context.initialState?.engine ?? getDefaultEngine();
  const state =
    context.initialState ??
    StateValue.array(
      Array.from({ length: slotCount }, () => StateValue.counter(0n, engine)),
      engine,
    );
  return {
    currentContractState: state,
    currentPrivateState: context.initialPrivateState,
  };
}

/** Read a `Counter` ledger field at slot `index` from a `StateValue`. */
export function decodeCounter(state: StateValue, index: number): bigint {
  return state.engine.readCounterAtBytes(state.bytes, index);
}

function encodeSmallUintPathKey(slot: number): Record<string, unknown> {
  if (!Number.isInteger(slot) || slot < 0 || slot > 255) {
    throw new CompactError(`Ledger slot index out of range: ${slot}`);
  }
  return {
    tag: "value",
    value: {
      value: [slot === 0 ? [] : [slot]],
      alignment: [{ tag: "atom", value: { tag: "bytes", length: 1 } }],
    },
  };
}

/** Normalize simplified compiler op objects into canonical `midnight-onchain-vm` Op JSON. */
function normalizeImpactOps(ops: unknown[]): unknown[] {
  return ops.map((rawOp) => {
    if (typeof rawOp === "object" && rawOp !== null && "idx" in rawOp) {
      const idx = (rawOp as { idx: { cached: boolean; pushPath: boolean; path: unknown } }).idx;
      const rawPath = Array.isArray(idx.path) ? idx.path : [idx.path];
      const normalizedPath = rawPath.map((entry) =>
        typeof entry === "number" ? encodeSmallUintPathKey(entry) : entry,
      );
      return {
        idx: {
          cached: idx.cached,
          pushPath: idx.pushPath,
          path: normalizedPath,
        },
      };
    }
    return rawOp;
  });
}

/**
 * Execute Impact VM ledger ops on `context.currentState` via the active native/WASM engine,
 * updating `context.currentState` and recording verified transcript ops + gas in `context.proofData`.
 */
export function queryLedger<PS>(context: CircuitContext<PS>, ops: unknown[]): unknown[] {
  const normalized = normalizeImpactOps(ops);
  const res = context.engine.queryGatherJson(
    context.currentState.bytes,
    context.contractAddress,
    JSON.stringify(normalized),
  );
  context.currentState = new StateValue(res.stateBytes, context.engine);

  const prevGas = context.proofData.gas;
  const newVerified = JSON.parse(res.verifiedOpsJson) as unknown[];
  const existingVerified = context.proofData.verifiedOpsJson.flatMap(
    (chunk) => JSON.parse(chunk) as unknown[],
  );
  context.proofData = {
    ...context.proofData,
    verifiedOpsJson: [JSON.stringify([...existingVerified, ...newVerified])],
    gas: {
      readTimePs: prevGas.readTimePs + res.gas.readTimePs,
      computeTimePs: prevGas.computeTimePs + res.gas.computeTimePs,
      bytesWritten: prevGas.bytesWritten + res.gas.bytesWritten,
      bytesDeleted: prevGas.bytesDeleted + res.gas.bytesDeleted,
    },
  };
  return JSON.parse(res.readsJson) as unknown[];
}

/** Build canonical tagged `ProofPreimage` bytes from a completed `CircuitContext`. */
export function buildProofPreimage<PS>(
  context: CircuitContext<PS>,
  keyLocation: string,
  options?: {
    bindingInput?: Uint8Array;
    commCommRand?: Uint8Array;
  },
): Uint8Array {
  const verifiedOpsJson = context.proofData.verifiedOpsJson[0] ?? "[]";
  return context.engine.buildContractProofPreimageBytes({
    inputJson: context.proofData.inputJson,
    outputJson: context.proofData.outputJson,
    privateTranscriptOutputsJson:
      context.proofData.privateTranscriptOutputsJson.length > 0
        ? `[${context.proofData.privateTranscriptOutputsJson.join(",")}]`
        : undefined,
    verifiedOpsJson,
    bindingInput: options?.bindingInput,
    commCommRand: options?.commCommRand,
    keyLocation,
  });
}

/** Poseidon transient hash builtin (`Field[] -> Field`). */
export function transientHash(
  elems: bigint[],
  engine: MidnightEngine = getDefaultEngine(),
): bigint {
  const raw = elems.map((e) => bigIntToLeBytes(e, 32));
  return leBytesToBigInt(engine.transientHash(raw));
}

/** JubJub curve point addition builtin. */
export function ecAdd(
  a: { readonly x: bigint; readonly y: bigint },
  b: { readonly x: bigint; readonly y: bigint },
  engine: MidnightEngine = getDefaultEngine(),
): { readonly x: bigint; readonly y: bigint } {
  const pa: EcPoint = { x: bigIntToLeBytes(a.x, 32), y: bigIntToLeBytes(a.y, 32) };
  const pb: EcPoint = { x: bigIntToLeBytes(b.x, 32), y: bigIntToLeBytes(b.y, 32) };
  const sum = engine.ecAdd(pa, pb);
  return { x: leBytesToBigInt(sum.x), y: leBytesToBigInt(sum.y) };
}

/** JubJub generator scalar multiplication builtin. */
export function ecMulGenerator(
  scalar: bigint,
  engine: MidnightEngine = getDefaultEngine(),
): { readonly x: bigint; readonly y: bigint } {
  const prod = engine.ecMulGenerator(bigIntToLeBytes(scalar, 32));
  return { x: leBytesToBigInt(prod.x), y: leBytesToBigInt(prod.y) };
}
