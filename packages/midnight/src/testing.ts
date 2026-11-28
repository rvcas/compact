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
 * `@rvcas/midnight/testing` — Zero-network, zero-Docker in-memory Compact contract simulator.
 *
 * Executes compiled Compact circuits against the real Impact VM and can optionally check
 * witnesses or generate/verify real Halo2 proofs in-process.
 */

import {
  buildProofPreimage,
  createCircuitContext,
  type CircuitContext,
  type CircuitResults,
  type ConstructorContext,
  type ConstructorResult,
  type StateValue,
} from "./compact.js";
import { getDefaultEngine, type GasSummary, type MidnightEngine } from "./engine.js";

/** Minimal structural shape of a `compact build`-generated `Contract` class. */
export interface CompiledContract<PS, W, C extends Record<string, (...args: never[]) => unknown>> {
  readonly witnesses: W;
  readonly impureCircuits: C;
  initialState(context: ConstructorContext<PS>): ConstructorResult<PS>;
}

/** Result of executing an impure circuit inside `ContractSimulator`. */
export interface SimulationCallResult<PS, L, R> {
  readonly result: R;
  readonly ledger: L;
  readonly state: StateValue;
  readonly privateState: PS;
  readonly gas: GasSummary;
  readonly preimageBytes: Uint8Array;
}

/** In-memory Compact contract simulator. */
export interface ContractSimulator<
  PS,
  L,
  C extends Record<
    string,
    (context: CircuitContext<PS>, ...args: any[]) => CircuitResults<PS, any>
  >,
> {
  readonly contractAddress: Uint8Array;
  getState(): StateValue;
  getPrivateState(): PS;
  getLedger(): L;
  call<K extends keyof C & string>(
    circuitId: K,
    ...args: Parameters<C[K]> extends [CircuitContext<PS>, ...infer Rest] ? Rest : never
  ): SimulationCallResult<PS, L, ReturnType<C[K]>["result"]>;
  check(preimageBytes: Uint8Array, irBytes: Uint8Array): Array<number | null>;
}

/** Create an in-memory simulator for a compiled Compact contract. */
export function createContractSimulator<
  PS,
  W,
  L,
  C extends Record<
    string,
    (context: CircuitContext<PS>, ...args: any[]) => CircuitResults<PS, any>
  >,
>(options: {
  contract: CompiledContract<PS, W, C>;
  ledger: (state: StateValue) => L;
  initialPrivateState: PS;
  initialState?: StateValue;
  contractAddress?: Uint8Array;
  engine?: MidnightEngine;
}): ContractSimulator<PS, L, C> {
  const engine = options.engine ?? getDefaultEngine();
  const contractAddress = options.contractAddress ?? new Uint8Array(32);

  const init = options.contract.initialState({
    initialPrivateState: options.initialPrivateState,
    initialState: options.initialState,
    contractAddress,
    engine,
  });

  let currentState = init.currentContractState;
  let currentPrivateState = init.currentPrivateState;

  return {
    contractAddress,

    getState(): StateValue {
      return currentState;
    },

    getPrivateState(): PS {
      return currentPrivateState;
    },

    getLedger(): L {
      return options.ledger(currentState);
    },

    call<K extends keyof C & string>(
      circuitId: K,
      ...args: Parameters<C[K]> extends [CircuitContext<PS>, ...infer Rest] ? Rest : never
    ): SimulationCallResult<PS, L, ReturnType<C[K]>["result"]> {
      const fn = options.contract.impureCircuits[circuitId];
      if (!fn) {
        throw new Error(`Unknown impure circuit '${circuitId}'`);
      }
      const ctx = createCircuitContext({
        privateState: currentPrivateState,
        state: currentState,
        contractAddress,
        engine,
      });
      const out = fn(ctx, ...args);
      currentState = out.context.currentState;
      currentPrivateState = out.context.currentPrivateState;
      const preimageBytes = buildProofPreimage(out.context, circuitId);
      return {
        result: out.result,
        ledger: options.ledger(currentState),
        state: currentState,
        privateState: currentPrivateState,
        gas: out.context.proofData.gas,
        preimageBytes,
      };
    },

    check(preimageBytes: Uint8Array, irBytes: Uint8Array): Array<number | null> {
      return engine.checkPreimage(preimageBytes, irBytes);
    },
  };
}
