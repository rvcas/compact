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
import { execFileSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

import {
  createFsZkConfigProvider,
  createNativeProver,
  nativeEngine,
  useNativeEngine,
} from "../../src/node.js";
import { createContractSimulator } from "../../src/testing.js";

const TEST_DIR = dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = resolve(TEST_DIR, "../../../..");

describe("compiler <-> @rvcas/midnight e2e", () => {
  test("compiles examples/counter.compact, runs generated JS on native Impact VM, and checks ZKIR preimage", async () => {
    useNativeEngine();

    const tmp = mkdtempSync(join(tmpdir(), "midnight-sdk-e2e-"));
    try {
      const compactBin = join(REPO_ROOT, "target/debug/compact");
      const counterSrc = join(REPO_ROOT, "examples/counter.compact");
      execFileSync(compactBin, ["build", counterSrc, tmp, "--skip-zk"], {
        stdio: "pipe",
      });

      const generatedJsPath = join(tmp, "contract/index.js");
      const compactRuntimeUrl = pathToFileURL(resolve(TEST_DIR, "../../dist/compact.mjs")).href;
      const generatedJs = readFileSync(generatedJsPath, "utf8").replace(
        "@midnight-ntwrk/compact-runtime",
        compactRuntimeUrl,
      );
      const runnablePath = join(tmp, "contract/index.mjs");
      writeFileSync(runnablePath, generatedJs);

      const mod = (await import(pathToFileURL(runnablePath).href)) as {
        Contract: new (witnesses: Record<string, never>) => any;
        ledger: (state: any) => { readonly round: bigint };
      };

      const sim = createContractSimulator({
        contract: new mod.Contract({}),
        ledger: mod.ledger,
        initialPrivateState: {},
        engine: nativeEngine,
      });

      expect(sim.getLedger().round).toBe(0n);

      const step1 = sim.call("increment");
      expect(step1.result).toEqual([]);
      expect(step1.ledger.round).toBe(1n);
      expect(step1.gas.computeTimePs).toBeGreaterThan(0n);

      const step2 = sim.call("increment");
      expect(step2.ledger.round).toBe(2n);

      const zkConfig = createFsZkConfigProvider(tmp);
      const irBytes = await zkConfig.getIr("increment");
      expect(nativeEngine.irK(irBytes)).toBeGreaterThanOrEqual(1);

      const prover = createNativeProver(zkConfig);
      const skips = await prover.check(step1.preimageBytes, "increment");
      expect(skips.every((s) => s === null)).toBe(true);
    } finally {
      rmSync(tmp, { recursive: true, force: true });
    }
  });
});
