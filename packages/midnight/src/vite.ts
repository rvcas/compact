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
 * `@rvcas/midnight/vite` — Vite plugin for Compact smart contracts.
 *
 * Watches `.compact` source files and invokes the `compact` CLI (`compact build`) automatically
 * during dev/build without embedding the compiler in JavaScript.
 */

import { execFile } from "node:child_process";
import { promisify } from "node:util";

const execFileAsync = promisify(execFile);

/** Options for the `compact()` Vite plugin. */
export interface CompactVitePluginOptions {
  /** Path to the `compact` CLI binary (defaults to `"compact"` on `PATH`). */
  readonly binary?: string;
  /** Entry `.compact` source files to compile. */
  readonly contracts: ReadonlyArray<{
    readonly source: string;
    readonly outDir: string;
    readonly skipZk?: boolean;
  }>;
}

/** Minimal Vite plugin shape (avoids hard runtime dependency on `vite`). */
export interface CompactVitePlugin {
  readonly name: string;
  buildStart(): Promise<void>;
  handleHotUpdate?(ctx: { file: string }): Promise<void>;
}

/** Create a Vite plugin that compiles `.compact` contracts with the `compact` CLI. */
export function compact(options: CompactVitePluginOptions): CompactVitePlugin {
  const bin = options.binary ?? "compact";

  async function compileOne(entry: CompactVitePluginOptions["contracts"][number]): Promise<void> {
    const args = ["build", entry.source, entry.outDir];
    if (entry.skipZk) args.push("--skip-zk");
    await execFileAsync(bin, args);
  }

  return {
    name: "@rvcas/midnight/vite",
    async buildStart(): Promise<void> {
      await Promise.all(options.contracts.map(compileOne));
    },
    async handleHotUpdate(ctx: { file: string }): Promise<void> {
      if (!ctx.file.endsWith(".compact")) return;
      const matching = options.contracts.filter((c) => ctx.file.endsWith(c.source));
      await Promise.all((matching.length > 0 ? matching : options.contracts).map(compileOne));
    },
  };
}
