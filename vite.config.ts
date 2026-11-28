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

import { defineConfig } from "vite-plus";

export default defineConfig({
  fmt: {
    semi: true,
    ignorePatterns: [
      "compact-scheme/**",
      "target/**",
      "crates/**",
      "tests/conformance/**",
      "packages/*/dist/**",
      "packages/native/index.js",
      "packages/native/index.d.ts",
      ".github/workflows/release.yml",
      "**/*.toml",
      "pnpm-lock.yaml",
    ],
  },
  lint: {
    ignorePatterns: [
      "compact-scheme/**",
      "target/**",
      "crates/**",
      "tests/conformance/**",
      "packages/*/dist/**",
      "packages/native/index.js",
      "packages/native/index.d.ts",
    ],
  },
  test: {
    projects: [
      {
        test: {
          name: "unit",
          root: "packages/midnight",
          include: ["test/unit/**/*.test.ts"],
          environment: "node",
        },
      },
      {
        test: {
          name: "e2e",
          root: "packages/midnight",
          include: ["test/e2e/**/*.test.ts"],
          environment: "node",
        },
      },
    ],
  },
  run: {
    tasks: {
      "build:cli": {
        command: "cargo build -p compact",
        cache: false,
      },
    },
  },
});
