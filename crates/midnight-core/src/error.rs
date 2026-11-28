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

use thiserror::Error;

/// Structured error type for `midnight-core` protocol, VM, crypto, and proving operations.
#[derive(Debug, Error)]
pub enum MidnightError {
    #[error("invalid hex encoding: {0}")]
    InvalidHex(#[from] hex::FromHexError),

    #[error("field element out of range or malformed: {0}")]
    InvalidField(String),

    #[error("invalid embedded curve point: {0}")]
    InvalidPoint(String),

    #[error("invalid cryptographic key or signature: {0}")]
    InvalidKey(String),

    #[error("serialization error: {0}")]
    Serialization(String),

    #[error("JSON codec error: {0}")]
    Json(#[from] serde_json::Error),

    #[error("Impact VM execution failed: {0}")]
    VmExecution(String),

    #[error("invalid Impact state layout: {0}")]
    InvalidState(String),

    #[error("ZK proving failed: {0}")]
    Proving(String),

    #[error("ZK proof verification failed: {0}")]
    Verification(String),

    #[error("parameter / key data provider error: {0}")]
    DataProvider(String),

    #[error("async runtime error: {0}")]
    Runtime(#[from] std::io::Error),
}
