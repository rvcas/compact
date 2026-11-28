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

//! Impact VM execution and on-chain `StateValue` helpers powered by `midnight-onchain-runtime`.

use midnight_base_crypto::cost_model::RunningCost;
use midnight_base_crypto::fab::AlignedValue;
use midnight_base_crypto::hash::HashOutput;
use midnight_coin_structure::contract::ContractAddress;
use midnight_onchain_runtime::context::QueryContext;
use midnight_onchain_runtime::cost_model::{CostModel, INITIAL_COST_MODEL};
use midnight_onchain_runtime::ops::Op;
use midnight_onchain_runtime::result_mode::{GatherEvent, ResultModeGather, ResultModeVerify};
use midnight_onchain_runtime::state::{ChargedState, StateValue};
use midnight_serialize::{tagged_deserialize, tagged_serialize};
use midnight_storage::arena::Sp;
use midnight_storage::db::InMemoryDB;

use crate::MidnightError;

/// Default in-memory `StateValue` alias.
pub type MemStateValue = StateValue<InMemoryDB>;

/// Default in-memory `QueryContext` alias.
pub type MemQueryContext = QueryContext<InMemoryDB>;

/// Default in-memory gather-mode Impact VM op.
pub type GatherOp = Op<ResultModeGather, InMemoryDB>;

/// Default in-memory verify-mode Impact VM op.
pub type VerifyOp = Op<ResultModeVerify, InMemoryDB>;

/// Gas cost summary returned from Impact VM execution.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GasSummary {
    pub read_time_ps: u64,
    pub compute_time_ps: u64,
    pub bytes_written: u64,
    pub bytes_deleted: u64,
}

impl From<RunningCost> for GasSummary {
    fn from(cost: RunningCost) -> Self {
        Self {
            read_time_ps: cost.read_time.into_picoseconds(),
            compute_time_ps: cost.compute_time.into_picoseconds(),
            bytes_written: cost.bytes_written,
            bytes_deleted: cost.bytes_deleted,
        }
    }
}

/// Output of running a sequence of gather-mode Impact VM ops against a contract state.
#[derive(Debug, Clone)]
pub struct VmQueryOutput {
    /// Updated contract `StateValue` after applying the program.
    pub state: MemStateValue,
    /// Tagged-serialized bytes of the updated `StateValue`.
    pub state_bytes: Vec<u8>,
    /// Read values gathered by `Popeq` operations (in execution order).
    pub reads: Vec<AlignedValue>,
    /// Verify-mode operations with concrete `Popeq { result }` values filled in.
    pub verified_ops: Vec<VerifyOp>,
    /// JSON representation of `verified_ops`.
    pub verified_ops_json: String,
    /// Measured gas cost under the cost model.
    pub gas: GasSummary,
}

/// Return Midnight's canonical initial VM `CostModel`.
pub fn initial_cost_model() -> CostModel {
    INITIAL_COST_MODEL
}

/// Construct an empty `StateValue::Null`.
pub fn empty_state_value() -> MemStateValue {
    StateValue::Null
}

/// Construct a fixed-length `StateValue::Array` (e.g., top-level contract ledger fields).
pub fn state_value_array(items: Vec<MemStateValue>) -> MemStateValue {
    StateValue::Array(items.into())
}

/// Construct a `StateValue::Cell` holding an `AlignedValue`.
pub fn state_value_cell(val: AlignedValue) -> MemStateValue {
    StateValue::Cell(Sp::new(val))
}

/// Construct a `Counter` cell initialized to `value`.
pub fn state_value_counter(value: u64) -> MemStateValue {
    StateValue::Cell(Sp::new(value.into()))
}

/// Read a `u64` counter stored at slot `index` of a top-level `StateValue::Array`
/// (or directly from a `StateValue::Cell` when `index == 0` and root is a cell).
pub fn read_counter_at(state: &MemStateValue, index: usize) -> Result<u64, MidnightError> {
    let cell_val = match state {
        StateValue::Array(arr) => arr.get(index).ok_or_else(|| {
            MidnightError::InvalidState(format!(
                "ledger slot {index} out of bounds (array len {})",
                arr.len()
            ))
        })?,
        StateValue::Cell(_) if index == 0 => state,
        other => {
            return Err(MidnightError::InvalidState(format!(
                "expected Array or Cell at slot {index}, got {other:?}"
            )));
        }
    };
    match cell_val {
        StateValue::Cell(val) => u64::try_from(&*val.value).map_err(|e| {
            MidnightError::InvalidState(format!(
                "failed to decode u64 counter at slot {index}: {e}"
            ))
        }),
        StateValue::Null => Ok(0),
        other => Err(MidnightError::InvalidState(format!(
            "expected Cell or Null for counter at slot {index}, got {other:?}"
        ))),
    }
}

/// Tagged-serialize a `StateValue` into canonical Midnight binary bytes.
pub fn serialize_state_value(state: &MemStateValue) -> Result<Vec<u8>, MidnightError> {
    let mut buf = Vec::new();
    tagged_serialize(state, &mut buf).map_err(|e| MidnightError::Serialization(e.to_string()))?;
    Ok(buf)
}

/// Tagged-deserialize a `StateValue` from canonical Midnight binary bytes.
pub fn deserialize_state_value(bytes: &[u8]) -> Result<MemStateValue, MidnightError> {
    tagged_deserialize(&mut &bytes[..]).map_err(|e| MidnightError::Serialization(e.to_string()))
}

/// Execute gather-mode Impact VM ops against `state` at `address`, returning the new state,
/// gathered reads, materialized verify-mode ops, and gas cost.
pub fn query_gather(
    state: &MemStateValue,
    address: [u8; 32],
    ops: &[GatherOp],
) -> Result<VmQueryOutput, MidnightError> {
    let qc = QueryContext::new(
        ChargedState::new(state.clone()),
        ContractAddress(HashOutput(address)),
    );
    let cost_model = initial_cost_model();
    let res = qc
        .query(ops, None, &cost_model)
        .map_err(|e| MidnightError::VmExecution(format!("{e:?}")))?;

    let reads: Vec<AlignedValue> = res
        .events
        .into_iter()
        .filter_map(|ev| match ev {
            GatherEvent::Read(val) => Some(val),
            GatherEvent::Log(_) => None,
        })
        .collect();

    let verified_ops = materialize_verified_ops(ops, &reads)?;
    let verified_ops_json = serde_json::to_string(&verified_ops)?;
    let new_state = (*res.context.state.get()).clone();
    let state_bytes = serialize_state_value(&new_state)?;

    Ok(VmQueryOutput {
        state: new_state,
        state_bytes,
        reads,
        verified_ops,
        verified_ops_json,
        gas: res.gas_cost.into(),
    })
}

/// Execute gather-mode Impact VM ops parsed from canonical JSON against tagged-serialized state bytes.
pub fn query_gather_json(
    state_bytes: &[u8],
    address: [u8; 32],
    ops_json: &str,
) -> Result<VmQueryOutput, MidnightError> {
    let state = deserialize_state_value(state_bytes)?;
    let ops: Vec<GatherOp> = serde_json::from_str(ops_json)?;
    query_gather(&state, address, &ops)
}

/// Convert gather-mode ops into verify-mode ops by substituting each `Popeq` with its gathered read.
pub fn materialize_verified_ops(
    ops: &[GatherOp],
    reads: &[AlignedValue],
) -> Result<Vec<VerifyOp>, MidnightError> {
    let mut read_iter = reads.iter();
    let mut out = Vec::with_capacity(ops.len());
    for op in ops {
        let vop = match op {
            Op::Noop { n } => Op::Noop { n: *n },
            Op::Lt => Op::Lt,
            Op::Eq => Op::Eq,
            Op::Type => Op::Type,
            Op::Size => Op::Size,
            Op::New => Op::New,
            Op::And => Op::And,
            Op::Or => Op::Or,
            Op::Neg => Op::Neg,
            Op::Log => Op::Log,
            Op::Root => Op::Root,
            Op::Pop => Op::Pop,
            Op::Popeq { cached, .. } => {
                let result = read_iter.next().cloned().ok_or_else(|| {
                    MidnightError::VmExecution(
                        "missing gathered read result for Popeq operation".into(),
                    )
                })?;
                Op::Popeq {
                    cached: *cached,
                    result,
                }
            }
            Op::Addi { immediate } => Op::Addi {
                immediate: *immediate,
            },
            Op::Subi { immediate } => Op::Subi {
                immediate: *immediate,
            },
            Op::Push { storage, value } => Op::Push {
                storage: *storage,
                value: value.clone(),
            },
            Op::Branch { skip } => Op::Branch { skip: *skip },
            Op::Jmp { skip } => Op::Jmp { skip: *skip },
            Op::Add => Op::Add,
            Op::Sub => Op::Sub,
            Op::Concat { cached, n } => Op::Concat {
                cached: *cached,
                n: *n,
            },
            Op::Member => Op::Member,
            Op::Rem { cached } => Op::Rem { cached: *cached },
            Op::Dup { n } => Op::Dup { n: *n },
            Op::Swap { n } => Op::Swap { n: *n },
            Op::Idx {
                cached,
                push_path,
                path,
            } => Op::Idx {
                cached: *cached,
                push_path: *push_path,
                path: path.clone(),
            },
            Op::Ins { cached, n } => Op::Ins {
                cached: *cached,
                n: *n,
            },
            Op::Ckpt => Op::Ckpt,
            other => {
                return Err(MidnightError::VmExecution(format!(
                    "unsupported Impact VM op variant: {other:?}"
                )));
            }
        };
        out.push(vop);
    }
    Ok(out)
}
