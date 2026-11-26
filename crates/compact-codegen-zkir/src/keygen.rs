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

//! Pipelined, deduplicated, bounded-concurrency Halo2 key generation for ZKIR circuits.
//!
//! Architecture:
//! 1. **Parallel model analysis (`rayon`)**: Compute `(k, rows)` for every circuit up front.
//! 2. **Deduplicated SRS prefetch (one short-lived `tokio` runtime)**: Collect the unique `k`
//!    values, fetch/load each KZG SRS `ParamsProver` (`Arc<ParamsKZG<Bls12>>`) once into a
//!    [`CachedParamsProvider`], then drop the `tokio` runtime completely before keygen starts.
//! 3. **LPT-scheduled bounded-concurrency keygen (`std::thread::scope`)**: Schedule circuits
//!    largest `(k, rows)` first across a bounded worker count so single-threaded keygen/serialization/
//!    I/O overlaps across circuits while Halo2's inner FFTs/MSMs share the single global Rayon pool
//!    cleanly, polling `IrSource::keygen` synchronously with `Waker::noop()` (zero Tokio executor).

use std::collections::{BTreeSet, HashMap};
use std::future::Future;
use std::io;
use std::pin::pin;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll, Waker};

use midnight_base_crypto::data_provider::{FetchMode, MidnightDataProvider, OutputMode};
use midnight_serialize::tagged_serialize;
use midnight_transient_crypto::proofs::{ParamsProver, ParamsProverProvider, Zkir};
use midnight_zkir::IrSource;
use sha2::{Digest, Sha256};

use crate::{CircuitModelSummary, CompiledKeys, ZkirError};

/// Thread-safe, zero-copy cache of KZG prover parameters (`Arc<ParamsKZG<Bls12>>`) keyed by `k`.
#[derive(Clone, Default)]
pub struct CachedParamsProvider {
    params: Arc<HashMap<u8, ParamsProver>>,
}

impl CachedParamsProvider {
    pub fn from_map(map: HashMap<u8, ParamsProver>) -> Self {
        Self {
            params: Arc::new(map),
        }
    }

    pub fn len(&self) -> usize {
        self.params.len()
    }

    pub fn is_empty(&self) -> bool {
        self.params.is_empty()
    }

    pub fn contains_k(&self, k: u8) -> bool {
        self.params.contains_key(&k)
    }
}

impl ParamsProverProvider for CachedParamsProvider {
    async fn get_params(&self, k: u8) -> io::Result<ParamsProver> {
        self.params.get(&k).cloned().ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::NotFound,
                format!("prefetched KZG parameters missing for k={k}"),
            )
        })
    }
}

/// Prefetch and deserialize KZG SRS parameters once per unique `k` using a single short-lived
/// `current_thread` Tokio runtime and a single [`MidnightDataProvider`].
///
/// The Tokio runtime is dropped before returning so subsequent CPU-bound Halo2 keygen runs with
/// zero async executor overhead.
pub fn prefetch_params(
    ks: impl IntoIterator<Item = u8>,
) -> Result<CachedParamsProvider, ZkirError> {
    let unique_ks: BTreeSet<u8> = ks.into_iter().collect();
    if unique_ks.is_empty() {
        return Ok(CachedParamsProvider::default());
    }

    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .map_err(ZkirError::Runtime)?;

    let map = rt.block_on(async {
        let provider = MidnightDataProvider::new(FetchMode::OnDemand, OutputMode::Log, vec![])
            .map_err(|e| ZkirError::DataProvider(e.to_string()))?;

        let mut loaded = HashMap::with_capacity(unique_ks.len());
        for k in unique_ks {
            let params = provider
                .get_params(k)
                .await
                .map_err(|e| ZkirError::DataProvider(format!("k={k}: {e}")))?;
            loaded.insert(k, params);
        }
        Ok::<_, ZkirError>(loaded)
    })?;

    drop(rt);
    Ok(CachedParamsProvider::from_map(map))
}

/// Poll a future known to be immediately ready (no async I/O suspension) without a Tokio executor.
pub(crate) fn poll_ready_now<F: Future>(fut: F) -> Result<F::Output, ZkirError> {
    let waker = Waker::noop();
    let mut cx = Context::from_waker(waker);
    let mut pinned = pin!(fut);
    match pinned.as_mut().poll(&mut cx) {
        Poll::Ready(out) => Ok(out),
        Poll::Pending => Err(ZkirError::Keygen(
            "unexpected async suspension during cached-params keygen".to_owned(),
        )),
    }
}

/// Compile proving and verifier keys synchronously using already-prefetched [`CachedParamsProvider`].
pub fn compile_keys_with_cached_params(
    ir: &IrSource,
    model: CircuitModelSummary,
    params: &CachedParamsProvider,
) -> Result<CompiledKeys, ZkirError> {
    let (pk, vk) =
        poll_ready_now(ir.keygen(params))?.map_err(|e| ZkirError::Keygen(e.to_string()))?;

    let mut prover_key = Vec::new();
    tagged_serialize(&pk, &mut prover_key)
        .map_err(|e| ZkirError::SerializeProverKey(e.to_string()))?;

    let mut verifier_key = Vec::new();
    tagged_serialize(&vk, &mut verifier_key)
        .map_err(|e| ZkirError::SerializeVerifierKey(e.to_string()))?;

    let verifier_key_sha256 = hex::encode(Sha256::digest(&verifier_key));

    Ok(CompiledKeys {
        prover_key,
        verifier_key,
        verifier_key_sha256,
        k: model.k,
        rows: model.rows,
    })
}

/// Default bounded concurrency for outer Halo2 keygen workers.
///
/// Because Halo2's `setup_vk`/`setup_pk` internally parallelize FFTs and MSMs across the global
/// Rayon pool, bounding outer concurrency to `(cpus / 2).clamp(1, 4)` overlaps single-threaded
/// circuit assembly, serialization, and disk I/O without thrashing CPU caches or spiking RAM.
pub fn default_keygen_jobs(circuit_count: usize) -> usize {
    if circuit_count <= 1 {
        return 1;
    }
    let cpus = std::thread::available_parallelism()
        .map(usize::from)
        .unwrap_or(1);
    let cap = (cpus / 2).clamp(1, 4);
    circuit_count.min(cap).max(1)
}

/// Longest-Processing-Time (LPT) schedule: sort descending by `(k, rows)` so the heaviest
/// circuits start first and do not straggle at the tail of a parallel batch.
pub fn schedule_lpt<T>(mut items: Vec<T>, key: impl Fn(&T) -> (u8, usize)) -> Vec<T> {
    items.sort_by_key(|a| std::cmp::Reverse(key(a)));
    items
}

/// Execute `f` over `items` using at most `jobs` OS worker threads via `std::thread::scope`,
/// short-circuiting remaining items on the first error.
///
/// When `jobs <= 1` or `items.len() <= 1`, executes directly on the calling thread with zero
/// thread-spawning overhead.
pub fn run_bounded_parallel<Item, Out, E, F>(
    items: Vec<Item>,
    jobs: usize,
    f: F,
) -> Result<Vec<Out>, E>
where
    Item: Send + Sync,
    Out: Send,
    E: Send,
    F: Fn(&Item, usize) -> Result<Out, E> + Sync,
{
    let total = items.len();
    if total == 0 {
        return Ok(Vec::new());
    }
    let worker_count = jobs.max(1).min(total);
    if worker_count == 1 {
        let mut results = Vec::with_capacity(total);
        for (idx, item) in items.iter().enumerate() {
            results.push(f(item, idx)?);
        }
        return Ok(results);
    }

    let next_idx = AtomicUsize::new(0);
    let cancelled = AtomicBool::new(false);
    let first_err: Mutex<Option<E>> = Mutex::new(None);
    let slots: Vec<Mutex<Option<Out>>> = (0..total).map(|_| Mutex::new(None)).collect();

    std::thread::scope(|s| {
        for _ in 0..worker_count {
            s.spawn(|| {
                while !cancelled.load(Ordering::Acquire) {
                    let idx = next_idx.fetch_add(1, Ordering::Relaxed);
                    if idx >= total {
                        break;
                    }
                    match f(&items[idx], idx) {
                        Ok(val) => {
                            *slots[idx].lock().unwrap() = Some(val);
                        }
                        Err(err) => {
                            cancelled.store(true, Ordering::Release);
                            let mut guard = first_err.lock().unwrap();
                            if guard.is_none() {
                                *guard = Some(err);
                            }
                            break;
                        }
                    }
                }
            });
        }
    });

    if let Some(err) = first_err.into_inner().unwrap() {
        return Err(err);
    }

    let mut out = Vec::with_capacity(total);
    for slot in slots {
        if let Some(val) = slot.into_inner().unwrap() {
            out.push(val);
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::time::Duration;

    use super::*;

    #[test]
    fn schedule_lpt_orders_largest_k_and_rows_first() {
        let items = vec![
            ("small", 10u8, 500usize),
            ("huge", 15, 20_000),
            ("mid_b", 12, 3_000),
            ("mid_a", 12, 3_500),
        ];
        let ordered = schedule_lpt(items, |x| (x.1, x.2));
        let names: Vec<_> = ordered.into_iter().map(|x| x.0).collect();
        assert_eq!(names, vec!["huge", "mid_a", "mid_b", "small"]);
    }

    #[test]
    fn default_keygen_jobs_bounds_concurrency() {
        assert_eq!(default_keygen_jobs(0), 1);
        assert_eq!(default_keygen_jobs(1), 1);
        let j = default_keygen_jobs(16);
        assert!((1..=4).contains(&j), "unexpected default jobs: {j}");
    }

    #[test]
    fn prefetch_params_empty_skips_runtime() {
        let cache = prefetch_params(std::iter::empty()).unwrap();
        assert!(cache.is_empty());
        assert!(!cache.contains_k(10));
    }

    #[test]
    fn poll_ready_now_handles_ready_and_missing_cache_entry() {
        let cache = CachedParamsProvider::default();
        let res = poll_ready_now(cache.get_params(12)).unwrap();
        assert!(res.is_err());
        assert_eq!(res.err().unwrap().kind(), io::ErrorKind::NotFound);

        let ok = poll_ready_now(async { 42usize }).unwrap();
        assert_eq!(ok, 42);
    }

    #[test]
    fn run_bounded_parallel_respects_job_limit_and_preserves_order() {
        let items: Vec<usize> = (0..12).collect();
        let in_flight = AtomicUsize::new(0);
        let max_seen = AtomicUsize::new(0);

        let results = run_bounded_parallel(items, 3, |&item, _| -> Result<usize, ()> {
            let cur = in_flight.fetch_add(1, Ordering::SeqCst) + 1;
            max_seen.fetch_max(cur, Ordering::SeqCst);
            std::thread::sleep(Duration::from_millis(5));
            in_flight.fetch_sub(1, Ordering::SeqCst);
            Ok(item * 10)
        })
        .unwrap();

        assert_eq!(results, (0..12).map(|x| x * 10).collect::<Vec<_>>());
        assert!(
            max_seen.load(Ordering::SeqCst) <= 3,
            "exceeded job bound: {}",
            max_seen.load(Ordering::SeqCst)
        );
    }

    #[test]
    fn run_bounded_parallel_short_circuits_on_error() {
        let items: Vec<usize> = (0..10).collect();
        let res = run_bounded_parallel(items, 2, |&item, _| -> Result<usize, &'static str> {
            if item == 2 { Err("boom") } else { Ok(item) }
        });
        assert_eq!(res, Err("boom"));
    }
}
