//! SSA circuit optimization passes for [`ProofCircuit`].
//!
//! Mirrors upstream `compiler/circuit-passes/optimize-circuit.ss` and `discard-useless-code.ss`:
//! - Copy & constant propagation (with canonical `Imm`/`ImmBytes` normalization)
//! - Native-field constant folding & algebraic/boolean simplifications
//! - Nested `CondSelect` branch specialization & inverted-selector flipping
//! - Redundant constraint & assert elimination (`ConstrainToBoolean`, `ConstrainBits`,
//!   `ConstrainEq`, `Assert`, and statically dead `guard == 0` ops)
//! - Common Subexpression Elimination (CSE) for pure single- and multi-output instructions
//!   (including commutative canonicalization for `Add`, `Mul`, and `TestEq`)
//! - Sound backward Dead-Code Elimination (DCE) preserving all side-effecting and
//!   range/curve/invertibility-constraining instructions
//! - Dense `CircuitVar` compaction

use std::collections::{HashMap, HashSet};

use crate::{
    AlignmentAtom, CircuitInstr, CircuitProgram, CircuitVal, CircuitVar, ImpactStateValue,
    ImpactVmOp, PathSegment, ProofCircuit, WireType,
};

const MAX_OPT_ITERATIONS: usize = 8;

/// Optimize every proof circuit in `program`.
pub fn optimize_program(program: &mut CircuitProgram) {
    for circuit in &mut program.circuits {
        optimize_circuit(circuit);
    }
}

/// Run SSA optimization passes to a fixed point and compact live variables densely.
pub fn optimize_circuit(circuit: &mut ProofCircuit) {
    for _ in 0..MAX_OPT_ITERATIONS {
        let before_len = circuit.instructions.len();
        let (changed_fwd, droppable_lt) = forward_pass(circuit);
        let changed_bwd = backward_dce(circuit, &droppable_lt);
        if !changed_fwd && !changed_bwd && circuit.instructions.len() == before_len {
            break;
        }
    }
    compact_vars(circuit);
}

/// Canonical, hashable, ordered representation of a [`CircuitVal`] for CSE and deduplication.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum CanonVal {
    Imm(i128),
    ImmBytes(Vec<u8>),
    Var(u32),
}

impl CanonVal {
    fn from_val(val: &CircuitVal) -> Self {
        match normalize_val(val.clone()) {
            CircuitVal::Imm(n) => Self::Imm(n),
            CircuitVal::ImmBytes(b) => Self::ImmBytes(b),
            CircuitVal::Var(v) => Self::Var(v.id),
        }
    }
}

fn order_pair(a: CanonVal, b: CanonVal) -> (CanonVal, CanonVal) {
    if a <= b { (a, b) } else { (b, a) }
}

/// Normalize `ImmBytes` by stripping trailing zero bytes and converting values that fit in
/// `0..=i128::MAX` to `CircuitVal::Imm` so equivalent constants compare equal.
fn normalize_val(val: CircuitVal) -> CircuitVal {
    match val {
        CircuitVal::ImmBytes(mut bytes) => {
            while bytes.last() == Some(&0) && bytes.len() > 1 {
                bytes.pop();
            }
            if bytes.is_empty() || (bytes.len() == 1 && bytes[0] == 0) {
                return CircuitVal::Imm(0);
            }
            if bytes.len() < 16 || (bytes.len() == 16 && bytes[15] < 0x80) {
                let mut buf = [0u8; 16];
                buf[..bytes.len()].copy_from_slice(&bytes);
                return CircuitVal::Imm(i128::from_le_bytes(buf));
            }
            CircuitVal::ImmBytes(bytes)
        }
        other => other,
    }
}

/// Minimum number of bits required to represent a non-negative constant, or `None` if negative/var.
fn const_bit_width(val: &CircuitVal) -> Option<u32> {
    match val {
        CircuitVal::Imm(n) if *n >= 0 => {
            let u = *n as u128;
            Some(u128::BITS - u.leading_zeros())
        }
        CircuitVal::ImmBytes(bytes) => {
            let last_nz = bytes.iter().rposition(|&b| b != 0);
            match last_nz {
                None => Some(0),
                Some(idx) => {
                    let top = bytes[idx];
                    Some((idx as u32) * 8 + (u8::BITS - top.leading_zeros()))
                }
            }
        }
        _ => None,
    }
}

fn const_fits_in_bits(val: &CircuitVal, bits: u32) -> bool {
    const_bit_width(val).is_some_and(|w| w <= bits)
}

fn val_proven_within_bits(val: &CircuitVal, bits: u32, known_bits: &[Option<u32>]) -> bool {
    match val {
        CircuitVal::Var(v) => known_bits
            .get(v.id as usize)
            .and_then(|&b| b)
            .is_some_and(|b| b <= bits),
        _ => const_fits_in_bits(val, bits),
    }
}

fn is_const_zero(val: &CircuitVal) -> bool {
    matches!(val, CircuitVal::Imm(0))
}

fn is_const_one(val: &CircuitVal) -> bool {
    matches!(val, CircuitVal::Imm(1))
}

fn is_const_bool(val: &CircuitVal) -> bool {
    matches!(val, CircuitVal::Imm(0 | 1))
}

fn is_const_native(val: &CircuitVal) -> bool {
    matches!(val, CircuitVal::Imm(_) | CircuitVal::ImmBytes(_))
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum CseKey {
    Add(CanonVal, CanonVal),
    Mul(CanonVal, CanonVal),
    Neg(CanonVal),
    Not(CanonVal),
    TestEq(CanonVal, CanonVal),
    LessThan(CanonVal, CanonVal, u32),
    CondSelect(CanonVal, CanonVal, CanonVal),
    PersistentHash(Vec<AlignmentAtomKey>, Vec<CanonVal>),
    Keccak256(Vec<AlignmentAtomKey>, Vec<CanonVal>),
    Sha512(Vec<AlignmentAtomKey>, Vec<CanonVal>),
    TransientHash(Vec<CanonVal>),
    HashToCurve(Vec<CanonVal>),
    EcMul(CanonVal, CanonVal),
    EcMulGenerator(CanonVal),
    BytesFromNatives(Vec<CanonVal>, u32),
    ToBytes(CanonVal),
    Slice(u32, u32, u32),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum CseMultiKey {
    Encode(CanonVal, usize),
    DivModPowerOfTwo(CanonVal, u32),
    IntoCoordinates(CanonVal),
    BytesIntoNatives(u32, usize),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum AlignmentAtomKey {
    Bytes(u32),
    Field,
    Compress,
}

impl From<&AlignmentAtom> for AlignmentAtomKey {
    fn from(atom: &AlignmentAtom) -> Self {
        match atom {
            AlignmentAtom::Bytes(n) => Self::Bytes(*n),
            AlignmentAtom::Field => Self::Field,
            AlignmentAtom::Compress => Self::Compress,
        }
    }
}

fn alignment_key(alignment: &[AlignmentAtom]) -> Vec<AlignmentAtomKey> {
    alignment.iter().map(AlignmentAtomKey::from).collect()
}

/// Collect variables that are used in `CircuitVar`-only operand positions (`BytesIntoNatives`,
/// `FromBytes`, `Slice`) so copy propagation never substitutes an immediate into them.
fn collect_var_only_uses(instructions: &[CircuitInstr], num_vars: usize) -> Vec<bool> {
    let mut var_only = vec![false; num_vars];
    for instr in instructions {
        match instr {
            CircuitInstr::BytesIntoNatives { bytes, .. }
            | CircuitInstr::FromBytes { bytes, .. }
            | CircuitInstr::Slice { bytes, .. }
                if (bytes.id as usize) < var_only.len() =>
            {
                var_only[bytes.id as usize] = true;
            }
            _ => {}
        }
    }
    var_only
}

struct ForwardState {
    var_subst: Vec<Option<CircuitVal>>,
    var_types: Vec<WireType>,
    var_only_uses: Vec<bool>,
    known_bool: Vec<bool>,
    known_bits: Vec<Option<u32>>,
    known_not: HashMap<CircuitVar, CircuitVal>,
    known_neg: HashMap<CircuitVar, CircuitVal>,
    known_cond_select: HashMap<CircuitVar, (CircuitVal, CircuitVal, CircuitVal)>,
    known_and_factors: HashMap<CircuitVar, HashSet<CanonVal>>,
    known_or_terms: HashMap<CircuitVar, HashSet<CanonVal>>,
    cse: HashMap<CseKey, CircuitVar>,
    cse_multi: HashMap<CseMultiKey, Vec<CircuitVar>>,
    seen_asserts: HashSet<CanonVal>,
    seen_constrain_eq: HashSet<(CanonVal, CanonVal)>,
    changed: bool,
}

impl ForwardState {
    fn new(circuit: &ProofCircuit) -> Self {
        let n = circuit.var_names.len();
        let mut var_types = vec![WireType::Native; n];
        for &(var, wt) in &circuit.inputs {
            if (var.id as usize) < n {
                var_types[var.id as usize] = wt;
            }
        }
        let var_only_uses = collect_var_only_uses(&circuit.instructions, n);
        Self {
            var_subst: vec![None; n],
            var_types,
            var_only_uses,
            known_bool: vec![false; n],
            known_bits: vec![None; n],
            known_not: HashMap::new(),
            known_neg: HashMap::new(),
            known_cond_select: HashMap::new(),
            known_and_factors: HashMap::new(),
            known_or_terms: HashMap::new(),
            cse: HashMap::new(),
            cse_multi: HashMap::new(),
            seen_asserts: HashSet::new(),
            seen_constrain_eq: HashSet::new(),
            changed: false,
        }
    }

    fn resolve(&self, val: &CircuitVal) -> CircuitVal {
        let mut cur = normalize_val(val.clone());
        let mut hops = 0;
        while let CircuitVal::Var(v) = cur {
            if hops > 64 {
                break;
            }
            match self.var_subst.get(v.id as usize).and_then(|s| s.as_ref()) {
                Some(next) => {
                    cur = next.clone();
                    hops += 1;
                }
                None => break,
            }
        }
        cur
    }

    fn resolve_var(&self, var: CircuitVar) -> CircuitVar {
        let mut cur = var;
        let mut hops = 0;
        while hops <= 64 {
            match self.var_subst.get(cur.id as usize).and_then(|s| s.as_ref()) {
                Some(CircuitVal::Var(next)) => {
                    cur = *next;
                    hops += 1;
                }
                _ => break,
            }
        }
        cur
    }

    fn resolve_vec(&self, vals: &[CircuitVal]) -> Vec<CircuitVal> {
        vals.iter().map(|v| self.resolve(v)).collect()
    }

    fn wire_type(&self, val: &CircuitVal) -> WireType {
        match val {
            CircuitVal::Var(v) => self
                .var_types
                .get(v.id as usize)
                .copied()
                .unwrap_or(WireType::Native),
            CircuitVal::Imm(_) | CircuitVal::ImmBytes(_) => WireType::Native,
        }
    }

    fn is_native(&self, val: &CircuitVal) -> bool {
        self.wire_type(val) == WireType::Native
    }

    fn is_known_bool(&self, val: &CircuitVal) -> bool {
        match val {
            CircuitVal::Imm(0 | 1) => true,
            CircuitVal::Var(v) => self.known_bool.get(v.id as usize).copied().unwrap_or(false),
            _ => false,
        }
    }

    fn set_type(&mut self, var: CircuitVar, wt: WireType) {
        if (var.id as usize) < self.var_types.len() {
            self.var_types[var.id as usize] = wt;
        }
    }

    fn mark_bool(&mut self, var: CircuitVar) {
        if (var.id as usize) < self.known_bool.len() {
            self.known_bool[var.id as usize] = true;
        }
        self.record_bits(var, 1);
    }

    fn record_bits(&mut self, var: CircuitVar, bits: u32) {
        if let Some(slot) = self.known_bits.get_mut(var.id as usize) {
            *slot = Some(slot.map_or(bits, |prev| prev.min(bits)));
        }
    }

    fn can_subst(&self, output: CircuitVar, replacement: &CircuitVal) -> bool {
        if matches!(replacement, CircuitVal::Var(_)) {
            return true;
        }
        !self
            .var_only_uses
            .get(output.id as usize)
            .copied()
            .unwrap_or(false)
    }

    fn subst(&mut self, output: CircuitVar, replacement: CircuitVal) {
        let rep = normalize_val(replacement);
        if (output.id as usize) < self.var_subst.len() {
            self.var_subst[output.id as usize] = Some(rep);
        }
        self.changed = true;
    }

    fn resolve_impact_state(&self, sv: &ImpactStateValue) -> ImpactStateValue {
        match sv {
            ImpactStateValue::Null => ImpactStateValue::Null,
            ImpactStateValue::EmptyMap => ImpactStateValue::EmptyMap,
            ImpactStateValue::MerkleTree { depth } => {
                ImpactStateValue::MerkleTree { depth: *depth }
            }
            ImpactStateValue::Cell { alignment, values } => ImpactStateValue::Cell {
                alignment: alignment.clone(),
                values: self.resolve_vec(values),
            },
            ImpactStateValue::Array(elems) => ImpactStateValue::Array(
                elems.iter().map(|e| self.resolve_impact_state(e)).collect(),
            ),
        }
    }

    fn resolve_impact_op(&self, op: &ImpactVmOp) -> ImpactVmOp {
        match op {
            ImpactVmOp::Idx {
                cached,
                push_path,
                path,
            } => ImpactVmOp::Idx {
                cached: *cached,
                push_path: *push_path,
                path: path
                    .iter()
                    .map(|seg| match seg {
                        PathSegment::Static(s) => PathSegment::Static(*s),
                        PathSegment::Stack => PathSegment::Stack,
                        PathSegment::Dynamic { alignment, values } => PathSegment::Dynamic {
                            alignment: alignment.clone(),
                            values: self.resolve_vec(values),
                        },
                    })
                    .collect(),
            },
            ImpactVmOp::Popeq {
                cached,
                alignment,
                results,
            } => ImpactVmOp::Popeq {
                cached: *cached,
                alignment: alignment.clone(),
                results: self.resolve_vec(results),
            },
            ImpactVmOp::Push { storage, value } => ImpactVmOp::Push {
                storage: *storage,
                value: self.resolve_impact_state(value),
            },
            ImpactVmOp::Addi { immediate } => ImpactVmOp::Addi {
                immediate: self.resolve(immediate),
            },
            ImpactVmOp::Subi { immediate } => ImpactVmOp::Subi {
                immediate: self.resolve(immediate),
            },
            other => other.clone(),
        }
    }
}

fn forward_pass(circuit: &mut ProofCircuit) -> (bool, HashSet<CircuitVar>) {
    let mut st = ForwardState::new(circuit);
    let mut droppable_lt: HashSet<CircuitVar> = HashSet::new();
    let old_instrs = std::mem::take(&mut circuit.instructions);
    let mut out = Vec::with_capacity(old_instrs.len());

    for instr in old_instrs {
        match instr {
            CircuitInstr::PublicInput {
                guard,
                val_t,
                output,
            } => {
                st.set_type(output, val_t);
                let mut g = guard.as_ref().map(|x| st.resolve(x));
                if matches!(g, Some(CircuitVal::Imm(1))) {
                    g = None;
                    st.changed = true;
                }
                if matches!(g, Some(CircuitVal::Imm(0)))
                    && val_t == WireType::Native
                    && st.can_subst(output, &CircuitVal::Imm(0))
                {
                    st.subst(output, CircuitVal::Imm(0));
                    continue;
                }
                out.push(CircuitInstr::PublicInput {
                    guard: g,
                    val_t,
                    output,
                });
            }
            CircuitInstr::PrivateInput {
                guard,
                val_t,
                output,
            } => {
                st.set_type(output, val_t);
                let mut g = guard.as_ref().map(|x| st.resolve(x));
                if matches!(g, Some(CircuitVal::Imm(1))) {
                    g = None;
                    st.changed = true;
                }
                if matches!(g, Some(CircuitVal::Imm(0)))
                    && val_t == WireType::Native
                    && st.can_subst(output, &CircuitVal::Imm(0))
                {
                    st.subst(output, CircuitVal::Imm(0));
                    continue;
                }
                out.push(CircuitInstr::PrivateInput {
                    guard: g,
                    val_t,
                    output,
                });
            }
            CircuitInstr::Copy { val, output } => {
                let r = st.resolve(&val);
                st.set_type(output, st.wire_type(&r));
                if st.can_subst(output, &r) {
                    st.subst(output, r);
                    continue;
                }
                out.push(CircuitInstr::Copy { val: r, output });
            }
            CircuitInstr::ConstrainToBoolean { val } => {
                let r = st.resolve(&val);
                if is_const_bool(&r) {
                    st.changed = true;
                    continue;
                }
                if let CircuitVal::Var(v) = r {
                    if st.is_known_bool(&r) {
                        st.changed = true;
                        continue;
                    }
                    st.mark_bool(v);
                }
                out.push(CircuitInstr::ConstrainToBoolean { val: r });
            }
            CircuitInstr::ConstrainBits { val, bits } => {
                let r = st.resolve(&val);
                if const_fits_in_bits(&r, bits) {
                    st.changed = true;
                    continue;
                }
                if let CircuitVal::Var(v) = r {
                    if st
                        .known_bits
                        .get(v.id as usize)
                        .and_then(|&b| b)
                        .is_some_and(|b| b <= bits)
                    {
                        st.changed = true;
                        continue;
                    }
                    st.record_bits(v, bits);
                }
                out.push(CircuitInstr::ConstrainBits { val: r, bits });
            }
            CircuitInstr::ConstrainEq { a, b } => {
                let ra = st.resolve(&a);
                let rb = st.resolve(&b);
                let ca = CanonVal::from_val(&ra);
                let cb = CanonVal::from_val(&rb);
                if ca == cb {
                    st.changed = true;
                    continue;
                }
                let key = order_pair(ca, cb);
                if !st.seen_constrain_eq.insert(key) {
                    st.changed = true;
                    continue;
                }
                out.push(CircuitInstr::ConstrainEq { a: ra, b: rb });
            }
            CircuitInstr::Assert { cond } => {
                let r = st.resolve(&cond);
                if is_const_one(&r) {
                    st.changed = true;
                    continue;
                }
                let key = CanonVal::from_val(&r);
                if !st.seen_asserts.insert(key) {
                    st.changed = true;
                    continue;
                }
                out.push(CircuitInstr::Assert { cond: r });
            }
            CircuitInstr::Not { a, output } => {
                let ra = st.resolve(&a);
                st.set_type(output, WireType::Native);
                if is_const_zero(&ra) {
                    st.subst(output, CircuitVal::TRUE);
                    continue;
                }
                if is_const_one(&ra) {
                    st.subst(output, CircuitVal::FALSE);
                    continue;
                }
                if let CircuitVal::Var(v) = ra
                    && let Some(inner) = st.known_not.get(&v).cloned()
                    && st.is_known_bool(&inner)
                {
                    st.subst(output, inner);
                    continue;
                }
                let key = CseKey::Not(CanonVal::from_val(&ra));
                if let Some(&prev) = st.cse.get(&key) {
                    st.subst(output, CircuitVal::Var(prev));
                    continue;
                }
                st.cse.insert(key, output);
                st.mark_bool(output);
                st.known_not.insert(output, ra.clone());
                out.push(CircuitInstr::Not { a: ra, output });
            }
            CircuitInstr::Add { a, b, output } => {
                let ra = st.resolve(&a);
                let rb = st.resolve(&b);
                let wt = st.wire_type(&ra);
                st.set_type(output, wt);
                if wt == WireType::Native && st.is_native(&rb) {
                    if let (CircuitVal::Imm(x), CircuitVal::Imm(y)) = (&ra, &rb)
                        && let Some(sum) = x.checked_add(*y)
                    {
                        st.subst(output, CircuitVal::Imm(sum));
                        continue;
                    }
                    if is_const_zero(&ra) {
                        st.subst(output, rb);
                        continue;
                    }
                    if is_const_zero(&rb) {
                        st.subst(output, ra);
                        continue;
                    }
                    // x + (-x) == 0
                    if let CircuitVal::Var(va) = ra
                        && st.known_neg.get(&va).is_some_and(|inner| {
                            CanonVal::from_val(inner) == CanonVal::from_val(&rb)
                        })
                    {
                        st.subst(output, CircuitVal::Imm(0));
                        continue;
                    }
                    if let CircuitVal::Var(vb) = rb
                        && st.known_neg.get(&vb).is_some_and(|inner| {
                            CanonVal::from_val(inner) == CanonVal::from_val(&ra)
                        })
                    {
                        st.subst(output, CircuitVal::Imm(0));
                        continue;
                    }
                }
                let (ca, cb) = order_pair(CanonVal::from_val(&ra), CanonVal::from_val(&rb));
                let key = CseKey::Add(ca, cb);
                if let Some(&prev) = st.cse.get(&key) {
                    st.subst(output, CircuitVal::Var(prev));
                    continue;
                }
                st.cse.insert(key, output);
                out.push(CircuitInstr::Add {
                    a: ra,
                    b: rb,
                    output,
                });
            }
            CircuitInstr::Mul { a, b, output } => {
                let ra = st.resolve(&a);
                let rb = st.resolve(&b);
                let wt = st.wire_type(&ra);
                st.set_type(output, wt);
                if wt == WireType::Native && st.is_native(&rb) {
                    if let (CircuitVal::Imm(x), CircuitVal::Imm(y)) = (&ra, &rb)
                        && let Some(prod) = x.checked_mul(*y)
                    {
                        st.subst(output, CircuitVal::Imm(prod));
                        continue;
                    }
                    if is_const_zero(&ra) || is_const_zero(&rb) {
                        st.subst(output, CircuitVal::Imm(0));
                        continue;
                    }
                    if is_const_one(&ra) {
                        st.subst(output, rb);
                        continue;
                    }
                    if is_const_one(&rb) {
                        st.subst(output, ra);
                        continue;
                    }
                }
                let (ca, cb) = order_pair(CanonVal::from_val(&ra), CanonVal::from_val(&rb));
                let key = CseKey::Mul(ca, cb);
                if let Some(&prev) = st.cse.get(&key) {
                    st.subst(output, CircuitVal::Var(prev));
                    continue;
                }
                st.cse.insert(key, output);
                out.push(CircuitInstr::Mul {
                    a: ra,
                    b: rb,
                    output,
                });
            }
            CircuitInstr::Neg { a, output } => {
                let ra = st.resolve(&a);
                let wt = st.wire_type(&ra);
                st.set_type(output, wt);
                if wt == WireType::Native
                    && let CircuitVal::Imm(x) = ra
                    && let Some(neg) = x.checked_neg()
                {
                    st.subst(output, CircuitVal::Imm(neg));
                    continue;
                }
                if let CircuitVal::Var(v) = ra
                    && let Some(inner) = st.known_neg.get(&v).cloned()
                {
                    st.subst(output, inner);
                    continue;
                }
                let key = CseKey::Neg(CanonVal::from_val(&ra));
                if let Some(&prev) = st.cse.get(&key) {
                    st.subst(output, CircuitVal::Var(prev));
                    continue;
                }
                st.cse.insert(key, output);
                st.known_neg.insert(output, ra.clone());
                out.push(CircuitInstr::Neg { a: ra, output });
            }
            CircuitInstr::Inv { a, output } => {
                let ra = st.resolve(&a);
                let wt = st.wire_type(&ra);
                st.set_type(output, wt);
                // Keep Inv unconditionally because it constrains `a != 0`.
                out.push(CircuitInstr::Inv { a: ra, output });
            }
            CircuitInstr::TestEq { a, b, output } => {
                let ra = st.resolve(&a);
                let rb = st.resolve(&b);
                st.set_type(output, WireType::Native);
                let ca = CanonVal::from_val(&ra);
                let cb = CanonVal::from_val(&rb);
                if ca == cb {
                    st.subst(output, CircuitVal::TRUE);
                    continue;
                }
                if is_const_native(&ra) && is_const_native(&rb) {
                    // Canonicalized non-negative constants <= 31 bytes and signed i128 embed
                    // injectively into BLS12-381 Fr, so distinct CanonVals are unequal.
                    st.subst(output, CircuitVal::FALSE);
                    continue;
                }
                // Simplify `bool_var == 1` -> `bool_var`, `bool_var == 0` -> `Not(bool_var)`
                // (replaces an expensive field-inversion TestEq gadget with a free/linear Not).
                if st.is_known_bool(&ra) && is_const_one(&rb) {
                    st.subst(output, ra);
                    continue;
                }
                if st.is_known_bool(&rb) && is_const_one(&ra) {
                    st.subst(output, rb);
                    continue;
                }
                if st.is_known_bool(&ra) && is_const_zero(&rb) {
                    if let CircuitVal::Var(v) = ra
                        && let Some(inner) = st.known_not.get(&v).cloned()
                        && st.is_known_bool(&inner)
                    {
                        st.subst(output, inner);
                        continue;
                    }
                    let not_key = CseKey::Not(ca.clone());
                    if let Some(&prev) = st.cse.get(&not_key) {
                        st.subst(output, CircuitVal::Var(prev));
                        continue;
                    }
                    st.cse.insert(not_key, output);
                    st.mark_bool(output);
                    st.known_not.insert(output, ra.clone());
                    st.changed = true;
                    out.push(CircuitInstr::Not { a: ra, output });
                    continue;
                }
                if st.is_known_bool(&rb) && is_const_zero(&ra) {
                    if let CircuitVal::Var(v) = rb
                        && let Some(inner) = st.known_not.get(&v).cloned()
                        && st.is_known_bool(&inner)
                    {
                        st.subst(output, inner);
                        continue;
                    }
                    let not_key = CseKey::Not(cb.clone());
                    if let Some(&prev) = st.cse.get(&not_key) {
                        st.subst(output, CircuitVal::Var(prev));
                        continue;
                    }
                    st.cse.insert(not_key, output);
                    st.mark_bool(output);
                    st.known_not.insert(output, rb.clone());
                    st.changed = true;
                    out.push(CircuitInstr::Not { a: rb, output });
                    continue;
                }
                let (oa, ob) = order_pair(ca, cb);
                let key = CseKey::TestEq(oa, ob);
                if let Some(&prev) = st.cse.get(&key) {
                    st.subst(output, CircuitVal::Var(prev));
                    continue;
                }
                st.cse.insert(key, output);
                st.mark_bool(output);
                out.push(CircuitInstr::TestEq {
                    a: ra,
                    b: rb,
                    output,
                });
            }
            CircuitInstr::LessThan { a, b, bits, output } => {
                let ra = st.resolve(&a);
                let rb = st.resolve(&b);
                st.set_type(output, WireType::Native);
                if let (CircuitVal::Imm(x), CircuitVal::Imm(y)) = (&ra, &rb)
                    && *x >= 0
                    && *y >= 0
                    && const_fits_in_bits(&ra, bits)
                    && const_fits_in_bits(&rb, bits)
                {
                    st.subst(output, CircuitVal::Imm(if x < y { 1 } else { 0 }));
                    continue;
                }
                let a_in_range = val_proven_within_bits(&ra, bits, &st.known_bits);
                let b_in_range = val_proven_within_bits(&rb, bits, &st.known_bits);
                if a_in_range && b_in_range {
                    if CanonVal::from_val(&ra) == CanonVal::from_val(&rb) {
                        st.subst(output, CircuitVal::FALSE);
                        continue;
                    }
                    if is_const_zero(&rb) {
                        st.subst(output, CircuitVal::FALSE);
                        continue;
                    }
                }
                let key = CseKey::LessThan(CanonVal::from_val(&ra), CanonVal::from_val(&rb), bits);
                if let Some(&prev) = st.cse.get(&key) {
                    st.subst(output, CircuitVal::Var(prev));
                    continue;
                }
                // `LessThan` constrains both inputs to `< 2^bits` in ZKIR. Only mark it
                // droppable by DCE if both operands were ALREADY proven within `bits` before
                // this instruction.
                if a_in_range && b_in_range {
                    droppable_lt.insert(output);
                }
                if let CircuitVal::Var(va) = ra {
                    st.record_bits(va, bits);
                }
                if let CircuitVal::Var(vb) = rb {
                    st.record_bits(vb, bits);
                }
                st.cse.insert(key, output);
                st.mark_bool(output);
                out.push(CircuitInstr::LessThan {
                    a: ra,
                    b: rb,
                    bits,
                    output,
                });
            }
            CircuitInstr::CondSelect { bit, a, b, output } => {
                let mut rbit = st.resolve(&bit);
                let mut ra = st.resolve(&a);
                let mut rb = st.resolve(&b);
                let wt = st.wire_type(&ra);
                st.set_type(output, wt);

                // Flip `CondSelect(Not(c), a, b)` -> `CondSelect(c, b, a)`.
                if let CircuitVal::Var(vb) = rbit
                    && let Some(inner) = st.known_not.get(&vb).cloned()
                    && st.is_known_bool(&inner)
                {
                    rbit = inner;
                    std::mem::swap(&mut ra, &mut rb);
                    st.changed = true;
                }

                // Specialize arms under `rbit == 1` (true arm) and `rbit == 0` (false arm).
                let cbit = CanonVal::from_val(&rbit);
                if st.is_known_bool(&rbit) && wt == WireType::Native {
                    if CanonVal::from_val(&ra) == cbit {
                        ra = CircuitVal::TRUE;
                        st.changed = true;
                    }
                    if CanonVal::from_val(&rb) == cbit {
                        rb = CircuitVal::FALSE;
                        st.changed = true;
                    }
                }
                if let CircuitVal::Var(va) = ra
                    && let Some((c2, t2, _)) = st.known_cond_select.get(&va)
                    && CanonVal::from_val(c2) == cbit
                {
                    ra = t2.clone();
                    st.changed = true;
                }
                if let CircuitVal::Var(vb) = rb
                    && let Some((c2, _, e2)) = st.known_cond_select.get(&vb)
                    && CanonVal::from_val(c2) == cbit
                {
                    rb = e2.clone();
                    st.changed = true;
                }

                if is_const_one(&rbit) {
                    st.subst(output, ra);
                    continue;
                }
                if is_const_zero(&rbit) {
                    st.subst(output, rb);
                    continue;
                }
                let ca = CanonVal::from_val(&ra);
                let cb = CanonVal::from_val(&rb);
                if ca == cb {
                    st.subst(output, ra);
                    continue;
                }
                if st.is_known_bool(&rbit) && is_const_one(&ra) && is_const_zero(&rb) {
                    st.subst(output, rbit);
                    continue;
                }
                if st.is_known_bool(&rbit) && is_const_zero(&ra) && is_const_one(&rb) {
                    let not_key = CseKey::Not(cbit);
                    if let Some(&prev) = st.cse.get(&not_key) {
                        st.subst(output, CircuitVal::Var(prev));
                        continue;
                    }
                    st.cse.insert(not_key, output);
                    st.mark_bool(output);
                    st.known_not.insert(output, rbit.clone());
                    st.changed = true;
                    out.push(CircuitInstr::Not { a: rbit, output });
                    continue;
                }

                // Boolean AND (`CondSelect(bit, a, 0)`) idempotence & commutativity:
                // - `(x && y) && x` -> `x && y`
                // - `x && !x` -> `0`
                // - `a && b` == `b && a` for CSE
                let is_bool_and =
                    st.is_known_bool(&rbit) && st.is_known_bool(&ra) && is_const_zero(&rb);
                if is_bool_and {
                    let bit_implies_a = matches!(rbit, CircuitVal::Var(vb)
                        if st.known_and_factors.get(&vb).is_some_and(|fs| fs.contains(&ca)));
                    if bit_implies_a {
                        st.subst(output, rbit);
                        continue;
                    }
                    let a_implies_bit = matches!(ra, CircuitVal::Var(va)
                        if st.known_and_factors.get(&va).is_some_and(|fs| fs.contains(&cbit)));
                    if a_implies_bit {
                        st.subst(output, ra);
                        continue;
                    }
                    // `x && !x == 0`
                    let contradictory = matches!(rbit, CircuitVal::Var(vb)
                        if st.known_not.get(&vb).is_some_and(|inner| CanonVal::from_val(inner) == ca))
                        || matches!(ra, CircuitVal::Var(va)
                            if st.known_not.get(&va).is_some_and(|inner| CanonVal::from_val(inner) == cbit));
                    if contradictory {
                        st.subst(output, CircuitVal::FALSE);
                        continue;
                    }
                    if ca < cbit {
                        std::mem::swap(&mut rbit, &mut ra);
                    }
                }

                // Boolean OR (`CondSelect(bit, 1, b)`) idempotence & commutativity:
                // - `(x || y) || x` -> `x || y`
                // - `x || !x` -> `1`
                // - `a || b` == `b || a` for CSE
                let is_bool_or =
                    st.is_known_bool(&rbit) && is_const_one(&ra) && st.is_known_bool(&rb);
                if is_bool_or {
                    let bit_contains_b = matches!(rbit, CircuitVal::Var(vb)
                        if st.known_or_terms.get(&vb).is_some_and(|ts| ts.contains(&cb)));
                    if bit_contains_b {
                        st.subst(output, rbit);
                        continue;
                    }
                    let b_contains_bit = matches!(rb, CircuitVal::Var(vb)
                        if st.known_or_terms.get(&vb).is_some_and(|ts| ts.contains(&cbit)));
                    if b_contains_bit {
                        st.subst(output, rb);
                        continue;
                    }
                    // `x || !x == 1`
                    let tautology = matches!(rbit, CircuitVal::Var(vb)
                        if st.known_not.get(&vb).is_some_and(|inner| CanonVal::from_val(inner) == cb))
                        || matches!(rb, CircuitVal::Var(vb)
                            if st.known_not.get(&vb).is_some_and(|inner| CanonVal::from_val(inner) == cbit));
                    if tautology {
                        st.subst(output, CircuitVal::TRUE);
                        continue;
                    }
                    if cb < cbit {
                        std::mem::swap(&mut rbit, &mut rb);
                    }
                }

                let cbit_final = CanonVal::from_val(&rbit);
                let ca_final = CanonVal::from_val(&ra);
                let cb_final = CanonVal::from_val(&rb);
                let key =
                    CseKey::CondSelect(cbit_final.clone(), ca_final.clone(), cb_final.clone());
                if let Some(&prev) = st.cse.get(&key) {
                    st.subst(output, CircuitVal::Var(prev));
                    continue;
                }
                st.cse.insert(key, output);
                if st.is_known_bool(&ra) && st.is_known_bool(&rb) {
                    st.mark_bool(output);
                }
                if is_bool_and {
                    let mut factors = HashSet::new();
                    factors.insert(cbit_final.clone());
                    factors.insert(ca_final.clone());
                    if let CircuitVal::Var(vb) = rbit
                        && let Some(prev) = st.known_and_factors.get(&vb)
                    {
                        factors.extend(prev.iter().cloned());
                    }
                    if let CircuitVal::Var(va) = ra
                        && let Some(prev) = st.known_and_factors.get(&va)
                    {
                        factors.extend(prev.iter().cloned());
                    }
                    st.known_and_factors.insert(output, factors);
                } else if is_bool_or {
                    let mut terms = HashSet::new();
                    terms.insert(cbit_final.clone());
                    terms.insert(cb_final.clone());
                    if let CircuitVal::Var(vb) = rbit
                        && let Some(prev) = st.known_or_terms.get(&vb)
                    {
                        terms.extend(prev.iter().cloned());
                    }
                    if let CircuitVal::Var(vb) = rb
                        && let Some(prev) = st.known_or_terms.get(&vb)
                    {
                        terms.extend(prev.iter().cloned());
                    }
                    st.known_or_terms.insert(output, terms);
                }
                st.known_cond_select
                    .insert(output, (rbit.clone(), ra.clone(), rb.clone()));
                out.push(CircuitInstr::CondSelect {
                    bit: rbit,
                    a: ra,
                    b: rb,
                    output,
                });
            }
            CircuitInstr::DivModPowerOfTwo {
                val,
                bits,
                quotient,
                remainder,
            } => {
                let rv = st.resolve(&val);
                st.set_type(quotient, WireType::Native);
                st.set_type(remainder, WireType::Native);
                if let CircuitVal::Imm(n) = rv
                    && n >= 0
                    && bits < 127
                {
                    let q = n >> bits;
                    let mask = (1i128 << bits) - 1;
                    let r = n & mask;
                    st.subst(quotient, CircuitVal::Imm(q));
                    st.subst(remainder, CircuitVal::Imm(r));
                    continue;
                }
                let key = CseMultiKey::DivModPowerOfTwo(CanonVal::from_val(&rv), bits);
                if let Some(prev) = st.cse_multi.get(&key).cloned() {
                    st.subst(quotient, CircuitVal::Var(prev[0]));
                    st.subst(remainder, CircuitVal::Var(prev[1]));
                    continue;
                }
                st.cse_multi.insert(key, vec![quotient, remainder]);
                st.record_bits(remainder, bits);
                out.push(CircuitInstr::DivModPowerOfTwo {
                    val: rv,
                    bits,
                    quotient,
                    remainder,
                });
            }
            CircuitInstr::Encode { input, outputs } => {
                let ri = st.resolve(&input);
                for &v in &outputs {
                    st.set_type(v, WireType::Native);
                }
                let key = CseMultiKey::Encode(CanonVal::from_val(&ri), outputs.len());
                if let Some(prev) = st.cse_multi.get(&key).cloned() {
                    for (dst, src) in outputs.into_iter().zip(prev) {
                        st.subst(dst, CircuitVal::Var(src));
                    }
                    continue;
                }
                st.cse_multi.insert(key, outputs.clone());
                out.push(CircuitInstr::Encode { input: ri, outputs });
            }
            CircuitInstr::PersistentHash {
                alignment,
                inputs,
                output,
            } => {
                let rinputs = st.resolve_vec(&inputs);
                st.set_type(output, WireType::Native);
                let key = CseKey::PersistentHash(
                    alignment_key(&alignment),
                    rinputs.iter().map(CanonVal::from_val).collect(),
                );
                if let Some(&prev) = st.cse.get(&key) {
                    st.subst(output, CircuitVal::Var(prev));
                    continue;
                }
                st.cse.insert(key, output);
                out.push(CircuitInstr::PersistentHash {
                    alignment,
                    inputs: rinputs,
                    output,
                });
            }
            CircuitInstr::Keccak256 {
                alignment,
                inputs,
                output,
            } => {
                let rinputs = st.resolve_vec(&inputs);
                st.set_type(output, WireType::Native);
                let key = CseKey::Keccak256(
                    alignment_key(&alignment),
                    rinputs.iter().map(CanonVal::from_val).collect(),
                );
                if let Some(&prev) = st.cse.get(&key) {
                    st.subst(output, CircuitVal::Var(prev));
                    continue;
                }
                st.cse.insert(key, output);
                out.push(CircuitInstr::Keccak256 {
                    alignment,
                    inputs: rinputs,
                    output,
                });
            }
            CircuitInstr::Sha512 {
                alignment,
                inputs,
                output,
            } => {
                let rinputs = st.resolve_vec(&inputs);
                st.set_type(output, WireType::Native);
                let key = CseKey::Sha512(
                    alignment_key(&alignment),
                    rinputs.iter().map(CanonVal::from_val).collect(),
                );
                if let Some(&prev) = st.cse.get(&key) {
                    st.subst(output, CircuitVal::Var(prev));
                    continue;
                }
                st.cse.insert(key, output);
                out.push(CircuitInstr::Sha512 {
                    alignment,
                    inputs: rinputs,
                    output,
                });
            }
            CircuitInstr::TransientHash { inputs, output } => {
                let rinputs = st.resolve_vec(&inputs);
                st.set_type(output, WireType::Native);
                let key = CseKey::TransientHash(rinputs.iter().map(CanonVal::from_val).collect());
                if let Some(&prev) = st.cse.get(&key) {
                    st.subst(output, CircuitVal::Var(prev));
                    continue;
                }
                st.cse.insert(key, output);
                out.push(CircuitInstr::TransientHash {
                    inputs: rinputs,
                    output,
                });
            }
            CircuitInstr::HashToCurve { inputs, output } => {
                let rinputs = st.resolve_vec(&inputs);
                st.set_type(output, WireType::JubjubPoint);
                let key = CseKey::HashToCurve(rinputs.iter().map(CanonVal::from_val).collect());
                if let Some(&prev) = st.cse.get(&key) {
                    st.subst(output, CircuitVal::Var(prev));
                    continue;
                }
                st.cse.insert(key, output);
                out.push(CircuitInstr::HashToCurve {
                    inputs: rinputs,
                    output,
                });
            }
            CircuitInstr::EcMul { a, scalar, output } => {
                let ra = st.resolve(&a);
                let rs = st.resolve(&scalar);
                let wt = st.wire_type(&ra);
                st.set_type(output, wt);
                let key = CseKey::EcMul(CanonVal::from_val(&ra), CanonVal::from_val(&rs));
                if let Some(&prev) = st.cse.get(&key) {
                    st.subst(output, CircuitVal::Var(prev));
                    continue;
                }
                st.cse.insert(key, output);
                out.push(CircuitInstr::EcMul {
                    a: ra,
                    scalar: rs,
                    output,
                });
            }
            CircuitInstr::EcMulGenerator { scalar, output } => {
                let rs = st.resolve(&scalar);
                st.set_type(output, WireType::JubjubPoint);
                let key = CseKey::EcMulGenerator(CanonVal::from_val(&rs));
                if let Some(&prev) = st.cse.get(&key) {
                    st.subst(output, CircuitVal::Var(prev));
                    continue;
                }
                st.cse.insert(key, output);
                out.push(CircuitInstr::EcMulGenerator { scalar: rs, output });
            }
            CircuitInstr::IntoCoordinates { point, x, y } => {
                let rp = st.resolve(&point);
                let coord_wt = match st.wire_type(&rp) {
                    WireType::JubjubPoint => WireType::Native,
                    WireType::Secp256k1Point => WireType::Secp256k1Base,
                    WireType::Secp256r1Point => WireType::Secp256r1Base,
                    WireType::Curve25519Point => WireType::Curve25519Base,
                    _ => WireType::Native,
                };
                st.set_type(x, coord_wt);
                st.set_type(y, coord_wt);
                let key = CseMultiKey::IntoCoordinates(CanonVal::from_val(&rp));
                if let Some(prev) = st.cse_multi.get(&key).cloned() {
                    st.subst(x, CircuitVal::Var(prev[0]));
                    st.subst(y, CircuitVal::Var(prev[1]));
                    continue;
                }
                st.cse_multi.insert(key, vec![x, y]);
                out.push(CircuitInstr::IntoCoordinates { point: rp, x, y });
            }
            CircuitInstr::FromCoordinates { x, y, output } => {
                let rx = st.resolve(&x);
                let ry = st.resolve(&y);
                st.set_type(output, WireType::JubjubPoint);
                // Keep unconditionally because `FromCoordinates` constrains point-on-curve.
                out.push(CircuitInstr::FromCoordinates {
                    x: rx,
                    y: ry,
                    output,
                });
            }
            CircuitInstr::JubjubScalarFromNative { native, output } => {
                let rn = st.resolve(&native);
                st.set_type(output, WireType::JubjubScalar);
                // Keep unconditionally because it constrains `native < r_J`.
                out.push(CircuitInstr::JubjubScalarFromNative { native: rn, output });
            }
            CircuitInstr::BytesIntoNatives { bytes, outputs } => {
                let rb = st.resolve_var(bytes);
                for &v in &outputs {
                    st.set_type(v, WireType::Native);
                }
                let key = CseMultiKey::BytesIntoNatives(rb.id, outputs.len());
                if let Some(prev) = st.cse_multi.get(&key).cloned() {
                    for (dst, src) in outputs.into_iter().zip(prev) {
                        st.subst(dst, CircuitVal::Var(src));
                    }
                    continue;
                }
                st.cse_multi.insert(key, outputs.clone());
                out.push(CircuitInstr::BytesIntoNatives { bytes: rb, outputs });
            }
            CircuitInstr::BytesFromNatives {
                inputs,
                len,
                output,
            } => {
                let rinputs = st.resolve_vec(&inputs);
                st.set_type(output, WireType::Native);
                let key =
                    CseKey::BytesFromNatives(rinputs.iter().map(CanonVal::from_val).collect(), len);
                if let Some(&prev) = st.cse.get(&key) {
                    st.subst(output, CircuitVal::Var(prev));
                    continue;
                }
                st.cse.insert(key, output);
                out.push(CircuitInstr::BytesFromNatives {
                    inputs: rinputs,
                    len,
                    output,
                });
            }
            CircuitInstr::ToBytes { input, output } => {
                let ri = st.resolve(&input);
                st.set_type(output, WireType::Native);
                let key = CseKey::ToBytes(CanonVal::from_val(&ri));
                if let Some(&prev) = st.cse.get(&key) {
                    st.subst(output, CircuitVal::Var(prev));
                    continue;
                }
                st.cse.insert(key, output);
                out.push(CircuitInstr::ToBytes { input: ri, output });
            }
            CircuitInstr::FromBytes {
                bytes,
                val_t,
                output,
            } => {
                let rb = st.resolve_var(bytes);
                st.set_type(output, val_t);
                // Keep unconditionally because non-native `FromBytes` constrains valid encodings.
                out.push(CircuitInstr::FromBytes {
                    bytes: rb,
                    val_t,
                    output,
                });
            }
            CircuitInstr::Slice {
                bytes,
                start,
                len,
                output,
            } => {
                let rb = st.resolve_var(bytes);
                st.set_type(output, WireType::Native);
                let key = CseKey::Slice(rb.id, start, len);
                if let Some(&prev) = st.cse.get(&key) {
                    st.subst(output, CircuitVal::Var(prev));
                    continue;
                }
                st.cse.insert(key, output);
                out.push(CircuitInstr::Slice {
                    bytes: rb,
                    start,
                    len,
                    output,
                });
            }
            CircuitInstr::Impact { guard, op } => {
                let rg = st.resolve(&guard);
                if is_const_zero(&rg) {
                    st.changed = true;
                    continue;
                }
                let rop = st.resolve_impact_op(&op);
                out.push(CircuitInstr::Impact { guard: rg, op: rop });
            }
            CircuitInstr::Output { vals } => {
                let rvals = st.resolve_vec(&vals);
                out.push(CircuitInstr::Output { vals: rvals });
            }
        }
    }

    circuit.instructions = out;
    (st.changed, droppable_lt)
}

fn mark_val_live(val: &CircuitVal, live: &mut [bool]) {
    if let CircuitVal::Var(v) = val
        && let Some(slot) = live.get_mut(v.id as usize)
    {
        *slot = true;
    }
}

fn mark_var_live(var: CircuitVar, live: &mut [bool]) {
    if let Some(slot) = live.get_mut(var.id as usize) {
        *slot = true;
    }
}

fn mark_impact_state_live(sv: &ImpactStateValue, live: &mut [bool]) {
    match sv {
        ImpactStateValue::Cell { values, .. } => {
            for v in values {
                mark_val_live(v, live);
            }
        }
        ImpactStateValue::Array(elems) => {
            for e in elems {
                mark_impact_state_live(e, live);
            }
        }
        ImpactStateValue::Null
        | ImpactStateValue::EmptyMap
        | ImpactStateValue::MerkleTree { .. } => {}
    }
}

fn mark_impact_op_live(op: &ImpactVmOp, live: &mut [bool]) {
    match op {
        ImpactVmOp::Idx { path, .. } => {
            for seg in path {
                if let PathSegment::Dynamic { values, .. } = seg {
                    for v in values {
                        mark_val_live(v, live);
                    }
                }
            }
        }
        ImpactVmOp::Popeq { results, .. } => {
            for v in results {
                mark_val_live(v, live);
            }
        }
        ImpactVmOp::Push { value, .. } => mark_impact_state_live(value, live),
        ImpactVmOp::Addi { immediate } | ImpactVmOp::Subi { immediate } => {
            mark_val_live(immediate, live);
        }
        _ => {}
    }
}

fn backward_dce(circuit: &mut ProofCircuit, droppable_lt: &HashSet<CircuitVar>) -> bool {
    let n = circuit.var_names.len();
    let mut live = vec![false; n];
    let old_instrs = std::mem::take(&mut circuit.instructions);
    let old_len = old_instrs.len();
    let mut kept_rev = Vec::with_capacity(old_len);

    for instr in old_instrs.into_iter().rev() {
        let is_live = match &instr {
            // Side-effecting / transcript / constraint roots: always keep.
            CircuitInstr::Output { .. }
            | CircuitInstr::Assert { .. }
            | CircuitInstr::ConstrainToBoolean { .. }
            | CircuitInstr::ConstrainBits { .. }
            | CircuitInstr::ConstrainEq { .. }
            | CircuitInstr::Impact { .. }
            | CircuitInstr::PublicInput { .. }
            | CircuitInstr::PrivateInput { .. }
            | CircuitInstr::Inv { .. }
            | CircuitInstr::FromBytes { .. }
            | CircuitInstr::FromCoordinates { .. }
            | CircuitInstr::JubjubScalarFromNative { .. } => true,

            // `LessThan` constrains both operands to `< 2^bits`, so only drop if both were
            // already proven within `bits` before this instruction AND its output is unused.
            CircuitInstr::LessThan { output, .. } => {
                live.get(output.id as usize).copied().unwrap_or(false)
                    || !droppable_lt.contains(output)
            }

            // Pure single-output ops.
            CircuitInstr::Copy { output, .. }
            | CircuitInstr::PersistentHash { output, .. }
            | CircuitInstr::Keccak256 { output, .. }
            | CircuitInstr::Sha512 { output, .. }
            | CircuitInstr::TransientHash { output, .. }
            | CircuitInstr::BytesFromNatives { output, .. }
            | CircuitInstr::ToBytes { output, .. }
            | CircuitInstr::Slice { output, .. }
            | CircuitInstr::TestEq { output, .. }
            | CircuitInstr::Not { output, .. }
            | CircuitInstr::Add { output, .. }
            | CircuitInstr::Mul { output, .. }
            | CircuitInstr::Neg { output, .. }
            | CircuitInstr::EcMul { output, .. }
            | CircuitInstr::EcMulGenerator { output, .. }
            | CircuitInstr::HashToCurve { output, .. }
            | CircuitInstr::CondSelect { output, .. } => {
                live.get(output.id as usize).copied().unwrap_or(false)
            }

            // Pure multi-output ops.
            CircuitInstr::Encode { outputs, .. }
            | CircuitInstr::BytesIntoNatives { outputs, .. } => outputs
                .iter()
                .any(|v| live.get(v.id as usize).copied().unwrap_or(false)),
            CircuitInstr::DivModPowerOfTwo {
                quotient,
                remainder,
                ..
            } => {
                live.get(quotient.id as usize).copied().unwrap_or(false)
                    || live.get(remainder.id as usize).copied().unwrap_or(false)
            }
            CircuitInstr::IntoCoordinates { x, y, .. } => {
                live.get(x.id as usize).copied().unwrap_or(false)
                    || live.get(y.id as usize).copied().unwrap_or(false)
            }
        };

        if !is_live {
            continue;
        }

        // Mark all read operands live.
        match &instr {
            CircuitInstr::PublicInput { guard, .. } | CircuitInstr::PrivateInput { guard, .. } => {
                if let Some(g) = guard {
                    mark_val_live(g, &mut live);
                }
            }
            CircuitInstr::ConstrainToBoolean { val }
            | CircuitInstr::ConstrainBits { val, .. }
            | CircuitInstr::Copy { val, .. }
            | CircuitInstr::DivModPowerOfTwo { val, .. } => mark_val_live(val, &mut live),
            CircuitInstr::ConstrainEq { a, b }
            | CircuitInstr::LessThan { a, b, .. }
            | CircuitInstr::TestEq { a, b, .. }
            | CircuitInstr::Add { a, b, .. }
            | CircuitInstr::Mul { a, b, .. } => {
                mark_val_live(a, &mut live);
                mark_val_live(b, &mut live);
            }
            CircuitInstr::Not { a, .. }
            | CircuitInstr::Neg { a, .. }
            | CircuitInstr::Inv { a, .. } => mark_val_live(a, &mut live),
            CircuitInstr::Encode { input, .. } | CircuitInstr::ToBytes { input, .. } => {
                mark_val_live(input, &mut live);
            }
            CircuitInstr::Impact { guard, op } => {
                mark_val_live(guard, &mut live);
                mark_impact_op_live(op, &mut live);
            }
            CircuitInstr::PersistentHash { inputs, .. }
            | CircuitInstr::Keccak256 { inputs, .. }
            | CircuitInstr::Sha512 { inputs, .. }
            | CircuitInstr::TransientHash { inputs, .. }
            | CircuitInstr::BytesFromNatives { inputs, .. }
            | CircuitInstr::HashToCurve { inputs, .. } => {
                for v in inputs {
                    mark_val_live(v, &mut live);
                }
            }
            CircuitInstr::BytesIntoNatives { bytes, .. }
            | CircuitInstr::FromBytes { bytes, .. }
            | CircuitInstr::Slice { bytes, .. } => mark_var_live(*bytes, &mut live),
            CircuitInstr::JubjubScalarFromNative { native, .. } => {
                mark_val_live(native, &mut live);
            }
            CircuitInstr::EcMul { a, scalar, .. } => {
                mark_val_live(a, &mut live);
                mark_val_live(scalar, &mut live);
            }
            CircuitInstr::EcMulGenerator { scalar, .. } => mark_val_live(scalar, &mut live),
            CircuitInstr::IntoCoordinates { point, .. } => mark_val_live(point, &mut live),
            CircuitInstr::FromCoordinates { x, y, .. } => {
                mark_val_live(x, &mut live);
                mark_val_live(y, &mut live);
            }
            CircuitInstr::CondSelect { bit, a, b, .. } => {
                mark_val_live(bit, &mut live);
                mark_val_live(a, &mut live);
                mark_val_live(b, &mut live);
            }
            CircuitInstr::Assert { cond } => mark_val_live(cond, &mut live),
            CircuitInstr::Output { vals } => {
                for v in vals {
                    mark_val_live(v, &mut live);
                }
            }
        }

        kept_rev.push(instr);
    }

    kept_rev.reverse();
    let changed = kept_rev.len() != old_len;
    circuit.instructions = kept_rev;
    changed
}

/// Renumber all surviving `CircuitVar` IDs densely (`0..N`) and compact `var_names`.
fn compact_vars(circuit: &mut ProofCircuit) {
    let old_names = std::mem::take(&mut circuit.var_names);
    let mut remap: Vec<Option<CircuitVar>> = vec![None; old_names.len()];
    let mut new_names: Vec<String> = Vec::with_capacity(old_names.len());

    let alloc = |old: CircuitVar,
                 remap: &mut [Option<CircuitVar>],
                 new_names: &mut Vec<String>,
                 old_names: &[String]|
     -> CircuitVar {
        if let Some(existing) = remap[old.id as usize] {
            return existing;
        }
        let id = new_names.len() as u32;
        let hint = old_names
            .get(old.id as usize)
            .cloned()
            .unwrap_or_else(|| "v".to_owned());
        new_names.push(hint);
        let nv = CircuitVar { id };
        remap[old.id as usize] = Some(nv);
        nv
    };

    let map_var = |old: CircuitVar, remap: &[Option<CircuitVar>]| -> CircuitVar {
        remap[old.id as usize].expect("referenced CircuitVar must be defined before use")
    };

    let map_val = |val: &mut CircuitVal, remap: &[Option<CircuitVar>]| {
        if let CircuitVal::Var(v) = val {
            *v = map_var(*v, remap);
        }
    };

    fn map_impact_state(sv: &mut ImpactStateValue, remap: &[Option<CircuitVar>]) {
        match sv {
            ImpactStateValue::Cell { values, .. } => {
                for v in values {
                    if let CircuitVal::Var(var) = v {
                        *var = remap[var.id as usize]
                            .expect("referenced CircuitVar in ImpactStateValue must be defined");
                    }
                }
            }
            ImpactStateValue::Array(elems) => {
                for e in elems {
                    map_impact_state(e, remap);
                }
            }
            ImpactStateValue::Null
            | ImpactStateValue::EmptyMap
            | ImpactStateValue::MerkleTree { .. } => {}
        }
    }

    for (var, _) in &mut circuit.inputs {
        *var = alloc(*var, &mut remap, &mut new_names, &old_names);
    }

    for instr in &mut circuit.instructions {
        match instr {
            CircuitInstr::PublicInput { guard, output, .. }
            | CircuitInstr::PrivateInput { guard, output, .. } => {
                if let Some(g) = guard {
                    map_val(g, &remap);
                }
                *output = alloc(*output, &mut remap, &mut new_names, &old_names);
            }
            CircuitInstr::ConstrainToBoolean { val } | CircuitInstr::ConstrainBits { val, .. } => {
                map_val(val, &remap);
            }
            CircuitInstr::ConstrainEq { a, b } => {
                map_val(a, &remap);
                map_val(b, &remap);
            }
            CircuitInstr::LessThan { a, b, output, .. }
            | CircuitInstr::TestEq { a, b, output }
            | CircuitInstr::Add { a, b, output }
            | CircuitInstr::Mul { a, b, output } => {
                map_val(a, &remap);
                map_val(b, &remap);
                *output = alloc(*output, &mut remap, &mut new_names, &old_names);
            }
            CircuitInstr::Copy { val, output } => {
                map_val(val, &remap);
                *output = alloc(*output, &mut remap, &mut new_names, &old_names);
            }
            CircuitInstr::Not { a, output }
            | CircuitInstr::Neg { a, output }
            | CircuitInstr::Inv { a, output } => {
                map_val(a, &remap);
                *output = alloc(*output, &mut remap, &mut new_names, &old_names);
            }
            CircuitInstr::Encode { input, outputs } => {
                map_val(input, &remap);
                for o in outputs {
                    *o = alloc(*o, &mut remap, &mut new_names, &old_names);
                }
            }
            CircuitInstr::Impact { guard, op } => {
                map_val(guard, &remap);
                match op {
                    ImpactVmOp::Idx { path, .. } => {
                        for seg in path {
                            if let PathSegment::Dynamic { values, .. } = seg {
                                for v in values {
                                    map_val(v, &remap);
                                }
                            }
                        }
                    }
                    ImpactVmOp::Popeq { results, .. } => {
                        for v in results {
                            map_val(v, &remap);
                        }
                    }
                    ImpactVmOp::Push { value, .. } => map_impact_state(value, &remap),
                    ImpactVmOp::Addi { immediate } | ImpactVmOp::Subi { immediate } => {
                        map_val(immediate, &remap);
                    }
                    _ => {}
                }
            }
            CircuitInstr::PersistentHash { inputs, output, .. }
            | CircuitInstr::Keccak256 { inputs, output, .. }
            | CircuitInstr::Sha512 { inputs, output, .. }
            | CircuitInstr::TransientHash { inputs, output }
            | CircuitInstr::BytesFromNatives { inputs, output, .. }
            | CircuitInstr::HashToCurve { inputs, output } => {
                for v in inputs {
                    map_val(v, &remap);
                }
                *output = alloc(*output, &mut remap, &mut new_names, &old_names);
            }
            CircuitInstr::BytesIntoNatives { bytes, outputs } => {
                *bytes = map_var(*bytes, &remap);
                for o in outputs {
                    *o = alloc(*o, &mut remap, &mut new_names, &old_names);
                }
            }
            CircuitInstr::ToBytes { input, output } => {
                map_val(input, &remap);
                *output = alloc(*output, &mut remap, &mut new_names, &old_names);
            }
            CircuitInstr::FromBytes { bytes, output, .. }
            | CircuitInstr::Slice { bytes, output, .. } => {
                *bytes = map_var(*bytes, &remap);
                *output = alloc(*output, &mut remap, &mut new_names, &old_names);
            }
            CircuitInstr::JubjubScalarFromNative { native, output } => {
                map_val(native, &remap);
                *output = alloc(*output, &mut remap, &mut new_names, &old_names);
            }
            CircuitInstr::DivModPowerOfTwo {
                val,
                quotient,
                remainder,
                ..
            } => {
                map_val(val, &remap);
                *quotient = alloc(*quotient, &mut remap, &mut new_names, &old_names);
                *remainder = alloc(*remainder, &mut remap, &mut new_names, &old_names);
            }
            CircuitInstr::EcMul { a, scalar, output } => {
                map_val(a, &remap);
                map_val(scalar, &remap);
                *output = alloc(*output, &mut remap, &mut new_names, &old_names);
            }
            CircuitInstr::EcMulGenerator { scalar, output } => {
                map_val(scalar, &remap);
                *output = alloc(*output, &mut remap, &mut new_names, &old_names);
            }
            CircuitInstr::IntoCoordinates { point, x, y } => {
                map_val(point, &remap);
                *x = alloc(*x, &mut remap, &mut new_names, &old_names);
                *y = alloc(*y, &mut remap, &mut new_names, &old_names);
            }
            CircuitInstr::FromCoordinates { x, y, output } => {
                map_val(x, &remap);
                map_val(y, &remap);
                *output = alloc(*output, &mut remap, &mut new_names, &old_names);
            }
            CircuitInstr::CondSelect { bit, a, b, output } => {
                map_val(bit, &remap);
                map_val(a, &remap);
                map_val(b, &remap);
                *output = alloc(*output, &mut remap, &mut new_names, &old_names);
            }
            CircuitInstr::Assert { cond } => map_val(cond, &remap),
            CircuitInstr::Output { vals } => {
                for v in vals {
                    map_val(v, &remap);
                }
            }
        }
    }

    circuit.var_names = new_names;
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mk_circuit(
        inputs: Vec<(&str, WireType)>,
        extra_names: Vec<&str>,
        instructions: Vec<CircuitInstr>,
        output_types: Vec<WireType>,
    ) -> ProofCircuit {
        let mut var_names = Vec::new();
        let mut typed_inputs = Vec::new();
        for (name, wt) in inputs {
            let id = var_names.len() as u32;
            var_names.push(name.to_owned());
            typed_inputs.push((CircuitVar { id }, wt));
        }
        for name in extra_names {
            var_names.push(name.to_owned());
        }
        ProofCircuit {
            name: "test".to_owned(),
            var_names,
            inputs: typed_inputs,
            output_types,
            instructions,
        }
    }

    #[test]
    fn folds_constants_identities_and_eliminates_dead_code() {
        let v0 = CircuitVar { id: 0 }; // input x
        let v1 = CircuitVar { id: 1 }; // x + 0
        let v2 = CircuitVar { id: 2 }; // v1 * 1
        let v3 = CircuitVar { id: 3 }; // 3 * 4 = 12
        let v4 = CircuitVar { id: 4 }; // v2 + v3
        let v5 = CircuitVar { id: 5 }; // dead: v4 * 99
        let v6 = CircuitVar { id: 6 }; // copy of v4

        let mut c = mk_circuit(
            vec![("x", WireType::Native)],
            vec!["t1", "t2", "t3", "t4", "dead", "cpy"],
            vec![
                CircuitInstr::Add {
                    a: CircuitVal::Var(v0),
                    b: CircuitVal::Imm(0),
                    output: v1,
                },
                CircuitInstr::Mul {
                    a: CircuitVal::Var(v1),
                    b: CircuitVal::Imm(1),
                    output: v2,
                },
                CircuitInstr::Mul {
                    a: CircuitVal::Imm(3),
                    b: CircuitVal::Imm(4),
                    output: v3,
                },
                CircuitInstr::Add {
                    a: CircuitVal::Var(v2),
                    b: CircuitVal::Var(v3),
                    output: v4,
                },
                CircuitInstr::Mul {
                    a: CircuitVal::Var(v4),
                    b: CircuitVal::Imm(99),
                    output: v5,
                },
                CircuitInstr::Copy {
                    val: CircuitVal::Var(v4),
                    output: v6,
                },
                CircuitInstr::Assert {
                    cond: CircuitVal::TRUE,
                },
                CircuitInstr::Output {
                    vals: vec![CircuitVal::Var(v6)],
                },
            ],
            vec![WireType::Native],
        );

        optimize_circuit(&mut c);

        // Expect only `Add(x, 12)` and `Output`.
        assert_eq!(c.instructions.len(), 2, "{:#?}", c.instructions);
        assert_eq!(
            c.instructions[0],
            CircuitInstr::Add {
                a: CircuitVal::Var(CircuitVar { id: 0 }),
                b: CircuitVal::Imm(12),
                output: CircuitVar { id: 1 },
            }
        );
        assert_eq!(
            c.instructions[1],
            CircuitInstr::Output {
                vals: vec![CircuitVal::Var(CircuitVar { id: 1 })],
            }
        );
        assert_eq!(c.var_names.len(), 2);
    }

    #[test]
    fn cse_deduplicates_commutative_ops_and_hashes() {
        let x = CircuitVar { id: 0 };
        let y = CircuitVar { id: 1 };
        let sum1 = CircuitVar { id: 2 };
        let sum2 = CircuitVar { id: 3 };
        let h1 = CircuitVar { id: 4 };
        let h2 = CircuitVar { id: 5 };
        let out = CircuitVar { id: 6 };

        let mut c = mk_circuit(
            vec![("x", WireType::Native), ("y", WireType::Native)],
            vec!["s1", "s2", "h1", "h2", "out"],
            vec![
                CircuitInstr::Add {
                    a: CircuitVal::Var(x),
                    b: CircuitVal::Var(y),
                    output: sum1,
                },
                CircuitInstr::Add {
                    a: CircuitVal::Var(y),
                    b: CircuitVal::Var(x),
                    output: sum2,
                },
                CircuitInstr::TransientHash {
                    inputs: vec![CircuitVal::Var(sum1)],
                    output: h1,
                },
                CircuitInstr::TransientHash {
                    inputs: vec![CircuitVal::Var(sum2)],
                    output: h2,
                },
                CircuitInstr::Add {
                    a: CircuitVal::Var(h1),
                    b: CircuitVal::Var(h2),
                    output: out,
                },
                CircuitInstr::Output {
                    vals: vec![CircuitVal::Var(out)],
                },
            ],
            vec![WireType::Native],
        );

        optimize_circuit(&mut c);

        // Only 1 Add(x, y), 1 TransientHash, 1 Add(h, h), 1 Output.
        assert_eq!(c.instructions.len(), 4, "{:#?}", c.instructions);
        assert!(matches!(c.instructions[0], CircuitInstr::Add { .. }));
        assert!(matches!(
            c.instructions[1],
            CircuitInstr::TransientHash { .. }
        ));
        assert_eq!(
            c.instructions[2],
            CircuitInstr::Add {
                a: CircuitVal::Var(CircuitVar { id: 3 }),
                b: CircuitVal::Var(CircuitVar { id: 3 }),
                output: CircuitVar { id: 4 },
            }
        );
    }

    #[test]
    fn simplifies_boolean_test_eq_not_and_cond_select() {
        let b = CircuitVar { id: 0 };
        let nb = CircuitVar { id: 1 };
        let nnb = CircuitVar { id: 2 };
        let eq0 = CircuitVar { id: 3 };
        let sel = CircuitVar { id: 4 };
        let inner_sel = CircuitVar { id: 5 };
        let outer_sel = CircuitVar { id: 6 };

        let mut c = mk_circuit(
            vec![("b", WireType::Native)],
            vec!["nb", "nnb", "eq0", "sel", "isel", "osel"],
            vec![
                CircuitInstr::ConstrainToBoolean {
                    val: CircuitVal::Var(b),
                },
                // Redundant boolean constraint should be eliminated.
                CircuitInstr::ConstrainToBoolean {
                    val: CircuitVal::Var(b),
                },
                CircuitInstr::Not {
                    a: CircuitVal::Var(b),
                    output: nb,
                },
                CircuitInstr::Not {
                    a: CircuitVal::Var(nb),
                    output: nnb,
                },
                // `nnb == 0` simplifies to `Not(b)`, hitting CSE with `nb`!
                CircuitInstr::TestEq {
                    a: CircuitVal::Var(nnb),
                    b: CircuitVal::Imm(0),
                    output: eq0,
                },
                // `CondSelect(Not(b), 10, 20)` flips to `CondSelect(b, 20, 10)`
                CircuitInstr::CondSelect {
                    bit: CircuitVal::Var(eq0),
                    a: CircuitVal::Imm(10),
                    b: CircuitVal::Imm(20),
                    output: sel,
                },
                // Nested `CondSelect(b, CondSelect(b, 20, 10), 10)` -> `CondSelect(b, 20, 10)` (CSE!)
                CircuitInstr::CondSelect {
                    bit: CircuitVal::Var(b),
                    a: CircuitVal::Var(sel),
                    b: CircuitVal::Imm(10),
                    output: inner_sel,
                },
                // `CondSelect(b, inner_sel, inner_sel)` -> `inner_sel`
                CircuitInstr::CondSelect {
                    bit: CircuitVal::Var(b),
                    a: CircuitVal::Var(inner_sel),
                    b: CircuitVal::Var(inner_sel),
                    output: outer_sel,
                },
                CircuitInstr::Output {
                    vals: vec![CircuitVal::Var(outer_sel)],
                },
            ],
            vec![WireType::Native],
        );

        optimize_circuit(&mut c);

        // Expect: 1 ConstrainToBoolean, 1 CondSelect(b, 20, 10), 1 Output!
        assert_eq!(c.instructions.len(), 3, "{:#?}", c.instructions);
        assert_eq!(
            c.instructions[0],
            CircuitInstr::ConstrainToBoolean {
                val: CircuitVal::Var(CircuitVar { id: 0 }),
            }
        );
        assert_eq!(
            c.instructions[1],
            CircuitInstr::CondSelect {
                bit: CircuitVal::Var(CircuitVar { id: 0 }),
                a: CircuitVal::Imm(20),
                b: CircuitVal::Imm(10),
                output: CircuitVar { id: 1 },
            }
        );
    }

    #[test]
    fn preserves_constraining_instructions_even_when_outputs_unused() {
        let x = CircuitVar { id: 0 };
        let inv_x = CircuitVar { id: 1 };
        let lt = CircuitVar { id: 2 };
        let pi = CircuitVar { id: 3 };

        let mut c = mk_circuit(
            vec![("x", WireType::Secp256k1Base)],
            vec!["inv_x", "lt", "pi"],
            vec![
                // Must keep `Inv` because it constrains `x != 0`.
                CircuitInstr::Inv {
                    a: CircuitVal::Var(x),
                    output: inv_x,
                },
                // Must keep `PublicInput` because it consumes transcript entries.
                CircuitInstr::PublicInput {
                    guard: None,
                    val_t: WireType::Native,
                    output: pi,
                },
                // Must keep `LessThan` because `pi` is not yet range-constrained to 8 bits.
                CircuitInstr::LessThan {
                    a: CircuitVal::Var(pi),
                    b: CircuitVal::Imm(100),
                    bits: 8,
                    output: lt,
                },
                // Dead `Impact` with guard == 0 CAN be dropped.
                CircuitInstr::Impact {
                    guard: CircuitVal::FALSE,
                    op: ImpactVmOp::Ckpt,
                },
                CircuitInstr::Output { vals: vec![] },
            ],
            vec![],
        );

        optimize_circuit(&mut c);

        // Dead Impact dropped; Inv, PublicInput, LessThan, Output all preserved!
        assert_eq!(c.instructions.len(), 4, "{:#?}", c.instructions);
        assert!(matches!(c.instructions[0], CircuitInstr::Inv { .. }));
        assert!(matches!(
            c.instructions[1],
            CircuitInstr::PublicInput { .. }
        ));
        assert!(matches!(c.instructions[2], CircuitInstr::LessThan { .. }));
        assert!(matches!(c.instructions[3], CircuitInstr::Output { .. }));
    }

    #[test]
    fn simplifies_boolean_and_or_idempotence_and_complements() {
        let a = CircuitVar { id: 0 };
        let b = CircuitVar { id: 1 };
        let ab = CircuitVar { id: 2 };
        let aba = CircuitVar { id: 3 };
        let na = CircuitVar { id: 4 };
        let contra = CircuitVar { id: 5 };
        let tauto = CircuitVar { id: 6 };

        let mut c = mk_circuit(
            vec![("a", WireType::Native), ("b", WireType::Native)],
            vec!["ab", "aba", "na", "contra", "tauto"],
            vec![
                CircuitInstr::ConstrainToBoolean {
                    val: CircuitVal::Var(a),
                },
                CircuitInstr::ConstrainToBoolean {
                    val: CircuitVal::Var(b),
                },
                CircuitInstr::CondSelect {
                    bit: CircuitVal::Var(a),
                    a: CircuitVal::Var(b),
                    b: CircuitVal::FALSE,
                    output: ab,
                },
                // `(a && b) && a` -> `a && b`
                CircuitInstr::CondSelect {
                    bit: CircuitVal::Var(ab),
                    a: CircuitVal::Var(a),
                    b: CircuitVal::FALSE,
                    output: aba,
                },
                CircuitInstr::Not {
                    a: CircuitVal::Var(a),
                    output: na,
                },
                // `a && !a` -> `0`
                CircuitInstr::CondSelect {
                    bit: CircuitVal::Var(a),
                    a: CircuitVal::Var(na),
                    b: CircuitVal::FALSE,
                    output: contra,
                },
                // `a || !a` -> `1`
                CircuitInstr::CondSelect {
                    bit: CircuitVal::Var(a),
                    a: CircuitVal::TRUE,
                    b: CircuitVal::Var(na),
                    output: tauto,
                },
                CircuitInstr::Output {
                    vals: vec![
                        CircuitVal::Var(aba),
                        CircuitVal::Var(contra),
                        CircuitVal::Var(tauto),
                    ],
                },
            ],
            vec![WireType::Native, WireType::Native, WireType::Native],
        );

        optimize_circuit(&mut c);

        // Expect: 2 ConstrainToBoolean, 1 CondSelect(a, b, 0), 1 Output([%ab, 0, 1])!
        assert_eq!(c.instructions.len(), 4, "{:#?}", c.instructions);
        assert_eq!(
            c.instructions[3],
            CircuitInstr::Output {
                vals: vec![
                    CircuitVal::Var(CircuitVar { id: 2 }),
                    CircuitVal::FALSE,
                    CircuitVal::TRUE,
                ],
            }
        );
    }
}
