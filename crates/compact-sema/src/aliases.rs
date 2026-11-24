//! Deprecated standard-library and ledger-operator name aliases migrated by `compact-fixup`.
//!
//! Mirrors upstream `compiler/standard-library-aliases.ss`.

/// Deprecated `CompactStandardLibrary` circuit/builtin names mapped to their canonical names.
pub const STDLIB_CIRCUIT_ALIASES: &[(&str, &str)] = &[
    ("transient_hash", "transientHash"),
    ("transient_commit", "transientCommit"),
    ("persistent_hash", "persistentHash"),
    ("persistent_commit", "persistentCommit"),
    ("degrade_to_transient", "degradeToTransient"),
    ("upgrade_from_transient", "upgradeFromTransient"),
    ("ec_add", "ecAdd"),
    ("ec_mul", "ecMul"),
    ("ec_mul_generator", "ecMulGenerator"),
    ("hash_to_curve", "hashToCurve"),
    ("merkle_tree_path_root", "merkleTreePathRoot"),
    (
        "merkle_tree_path_root_no_leaf_hash",
        "merkleTreePathRootNoLeafHash",
    ),
    ("native_token", "nativeToken"),
    ("own_public_key", "ownPublicKey"),
    ("create_zswap_input", "createZswapInput"),
    ("create_zswap_output", "createZswapOutput"),
    ("token_type", "tokenType"),
    ("mint_token", "mintShieldedToken"),
    ("evolve_nonce", "evolveNonce"),
    ("burn_address", "shieldedBurnAddress"),
    ("send_immediate", "sendImmediateShielded"),
    ("merge_coin", "mergeCoin"),
    ("merge_coin_immediate", "mergeCoinImmediate"),
    ("mintToken", "mintShieldedToken"),
    ("burnAddress", "shieldedBurnAddress"),
    ("receive", "receiveShielded"),
    ("send", "sendShielded"),
    ("sendImmediate", "sendImmediateShielded"),
    ("NativePointX", "jubjubPointX"),
    ("NativePointY", "jubjubPointY"),
    ("nativePointX", "jubjubPointX"),
    ("nativePointY", "jubjubPointY"),
    ("constructNativePoint", "constructJubjubPoint"),
];

/// Deprecated `CompactStandardLibrary` type aliases (currently empty upstream).
pub const STDLIB_TYPE_ALIASES: &[(&str, &str)] = &[];

/// Deprecated ledger ADT method names mapped to their canonical camelCase names.
pub const LEDGER_OP_ALIASES: &[(&str, &str)] = &[
    ("check_root", "checkRoot"),
    ("claim_contract_call", "claimContractCall"),
    ("claim_zswap_coin_receive", "claimZswapCoinReceive"),
    ("claim_zswap_coin_spend", "claimZswapCoinSpend"),
    ("claim_zswap_nullifier", "claimZswapNullifier"),
    ("insert_coin", "insertCoin"),
    ("insert_default", "insertDefault"),
    ("insert_hash", "insertHash"),
    ("insert_hash_index", "insertHashIndex"),
    ("insert_index", "insertIndex"),
    ("insert_index_default", "insertIndexDefault"),
    ("is_empty", "isEmpty"),
    ("is_full", "isFull"),
    ("less_than", "lessThan"),
    ("pop_front", "popFront"),
    ("push_front", "pushFront"),
    ("push_front_coin", "pushFrontCoin"),
    ("reset_history", "resetHistory"),
    ("reset_to_default", "resetToDefault"),
    ("write_coin", "writeCoin"),
];

pub fn lookup_stdlib_circuit_alias(name: &str) -> Option<&'static str> {
    STDLIB_CIRCUIT_ALIASES
        .iter()
        .find_map(|&(old, new)| (old == name).then_some(new))
}

pub fn lookup_stdlib_type_alias(name: &str) -> Option<&'static str> {
    STDLIB_TYPE_ALIASES
        .iter()
        .find_map(|&(old, new)| (old == name).then_some(new))
}

pub fn lookup_ledger_op_alias(name: &str) -> Option<&'static str> {
    LEDGER_OP_ALIASES
        .iter()
        .find_map(|&(old, new)| (old == name).then_some(new))
}
