/// Embedded Midnight Compact standard library definitions (types and helper circuits)
/// corresponding to upstream `standard-library.compact` (kernel, block-time, shielded &
/// unshielded token utilities).
///
/// Structs and circuits defined here are registered lazily by `compact-sema` when
/// `import CompactStandardLibrary;` is active, so only items actually referenced by a
/// contract are materialized into HIR, ZKIR, and TypeScript output.
pub const STDLIB_SOURCE: &str = r#"
export struct ContractAddress {
  bytes: Bytes<32>;
}

export struct UserAddress {
  bytes: Bytes<32>;
}

export type PublicAddress = Either<ContractAddress, UserAddress>;

export struct ZswapCoinPublicKey {
  bytes: Bytes<32>;
}

export struct ShieldedCoinInfo {
  nonce: Bytes<32>;
  color: Bytes<32>;
  value: Uint<128>;
}

export struct QualifiedShieldedCoinInfo {
  nonce: Bytes<32>;
  color: Bytes<32>;
  value: Uint<128>;
  mt_index: Uint<64>;
}

export struct ShieldedSendResult {
  change: Maybe<ShieldedCoinInfo>;
  sent: ShieldedCoinInfo;
}

export circuit nativeToken(): Bytes<32> {
  return pad(32, "");
}

export circuit tokenType(domain_sep: Bytes<32>, contractAddress: ContractAddress): Bytes<32> {
  return persistentCommit<Vector<2, Bytes<32>>>(
    [domain_sep, contractAddress.bytes],
    pad(32, "midnight:derive_token")
  );
}

export circuit evolveNonce(index: Uint<128>, nonce: Bytes<32>): Bytes<32> {
  return upgradeFromTransient(transientHash<Vector<3, Field>>([
    "midnight:kernel:nonce_evolve" as Field,
    index as Field,
    degradeToTransient(nonce)
  ]));
}

export circuit shieldedBurnAddress(): Either<ZswapCoinPublicKey, ContractAddress> {
  return left<ZswapCoinPublicKey, ContractAddress>(default<ZswapCoinPublicKey>);
}

struct CoinPreimage {
  domain_sep: Bytes<21>;
  info: ShieldedCoinInfo;
  dataType: Boolean;
  data: Bytes<32>;
}

circuit downcastQualifiedCoin(coin: QualifiedShieldedCoinInfo): ShieldedCoinInfo {
  return ShieldedCoinInfo{ nonce: coin.nonce, color: coin.color, value: coin.value };
}

circuit upcastQualifiedCoin(coin: ShieldedCoinInfo): QualifiedShieldedCoinInfo {
  return QualifiedShieldedCoinInfo{ nonce: coin.nonce, color: coin.color, value: coin.value, mt_index: 0 };
}

circuit coinCommitment(
  coin: ShieldedCoinInfo,
  recipient: Either<ZswapCoinPublicKey, ContractAddress>
): Bytes<32> {
  return persistentHash<CoinPreimage>(CoinPreimage{
    domain_sep: "midnight:zswap-cc[v1]",
    info: coin,
    dataType: recipient.is_left,
    data: recipient.is_left ? recipient.left.bytes : recipient.right.bytes
  });
}

circuit coinNullifier(
  coin: ShieldedCoinInfo,
  addr: ContractAddress
): Bytes<32> {
  return persistentHash<CoinPreimage>(CoinPreimage{
    domain_sep: "midnight:zswap-cn[v1]",
    info: coin,
    dataType: false,
    data: addr.bytes
  });
}

export circuit mintShieldedToken(
  domain_sep: Bytes<32>,
  value: Uint<64>,
  nonce: Bytes<32>,
  recipient: Either<ZswapCoinPublicKey, ContractAddress>
): ShieldedCoinInfo {
  const coin = ShieldedCoinInfo{ nonce: nonce, color: tokenType(domain_sep, kernel.self()), value: value };
  kernel.mintShielded(domain_sep, value);
  createZswapOutput(coin, recipient);
  const cm = coinCommitment(coin, recipient);
  kernel.claimZswapCoinSpend(cm);
  if (!recipient.is_left && recipient.right.bytes == kernel.self().bytes) {
    kernel.claimZswapCoinReceive(cm);
  }
  return coin;
}

export circuit receiveShielded(coin: ShieldedCoinInfo): [] {
  const recipient = right<ZswapCoinPublicKey, ContractAddress>(kernel.self());
  createZswapOutput(coin, recipient);
  kernel.claimZswapCoinReceive(coinCommitment(coin, recipient));
}

export circuit sendShielded(
  input: QualifiedShieldedCoinInfo,
  recipient: Either<ZswapCoinPublicKey, ContractAddress>,
  value: Uint<128>
): ShieldedSendResult {
  const selfAddr = kernel.self();
  createZswapInput(input);
  kernel.claimZswapNullifier(coinNullifier(downcastQualifiedCoin(input), selfAddr));
  const change = input.value - value;
  const output = ShieldedCoinInfo{
    nonce: upgradeFromTransient(transientHash<Vector<2, Field>>([
      "midnight:kernel:nonce_evolve" as Field,
      degradeToTransient(input.nonce)
    ])),
    color: input.color,
    value: value
  };
  createZswapOutput(output, recipient);
  kernel.claimZswapCoinSpend(coinCommitment(output, recipient));
  if (!recipient.is_left && recipient.right.bytes == selfAddr.bytes) {
    kernel.claimZswapCoinReceive(coinCommitment(output, recipient));
  }
  if (change == 0) {
    return ShieldedSendResult{ change: none<ShieldedCoinInfo>(), sent: output };
  } else {
    const changeCoin = ShieldedCoinInfo{
      nonce: upgradeFromTransient(transientHash<Vector<2, Field>>([
        "midnight:kernel:nonce_evolve/2" as Field,
        degradeToTransient(input.nonce)
      ])),
      color: input.color,
      value: change
    };
    createZswapOutput(changeCoin, right<ZswapCoinPublicKey, ContractAddress>(selfAddr));
    const cm = coinCommitment(changeCoin, right<ZswapCoinPublicKey, ContractAddress>(selfAddr));
    kernel.claimZswapCoinSpend(cm);
    kernel.claimZswapCoinReceive(cm);
    return ShieldedSendResult{ change: some<ShieldedCoinInfo>(changeCoin), sent: output };
  }
}

export circuit sendImmediateShielded(
  input: ShieldedCoinInfo,
  target: Either<ZswapCoinPublicKey, ContractAddress>,
  value: Uint<128>
): ShieldedSendResult {
  return sendShielded(upcastQualifiedCoin(input), target, value);
}

export circuit mergeCoin(
  a: QualifiedShieldedCoinInfo,
  b: QualifiedShieldedCoinInfo
): ShieldedCoinInfo {
  const selfAddr = kernel.self();
  createZswapInput(a);
  kernel.claimZswapNullifier(coinNullifier(downcastQualifiedCoin(a), selfAddr));
  createZswapInput(b);
  kernel.claimZswapNullifier(coinNullifier(downcastQualifiedCoin(b), selfAddr));
  assert(a.color == b.color, "Can only merge coins of the same color");
  const newCoin = ShieldedCoinInfo{
    nonce: upgradeFromTransient(transientHash<Vector<2, Field>>([
      "midnight:kernel:nonce_evolve" as Field,
      degradeToTransient(a.nonce)
    ])),
    color: a.color,
    value: (a.value + b.value) as Uint<128>
  };
  createZswapOutput(newCoin, right<ZswapCoinPublicKey, ContractAddress>(selfAddr));
  const cm = coinCommitment(newCoin, right<ZswapCoinPublicKey, ContractAddress>(selfAddr));
  kernel.claimZswapCoinSpend(cm);
  kernel.claimZswapCoinReceive(cm);
  return newCoin;
}

export circuit mergeCoinImmediate(
  a: QualifiedShieldedCoinInfo,
  b: ShieldedCoinInfo
): ShieldedCoinInfo {
  return mergeCoin(a, upcastQualifiedCoin(b));
}

export circuit blockTimeLt(time: Uint<64>): Boolean {
  return kernel.blockTimeLessThan(time);
}

export circuit blockTimeGte(time: Uint<64>): Boolean {
  return !blockTimeLt(time);
}

export circuit blockTimeGt(time: Uint<64>): Boolean {
  return kernel.blockTimeGreaterThan(time);
}

export circuit blockTimeLte(time: Uint<64>): Boolean {
  return !blockTimeGt(time);
}

export circuit mintUnshieldedToken(
  domainSep: Bytes<32>,
  amount: Uint<64>,
  recipient: Either<ContractAddress, UserAddress>
): Bytes<32> {
  kernel.mintUnshielded(domainSep, amount);
  const color = tokenType(domainSep, kernel.self());
  kernel.claimUnshieldedCoinSpend(left<Bytes<32>, Bytes<32>>(color), recipient, amount);
  if (recipient.is_left && recipient.left.bytes == kernel.self().bytes) {
    kernel.incUnshieldedInputs(left<Bytes<32>, Bytes<32>>(color), amount);
  }
  return color;
}

export circuit sendUnshielded(
  color: Bytes<32>,
  amount: Uint<128>,
  recipient: Either<ContractAddress, UserAddress>
): [] {
  kernel.incUnshieldedOutputs(left<Bytes<32>, Bytes<32>>(color), amount);
  kernel.claimUnshieldedCoinSpend(left<Bytes<32>, Bytes<32>>(color), recipient, amount);
  if (recipient.is_left && recipient.left.bytes == kernel.self().bytes) {
    kernel.incUnshieldedInputs(left<Bytes<32>, Bytes<32>>(color), amount);
  }
}

export circuit receiveUnshielded(color: Bytes<32>, amount: Uint<128>): [] {
  kernel.incUnshieldedInputs(left<Bytes<32>, Bytes<32>>(color), amount);
}

export circuit unshieldedBalance(color: Bytes<32>): Uint<128> {
  return kernel.balance(left<Bytes<32>, Bytes<32>>(color));
}

export circuit unshieldedBalanceLt(color: Bytes<32>, amount: Uint<128>): Boolean {
  return kernel.balanceLessThan(left<Bytes<32>, Bytes<32>>(color), amount);
}

export circuit unshieldedBalanceGte(color: Bytes<32>, amount: Uint<128>): Boolean {
  return !unshieldedBalanceLt(color, amount);
}

export circuit unshieldedBalanceGt(color: Bytes<32>, amount: Uint<128>): Boolean {
  return kernel.balanceGreaterThan(left<Bytes<32>, Bytes<32>>(color), amount);
}

export circuit unshieldedBalanceLte(color: Bytes<32>, amount: Uint<128>): Boolean {
  return !unshieldedBalanceGt(color, amount);
}
"#;
