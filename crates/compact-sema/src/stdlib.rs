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

export struct JubjubSchnorrSignature {
  announcement: JubjubPoint;
  response: Field;
}

struct JubjubSchnorrHashInput<#N> {
  annX: Field;
  annY: Field;
  pkX: Field;
  pkY: Field;
  msg: Vector<N, Field>;
}

export circuit jubjubSchnorrVerify<#N>(
  msg: Vector<N, Field>,
  signature: JubjubSchnorrSignature,
  pk: JubjubPoint
): Boolean {
  assert(pk != default<JubjubPoint>, "JubjubPoint identity is not a permitted jubjubSchnorrVerify verification key");
  const { announcement, response } = signature;
  const cNative = transientHash<JubjubSchnorrHashInput<N>>(
    JubjubSchnorrHashInput<N> {
      annX: jubjubPointX(announcement),
      annY: jubjubPointY(announcement),
      pkX: jubjubPointX(pk),
      pkY: jubjubPointY(pk),
      msg: msg
    }
  );
  const c = cNative as JubjubScalar;
  const lhs = ecMulGenerator(response as JubjubScalar);
  const rhs = ecAdd(announcement, ecMul(pk, c));
  return lhs == rhs;
}

export struct Secp256k1EcdsaSignature {
  r: Secp256k1Scalar;
  s: Secp256k1Scalar;
}

circuit reverseBytes32(b: Bytes<32>): Bytes<32> {
  const v = b as Vector<32, Uint<8>>;
  return Bytes[
    v[31], v[30], v[29], v[28], v[27], v[26], v[25], v[24],
    v[23], v[22], v[21], v[20], v[19], v[18], v[17], v[16],
    v[15], v[14], v[13], v[12], v[11], v[10], v[9],  v[8],
    v[7],  v[6],  v[5],  v[4],  v[3],  v[2],  v[1],  v[0]
  ];
}

export circuit secp256k1EcdsaVerify(
  msgHash: Bytes<32>,
  sig: Secp256k1EcdsaSignature,
  pk: Secp256k1Point
): Boolean {
  assert(pk != default<Secp256k1Point>, "Secp256k1Point identity is not a permitted secp256k1EcdsaVerify verification key");
  const z: Secp256k1Scalar = reverseBytes32(msgHash) as Secp256k1Scalar;
  const { r, s } = sig;
  const w: Secp256k1Scalar = inv(s);
  const u1: Secp256k1Scalar = z * w;
  const u2: Secp256k1Scalar = r * w;
  const point: Secp256k1Point = ecAdd(ecMulGenerator(u1), ecMul(pk, u2));
  return (secp256k1PointX(point) as Bytes<32>) as Secp256k1Scalar == r;
}

circuit secp256k1BaseBigEndian(b: Secp256k1Base): Vector<32, Uint<8>> {
  const vec = b as Bytes<32> as Vector<32, Uint<8>>;
  return [
    vec[31], vec[30], vec[29], vec[28], vec[27], vec[26], vec[25], vec[24],
    vec[23], vec[22], vec[21], vec[20], vec[19], vec[18], vec[17], vec[16],
    vec[15], vec[14], vec[13], vec[12], vec[11], vec[10], vec[9],  vec[8],
    vec[7],  vec[6],  vec[5],  vec[4],  vec[3],  vec[2],  vec[1],  vec[0]
  ];
}

export circuit secp256k1EthereumAddress(pk: Secp256k1Point): Bytes<20> {
  assert(pk != default<Secp256k1Point>, "Secp256k1Point identity is not a permitted input to secp256k1EthereumAddress");
  const hash = keccak256<[Vector<32, Uint<8>>, Vector<32, Uint<8>>]>([
    secp256k1BaseBigEndian(secp256k1PointX(pk)),
    secp256k1BaseBigEndian(secp256k1PointY(pk))
  ]);
  return slice<20>(hash, 12);
}

export struct Secp256r1EcdsaSignature {
  r: Secp256r1Scalar;
  s: Secp256r1Scalar;
}

export circuit secp256r1EcdsaVerify(
  msgHash: Bytes<32>,
  sig: Secp256r1EcdsaSignature,
  pk: Secp256r1Point
): Boolean {
  assert(pk != default<Secp256r1Point>, "Secp256r1Point identity is not a permitted secp256r1EcdsaVerify verification key");
  const z: Secp256r1Scalar = reverseBytes32(msgHash) as Secp256r1Scalar;
  const { r, s } = sig;
  const w: Secp256r1Scalar = inv(s);
  const u1: Secp256r1Scalar = z * w;
  const u2: Secp256r1Scalar = r * w;
  const point: Secp256r1Point = ecAdd(ecMulGenerator(u1), ecMul(pk, u2));
  return (secp256r1PointX(point) as Bytes<32>) as Secp256r1Scalar == r;
}

export struct Ed25519Signature {
  r: Curve25519Point;
  s: Curve25519Scalar;
}

circuit curve25519BaseIsOdd(x: Curve25519Base): Boolean {
  const b = (x as Bytes<32> as Vector<32, Uint<8>>)[0];
  const b6 = b  >= 128 ? b  - 128 : b;
  const b5 = b6 >= 64  ? b6 - 64  : b6;
  const b4 = b5 >= 32  ? b5 - 32  : b5;
  const b3 = b4 >= 16  ? b4 - 16  : b4;
  const b2 = b3 >= 8   ? b3 - 8   : b3;
  const b1 = b2 >= 4   ? b2 - 4   : b2;
  return (b1 >= 2 ? b1 - 2 : b1) == 1;
}

circuit ed25519Encode(p: Curve25519Point): Bytes<32> {
  const y = curve25519PointY(p) as Bytes<32> as Vector<32, Uint<8>>;
  const sign = curve25519BaseIsOdd(curve25519PointX(p)) ? 128 : 0;
  return Bytes[
    y[0],  y[1],  y[2],  y[3],  y[4],  y[5],  y[6],  y[7],
    y[8],  y[9],  y[10], y[11], y[12], y[13], y[14], y[15],
    y[16], y[17], y[18], y[19], y[20], y[21], y[22], y[23],
    y[24], y[25], y[26], y[27], y[28], y[29], y[30],
    (y[31] + sign) as Uint<8>
  ];
}

export circuit ed25519Verify<#n>(
  msg: Bytes<n>,
  sig: Ed25519Signature,
  pk: Curve25519Point
): Boolean {
  assert((curve25519PointX(pk) as Bytes<32>) != pad(32, ""), "Curve25519Point identity is not a permitted ed25519Verify verification key");
  const { r, s } = sig;
  const k = sha512<[Bytes<32>, Bytes<32>, Bytes<n>]>([
    ed25519Encode(r),
    ed25519Encode(pk),
    msg
  ]) as Curve25519Scalar;
  return ecMulGenerator(s) == ecAdd(r, ecMul(pk, k));
}

export struct ShieldedSpend {
  nullifier: Bytes<32>;
}

export struct ShieldedReceive {
  commitment: Bytes<32>;
  ciphertext: Maybe<Bytes<512>>;
  contractAddress: Maybe<Bytes<32>>;
}

export struct ShieldedMint {
  commitment: Bytes<32>;
  domainSep: Bytes<32>;
  amount: Maybe<Uint<128>>;
}

export struct ShieldedBurn {
  nullifier: Bytes<32>;
  amount: Maybe<Uint<128>>;
}

export struct UnshieldedSpend {
  sender: Either<ZswapCoinPublicKey, ContractAddress>;
  domainSep: Bytes<32>;
  tokenType: Bytes<32>;
  amount: Uint<128>;
}

export struct UnshieldedReceive {
  recipient: Either<ZswapCoinPublicKey, ContractAddress>;
  domainSep: Bytes<32>;
  tokenType: Bytes<32>;
  amount: Uint<128>;
}

export struct UnshieldedMint {
  domainSep: Bytes<32>;
  tokenType: Bytes<32>;
  amount: Uint<128>;
}

export struct UnshieldedBurn {
  sender: Either<ZswapCoinPublicKey, ContractAddress>;
  tokenType: Bytes<32>;
  amount: Uint<128>;
}

export struct Paused {
}

export struct Unpaused {
}

export struct Misc {
  name: Bytes<32>;
  payload: Bytes<256>;
}
"#;
