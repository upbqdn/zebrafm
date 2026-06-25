# Future verification roadmap

A survey of Zebra's verification surface beyond what this repo currently
covers. Each item is sized by rough engineering effort.

## What's already verified

In rough order of how it grew here (not effort order):

- `Height` arithmetic, `Amount` arithmetic, `CompactSize64` serialisation
  (plus canonicity), `NetworkUpgrade` activation (mainnet count form),
  `LockTime` serialisation, `halving` / `block_subsidy` (post-Blossom core),
  `ZIP-317` conventional fee, `CONSENSUS_BRANCH_IDS` table integrity.

## Tractable next phases (one focused session each)

### Block validation arithmetic

1. **Block size limits** — `MAX_BLOCK_BYTES = 2 MB`,
   `MAX_PROTOCOL_MESSAGE_LEN`. Boolean predicates plus a few inequalities.
   Source: `zebra-chain/src/serialization/constraint.rs`.
2. **Coinbase-output spend maturity** — `MIN_TRANSPARENT_COINBASE_MATURITY = 100`.
   Height comparison + transition rule. Source:
   `zebra-chain/src/transparent.rs`.
3. **Block-max-time-in-the-future** — `MAX_BLOCK_TIME_TOLERANCE = 7200s`.
   Trivial inequality but consensus-critical.

### Subsidy completeness

4. **Founders reward / funding stream allocation** — splits the block
   subsidy across miner + founders + funding streams per network upgrade.
   Source: `zebra-chain/src/parameters/network/subsidy.rs:484`
   (`miner_subsidy`) and friends. ~10 theorems including monotonicity
   across halvings and conservation (sum equals total).
5. **Pre-Blossom subsidy ramp** — the slow-start interval our current
   `Subsidy.lean` skips. Source: same file.

### Difficulty

6. **`CompactDifficulty::to_expanded` / `to_compact`** (phase 4 from the
   original proposal). 256-bit bitfield reasoning, the hardest non-cryptographic
   target.
7. **Difficulty adjustment algorithm (DAA)** — `PoWAveragingWindow = 17`,
   `PoWMedianBlockSpan = 11`. Median-window computation; structurally
   like LockTime but with more bookkeeping.

### Serialisation

8. **Block header serialisation** — Bitcoin-style 80-byte header with
   version, prev_hash, merkle_root, time, bits, nonce. Round-trip
   identical in shape to LockTime.
9. **Transaction serialisation (v4, v5, v6)** — substantially bigger:
   tagged unions, variable-length pool data. Each version is its own
   round-trip proof. The roadmap's phase 8 (Merkle on transactions)
   depends on this.
10. **Bech32 / bech32m address encoding** — BIP-173 polynomial check,
    well-defined arithmetic over GF(32). Self-contained.
11. **Sapling / Orchard nullifier and commitment round-trip** — 32-byte
    primitives, trivial round-trip but pinpointed consensus properties.

### Network / mempool

12. **`addr` / `getdata` / `inv` message bounded sizes** —
    `MAX_ADDR_MESSAGE_ENTRIES = 1000`,
    `MAX_INV_MESSAGE_ENTRIES = 50000`. DoS-cap proofs.
    Source: `zebra-network/src/protocol/external/message.rs`.
13. **Network version negotiation** — `INITIAL_MIN_NETWORK_PROTOCOL_VERSION`
    progression.
14. **Mempool admission rule** — ZIP-317 unpaid actions ≤
    `BLOCK_UNPAID_ACTION_LIMIT`.

### State

15. **Reorg window** — `MAX_BLOCK_REORG_HEIGHT = 1000`. The recently-bumped
    rollback bound; closure under add/remove of finalised blocks.
    Source: `zebra-chain/src/parameters/constants.rs:30`.
16. **History tree update** — the Mountain Merkle structure on block
    headers. Append-only invariants; the `try_extend` round-trip would
    mirror our existing Sub round-trip.

### Cryptographic primitives (separate engagement-sized)

17. **Pedersen / sinsemilla commitments** — group arithmetic over Pallas.
    Requires modelling an elliptic curve abstractly. Substantial.
18. **Sapling / Orchard incremental Merkle trees** — phase 8 from the
    original proposal. Tree append + path verification.
19. **ZIP-244 sighash** — txid + sighash derivation for v5/v6 transactions.
    Hash function modelling required.
20. **Sapling and Orchard circuits** — requires modelling Halo2 / Groth16
    constraint systems. Almost certainly a separate, large engagement.

### Beyond `zebra-chain`

21. **`zebra-script` FFI** — script validation boundary. Modelling C++
    interop is hard; the consensus surface is just "did the script
    return TRUE?".
22. **`zebra-state` durable migrations** — disk-format upgrade safety.
    Per-version semantics, requires modelling RocksDB column families.
23. **`zebra-rpc` JSON encoding** — zcashd-compatibility round-trip for
    common methods (`getblockchaininfo`, `getblock`, etc.).

## Notes on prioritisation

- **For consensus risk**: items 6 (CompactDifficulty), 9 (transaction
  serialisation), 4 (subsidy allocation), 16 (history tree) are highest
  risk — bugs become chain splits.
- **For tractability with the current pipeline**: items 1–3, 8, 10, 12,
  14, 15 are all close to the difficulty profile of the work already done.
- **For grant-proposal alignment**: items 6, 9, 16 complete phases 4 and 8
  of the original ZCG #324 roadmap.
- **For ecosystem outreach**: item 23 (RPC JSON) produces artifacts
  external consumers can use immediately.

## Methodology gaps still open

- **Drift detection on items not in `rust-crate/`.** The current
  `drift-check.yml` only anchors three files. As new modules are added to
  `rust-crate/`, the anchors set needs to grow.
- **Aeneas re-extraction in CI is slow** (~30 min cold). A nightly build
  + cache would amortise this.
- **Coq backend has one representative proof.** Re-proving every Lean
  theorem in Coq would diversify the foundational trust claim end-to-end.
- **`zebra-chain` integration tests** that depend on the real upstream
  crate would catch the `rust-crate ↔ upstream` semantic gap that diff-
  anchoring catches only at the source-text level.
