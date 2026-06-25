# Findings

This document summarises 207 structured findings produced by a 7-wave parallel adversarial review of 62 Lean modules / 1004 theorems verifying the `zebra-chain` crate. Severity distribution: **15 critical**, **42 high**, **62 medium**, **74 low**, and **14 informational / positive-confirmation**.

How to use: Critical and high findings should be triaged before publishing the verification results. Several are Rust-vs-Lean semantic mismatches that mean the stated theorems do not pin the behaviour they claim to. Medium and low findings are mostly hidden trivialities, incomplete coverage, and stale citations into the Rust source. Informational findings record places where the verification meaningfully confirms a non-obvious invariant.

## Critical / High severity

### Finding 1: Subsidy.POST_BLOSSOM_HALVING_INTERVAL is wrong by 2x
- **Module:** Subsidy
- **Category:** rust-lean-mismatch
- **Summary:** `Subsidy.POST_BLOSSOM_HALVING_INTERVAL = 840_000`; Rust uses `1_680_000` (= `PRE_BLOSSOM * BLOSSOM_POW_TARGET_SPACING_RATIO`). Sibling `Zip1014Devfund` uses the correct value, so the project is internally inconsistent.
- **Evidence:** `Subsidy.lean:35` vs Rust `zebra-chain/src/parameters/network/subsidy/constants.rs:25-29`. Affects T4, T9, T10.
- **Recommended action:** Fix the constant; rerun affected theorems; add a cross-module sanity theorem `Subsidy.POST_BLOSSOM_HALVING_INTERVAL = Zip1014Devfund.POST_BLOSSOM_HALVING_INTERVAL`.

### Finding 2: Subsidy.halving omits slow_start_shift and post-Blossom scaling
- **Module:** Subsidy
- **Category:** rust-lean-mismatch
- **Summary:** `halving(h)` returns 0 below Blossom and a plain quotient above; Rust uses a 3-branch function with slow-start offset and post-Blossom scaling. At Canopy, Rust returns 1; Lean returns 0.
- **Evidence:** `Subsidy.lean:48-50` vs Rust `subsidy.rs:422-446`.
- **Recommended action:** Rewrite `halving` to mirror the Rust 3-branch shape; pin `halving Canopy = 1`; re-evaluate downstream theorems.

### Finding 3: Subsidy.blockSubsidy never applies post-Blossom 2x halving
- **Module:** Subsidy
- **Category:** rust-lean-mismatch
- **Summary:** Missing `base_subsidy = MAX_BLOCK_SUBSIDY / 2 if post-Blossom else MAX_BLOCK_SUBSIDY` step. Every post-Blossom `blockSubsidy` is 2x too large.
- **Evidence:** `Subsidy.lean:59-62` vs Rust `subsidy.rs:469-475`. T8/T9/T10 off by 2x.
- **Recommended action:** Introduce `baseSubsidy(h)` helper; update concrete vectors (`T8 = 625_000_000`, `T9 = 312_500_000`).

### Finding 4: TestnetMinDifficulty assumes Blossom-first on testnet
- **Module:** TestnetMinDifficulty
- **Category:** rust-lean-mismatch
- **Summary:** Lean hard-codes 450s for all heights ≥ 299_188. Blossom activates on testnet at 584_000, so Rust returns 900s for the ~285k blocks in `[299_188, 584_000)`.
- **Evidence:** `TestnetMinDifficulty.lean:60-72`, T6/T9. Rust `network_upgrade.rs:445-462`.
- **Recommended action:** Parameterise threshold by `current_upgrade(h, testnet)`; prove the two-region split.

### Finding 5: DAAMedianWindow clamp uses symmetric 0.5x/2x bounds
- **Module:** DAAMedianWindow
- **Category:** rust-lean-mismatch
- **Summary:** Lean uses `[ideal/2, ideal*2]`. ZIP-208 uses asymmetric `avg * 84/100` (up) and `avg * 132/100` (down). Lean is ~4x looser per side and omits `PoWDampingFactor = 4` damping.
- **Evidence:** `DAAMedianWindow.lean:36-41,95-96` vs Rust `difficulty.rs:38-43,291-300`.
- **Recommended action:** Re-derive clamp from `POW_MAX_ADJUST_UP/DOWN_PERCENT` and damping factor 4; refactor T3/T4/T5/T9. AUDIT.md C-6; likely needs U256 model.

### Finding 6: DAAMedianWindow.mean17 averages timestamps, not difficulties
- **Module:** DAAMedianWindow
- **Category:** rust-lean-mismatch
- **Summary:** `mean17` averages timestamps; Rust's `MeanTarget` averages 17 `ExpandedDifficulty` (U256) target thresholds. Modelled domain mismatches consensus quantity.
- **Evidence:** `DAAMedianWindow.lean:35,83-86` vs Rust `difficulty.rs:230,248-258`. Test vectors T13/T14 cement wrong interpretation.
- **Recommended action:** Refactor: model `MeanTarget` over U256 abstraction; rename current function to `meanTimestamp` or delete.

### Finding 7: DAAMedianWindow.medianOf11 returns 0 for non-length-11 inputs
- **Module:** DAAMedianWindow
- **Category:** incomplete-coverage
- **Summary:** Rust's `median_time` accepts any non-empty `Vec` of length `1..=11`; Lean returns 0 outside length-11, masking boot-up semantics.
- **Evidence:** `DAAMedianWindow.lean:72-75` vs Rust `difficulty.rs:349-364`.
- **Recommended action:** Generalise to accept `1..=11`; add partial-context theorems.

### Finding 8: DAAMedianWindow omits ActualTimespan, damping, and PoWLimit cap
- **Module:** DAAMedianWindow
- **Category:** incomplete-coverage
- **Summary:** No `actualTimespan`, no `dampedVariance`, no PoWLimit cap. Module title implies `ThresholdBits` semantics but pieces are isolated.
- **Evidence:** Rust `difficulty.rs:213-224,276-301`. AUDIT.md C-6.
- **Recommended action:** Add the three missing functions; reorganise as `ThresholdBits`.

### Finding 9: CompactDifficulty.toCompact is bit-packing, not the Rust shape
- **Module:** CompactDifficulty
- **Category:** incomplete-coverage
- **Summary:** Lean `toCompact (m size) = m + size * 2^24` skips Rust's `size = self.0.bits() / 8 + 1` derivation and the conditional shift step.
- **Evidence:** `CompactDifficulty.lean:119-120` vs Rust `difficulty.rs:460-507`.
- **Recommended action:** Rewrite to model full pipeline, or rename to `assembleCompact` with explicit caveat.

### Finding 10: CompactDifficulty.isCanonical excludes the wrong size bytes
- **Module:** CompactDifficulty
- **Category:** wrong-brief-corrected
- **Summary:** Docstring excludes `sizeByte ∈ {30, 31}` for normalisation; the Rust normalisation fires on exponent `e ∈ {30, 31}` corresponding to size bytes 33 and 34 (off by `OFFSET=3`).
- **Evidence:** `CompactDifficulty.lean:37-40,91-95` vs Rust `difficulty.rs:211,218-227`.
- **Recommended action:** Fix docstring; widen `isCanonical` to allow size bytes 30 and 31.

### Finding 11: EquihashSolution.decode accepts any in-range length
- **Module:** EquihashSolution
- **Category:** rust-lean-mismatch
- **Summary:** Lean accepts any length in `[0, SOLUTION_SIZE]`; Rust rejects everything other than 1344 or 36.
- **Evidence:** `EquihashSolution.lean:85-94` vs Rust `equihash.rs:96-113,263-280`.
- **Recommended action:** Tighten `decode` to two canonical sizes; add regtest variant.

### Finding 12: EquihashSolution omits the Regtest variant
- **Module:** EquihashSolution
- **Category:** incomplete-coverage
- **Summary:** Single variant in Lean; Rust is 2-variant enum discriminated by length.
- **Evidence:** `EquihashSolution.lean:48-49` vs Rust `equihash.rs:47-52`.
- **Recommended action:** Add `Solution.regtest` variant with parallel theorems.

### Finding 13: EquihashParams.collisionCount is invented terminology
- **Module:** EquihashParams
- **Category:** spec-ambiguity
- **Summary:** `collisionCount k := 2^(k+1)` is not an Equihash quantity. Six of 21 theorems operate on this fiction.
- **Evidence:** `EquihashParams.lean:97-99`; Rust `equihash.rs:76-78` has no such concept.
- **Recommended action:** Delete or rename and rederive against the real Equihash item-count formula.

### Finding 14: Amount.sumFold is right-fold, Rust is left-fold try_fold
- **Module:** Amount
- **Category:** rust-lean-mismatch
- **Summary:** Right-fold vs left-fold with short-circuit. AUDIT.md acknowledges as partial.
- **Evidence:** `Amount.lean:184-189` vs Rust `amount.rs:430`.
- **Recommended action:** Add a `tryFoldLeft` model.

### Finding 15: NetworkUpgrade enum omits Nu7
- **Module:** NetworkUpgrade
- **Category:** incomplete-coverage
- **Summary:** Lean enumerates 11 variants; Rust has `Nu7` with test-only branch id. Any `current()` / `branch_id()` involving Nu7 unmodeled.
- **Evidence:** `NetworkUpgrade.lean:26-39` vs Rust `network_upgrade.rs:66,237,404`.
- **Recommended action:** Add `nu7`; extend `current`, `toOrd`, `currentOrd`, and bridge with 12th band.

### Finding 16: FoundersReward uses silent floor division, not div_exact
- **Module:** FoundersReward
- **Category:** rust-lean-mismatch
- **Summary:** Lean `subsidy / 5` (silent floor); Rust `div_exact(5)` panics on non-divisibility.
- **Evidence:** `FoundersReward.lean:46-49` vs Rust `subsidy.rs:547`, `amount.rs:79-86`.
- **Recommended action:** Replace with Option-typed `divExact5`; add `subsidy % 5 = 0` invariant.

### Finding 17: Zip1014Devfund T10 docstring conflates first and second halving
- **Module:** Zip1014Devfund
- **Category:** spec-ambiguity
- **Summary:** T10 calls `DEV_FUND_END_HEIGHT = 2_726_400` "the first halving"; the first halving is Canopy = 1_046_400. T11 inherits the off-by-one.
- **Evidence:** `Zip1014Devfund.lean:309-323,328-330` vs Rust `subsidy.rs:239-257,307`.
- **Recommended action:** Rewrite docstrings; introduce `halving DEV_FUND_END_HEIGHT = 1` lemma.

### Finding 18: Zip1015FundingStreams.share_constant_in_range is rfl
- **Module:** Zip1015FundingStreams
- **Category:** hidden-triviality
- **Summary:** T10 claims height-independence; actual statement is `share s e r = share s e r` proved by `rfl`. Hypotheses `_h1, _h2` unused.
- **Evidence:** `Zip1015FundingStreams.lean:250-254`.
- **Recommended action:** Restate as `∀ h1 h2, in_range h1 ∧ in_range h2 → share s Era.postNu6 r at h1 = share s Era.postNu6 r at h2`.

### Finding 19: Zip2001Lockbox.minerPerBlock pays both dev fund and lockbox
- **Module:** Zip2001Lockbox
- **Category:** rust-lean-mismatch
- **Summary:** Lean treats both streams as active simultaneously; Rust defines them in disjoint height ranges.
- **Evidence:** `Zip2001Lockbox.lean:117-118,204-232,333` vs Rust `mainnet.rs:192-243`.
- **Recommended action:** Add height parameter or epoch tag; restate conservation per-height.

### Finding 20: Bech32 polymod skips GEN[i] mixing entirely
- **Module:** Bech32
- **Category:** hidden-triviality
- **Summary:** `polymod` step is `((c * 32 + v) % 2^30)` — no XOR, no GEN reference. T1-T5 are properties of any fold.
- **Evidence:** `Bech32.lean:50-51,65,21-23`.
- **Recommended action:** Model GF(32) XOR-with-GEN[i] faithfully, or remove BIP-173 references.

### Finding 21: Bech32.encode_injective_data is generic list cancellation
- **Module:** Bech32
- **Category:** hidden-triviality
- **Summary:** T10 is `List.append_cancel_left/right`; vacuous for any prefix/suffix concatenation.
- **Evidence:** `Bech32.lean:181-199`.
- **Recommended action:** Restate with real checksum dependency.

### Finding 22: Bech32 has no decode-and-verify theorem
- **Module:** Bech32
- **Category:** incomplete-coverage
- **Summary:** No `decode`, no `verify_checksum`. BIP-173 central property absent.
- **Evidence:** AUDIT.md:174-176; `Bech32.lean` has no decoder.
- **Recommended action:** Implement `decode` and `verify_checksum`.

### Finding 23: Bip34CoinbaseHeight rejects valid length-5 prefix
- **Module:** Bip34CoinbaseHeight
- **Category:** rust-lean-mismatch
- **Summary:** Lean rejects prefix byte 5 at parse layer; Rust accepts `n @ 1..=5`.
- **Evidence:** `Bip34CoinbaseHeight.lean:80-112` vs Rust `transparent/serialize.rs:68`.
- **Recommended action:** Add length-5 parse arm; restate T13 in canonicity terms.

### Finding 24: BlockHeader has no decoder or version-check rejection
- **Module:** BlockHeader
- **Category:** incomplete-coverage
- **Summary:** No `decodeFixed`; no encoder↔decoder round-trip; no `check_version` rejection theorem.
- **Evidence:** Rust `block/serialize.rs:86-108`.
- **Recommended action:** Add decoder, roundtrip, and explicit rejection theorems for high-bit-set and `version < 4`.

### Finding 25: TransactionV5Header round-trip accepts any header value
- **Module:** TransactionV5Header
- **Category:** incomplete-coverage
- **Summary:** No `h.header = V5_HEADER` constraint. Streams like `[0x05, 0, 0, 0, ...]` round-trip in Lean; Rust requires the high bit set.
- **Evidence:** `TransactionV5Header.lean:135-149` vs Rust `transaction/serialize.rs:520-523,780`.
- **Recommended action:** Add `WellFormed` predicate `h.header = V5_HEADER ∧ h.versionGroupId = TX_V5_VERSION_GROUP_ID`.

### Finding 26: TransactionMaxSize.MAX_TX_BYTES is invented
- **Module:** TransactionMaxSize
- **Category:** spec-ambiguity
- **Summary:** No `MAX_TX_BYTES` exists in Rust; per-tx byte cap is not enforced. Rust uses bounded reads.
- **Evidence:** `TransactionMaxSize.lean:75-78` vs Rust `transaction/serialize.rs:506-512`.
- **Recommended action:** Rename to `THEORETICAL_TX_BYTES_UPPER_BOUND`; document as derived not enforced.

### Finding 27: NU63IronwoodLayout.FlagsV6 misses the newtype structure
- **Module:** NU63IronwoodLayout
- **Category:** rust-lean-mismatch
- **Summary:** Lean struct with three Booleans; Rust is a newtype `FlagsV6(Flags)` with `From` impl and `Flags::from_byte(b, NU6_3_RESERVED)`.
- **Evidence:** `NU63IronwoodLayout.lean:103-107` vs PR #10762 `orchard/shielded_data.rs`.
- **Recommended action:** Refactor as newtype; add parser-level round-trip theorem.

### Finding 28: NU6_3 activation height is a placeholder
- **Module:** NU63IronwoodLayout
- **Category:** wrong-brief-corrected
- **Summary:** `NU6_3 := 3_500_000` is a placeholder; no `NU6_3` exists in Rust. T12-T16 vacuous on mainnet.
- **Evidence:** `NU63IronwoodLayout.lean:88-90`. Rust `parameters/constants.rs:73-95`.
- **Recommended action:** Gate module behind a feature flag.

### Finding 29: NU63IronwoodLayout T1 only covers bit 2 rejection
- **Module:** NU63IronwoodLayout
- **Category:** incomplete-coverage
- **Summary:** Rust `PRE_NU6_3_RESERVED` mask is `0b11111100`, rejecting bits 2..7. Theorems cover only bit 2.
- **Evidence:** `NU63IronwoodLayout.lean:166-176`.
- **Recommended action:** Add general bits-2..7 rejection theorem.

### Finding 30: Zip317.logicalActions is opaque
- **Module:** Zip317
- **Category:** incomplete-coverage
- **Summary:** Lean disavows the actual Rust derivation. Only arithmetic shell modelled.
- **Evidence:** `Zip317.lean:13-17` vs Rust `unmined/zip317.rs:140-170`.
- **Recommended action:** Add structured `LogicalActions` record.

### Finding 31: Zip317 omits mempool_checks and unpaid_actions
- **Module:** Zip317
- **Category:** incomplete-coverage
- **Summary:** `unpaid_actions`, `mempool_checks`, `BLOCK_UNPAID_ACTION_LIMIT`, `MIN_MEMPOOL_TX_FEE_RATE`, `MEMPOOL_TX_FEE_REQUIREMENT_CAP`, kilobyte-rate clamp — all absent.
- **Evidence:** Rust `unmined/zip317.rs:50,59,67,90-106,173-232`; Lean module is 81 lines.
- **Recommended action:** Extend substantially or split into `Zip317.Fee` and `Zip317.Mempool`.

### Finding 32: BlockMaxTime cites a constant that doesn't exist
- **Module:** BlockMaxTime
- **Category:** spec-ambiguity
- **Summary:** `MAX_BLOCK_TIME_TOLERANCE = 7200` is not a Rust constant; Rust uses `chrono::Duration::hours(2)` inline. Citations point to unrelated lines.
- **Evidence:** `BlockMaxTime.lean:25-32` vs Rust `block/header.rs:113`.
- **Recommended action:** Fix citations; note Lean-side label for inline value.

### Finding 33: ReorgWindow models per-block depth, not chain length
- **Module:** ReorgWindow
- **Category:** rust-lean-mismatch
- **Summary:** Lean: `tipHeight - blockHeight ≥ 1000`. Rust: `while best_chain_len() > MAX_BLOCK_REORG_HEIGHT { finalize() }`.
- **Evidence:** `ReorgWindow.lean:38-39` vs Rust `service/write.rs:451-463`.
- **Recommended action:** Rewrite predicate over `chain_len`.

### Finding 34: HashRoundTrip is all identity functions
- **Module:** HashRoundTrip
- **Category:** hidden-triviality
- **Summary:** `fromBytes`, `toBytes`, `zcashSerialize` all `:= bs`. T1, T2, T4, T5, T9 are `rfl`. Round-trip vacuous.
- **Evidence:** `HashRoundTrip.lean:45-47,49-51,62`.
- **Recommended action:** Model `BytesInDisplayOrder` reversal, or delete the module.

### Finding 35: HashRoundTrip omits BytesInDisplayOrder asymmetry
- **Module:** HashRoundTrip
- **Category:** incomplete-coverage
- **Summary:** `block::Hash` is `BytesInDisplayOrder<false>`, `transaction::Hash` is `<true>`. Lean conflates them.
- **Evidence:** Rust `{block,transaction}/hash.rs`.
- **Recommended action:** Add `REVERSED: Bool` parameter; display-order theorems for both.

### Finding 36: CoinbaseMaturity omits DisallowCoinbaseSpend variant
- **Module:** CoinbaseMaturity
- **Category:** incomplete-coverage
- **Summary:** Lean models only `CheckCoinbaseMaturity`. `DisallowCoinbaseSpend` (pre-Heartwood shielded-coinbase rule) absent.
- **Evidence:** Rust `service/check/utxo.rs:215`.
- **Recommended action:** Add the variant and `should_allow_unshielded_coinbase_spends` gate.

### Finding 37: Nullifiers round-trip is rfl on identity
- **Module:** Nullifiers
- **Category:** hidden-triviality
- **Summary:** Sprout/Sapling/Orchard `fromBytes`/`toBytes` identity. T1-T2, T8-T9, T15-T16 are `rfl`. Rust Orchard `TryFrom` rejects non-canonical pallas::Base bytes.
- **Evidence:** `Nullifiers.lean:55-59,77-81,106-110,125-126` vs Rust `orchard/note/nullifiers.rs:19-33`.
- **Recommended action:** Replace identity with canonical-encoding-check function.

### Finding 38: SaplingNoteCommitment.zcashDeserialize accepts non-canonical bytes
- **Module:** SaplingNoteCommitment
- **Category:** rust-lean-mismatch
- **Summary:** Lean length-only check; Rust calls `ExtractedNoteCommitment::from_bytes(&buf).into_option()`.
- **Evidence:** `SaplingNoteCommitment.lean:91-93` vs Rust `sapling/commitment.rs:115-127`.
- **Recommended action:** Add `isCanonicalJubjubBase` predicate.

### Finding 39: SaplingNoteCommitment round-trip is rfl on identity
- **Module:** SaplingNoteCommitment
- **Category:** hidden-triviality
- **Summary:** All encoder/decoder functions identity; T1-T6, T15 `rfl`.
- **Evidence:** `SaplingNoteCommitment.lean:68,75,84,99,104,119-120,124-125,190-193`.
- **Recommended action:** See Finding 38.

### Finding 40: ValueCommitment skips ZIP-216 small-order rejection
- **Module:** ValueCommitment
- **Category:** rust-lean-mismatch
- **Summary:** Lean length-only; Rust Sapling `from_bytes_not_small_order`, Orchard `pallas::Affine::from_bytes`.
- **Evidence:** `ValueCommitment.lean:77-78` vs Rust `sapling/commitment.rs:89-99`, `orchard/commitment.rs:202-214`.
- **Recommended action:** Model small-order subgroup check.

### Finding 41: ValueCommitment.isValidCommitmentBytes is fictional
- **Module:** ValueCommitment
- **Category:** incomplete-coverage
- **Summary:** Docstring promises predicate; grep returns zero hits.
- **Evidence:** `ValueCommitment.lean:74-75`.
- **Recommended action:** Implement or remove docstring promise.

### Finding 42: ValueCommitment round-trip is rfl on identity
- **Module:** ValueCommitment
- **Category:** hidden-triviality
- **Summary:** All encode/decode identity; T1-T2, T5-T6, T11 `rfl`. T15 conflates Sapling reversal with Orchard non-reversal.
- **Evidence:** `ValueCommitment.lean:48,53,59,65,70,84-88,103-109,143-146`.
- **Recommended action:** Model Sapling reversal separately.

### Finding 43: OrchardAnchorBytes.isCanonical is undefined
- **Module:** OrchardAnchorBytes
- **Category:** rust-lean-mismatch
- **Summary:** Docstring claims predicate; grep returns 0 hits. Both `*FromBytes` are identity.
- **Evidence:** `OrchardAnchorBytes.lean:31-39,101,124` vs Rust `{orchard,sapling}/tree.rs:151-165,93-107`.
- **Recommended action:** Implement `isCanonical`; restate 30 theorems under it.

### Finding 44: OrchardAnchorBytes round-trip theorems are rfl
- **Module:** OrchardAnchorBytes
- **Category:** hidden-triviality
- **Summary:** T2-T5, T10-T13, T18-T21, T25 `rfl` over identity. 30 theorems pin 2 non-trivial facts.
- **Evidence:** `OrchardAnchorBytes.lean:95-153,179-194,228-245,288-305,328-331`.
- **Recommended action:** Collapse redundant round-trip theorems; reinvest in canonical-encoding theorems.

### Finding 45: SaplingIncrementalMerkle.DEFAULT_UNCOMMITTED is empty list
- **Module:** SaplingIncrementalMerkle
- **Category:** rust-lean-mismatch
- **Summary:** Lean: `[]`. Rust: `jubjub::Fq::one().to_bytes()` (32 bytes encoding 1).
- **Evidence:** `SaplingIncrementalMerkle.lean:138` vs Rust `sapling/tree.rs:430-432`.
- **Recommended action:** Replace with 32-element list representing LE encoding of 1.

### Finding 46: SaplingIncrementalMerkle.root is a fictional algorithm
- **Module:** SaplingIncrementalMerkle
- **Category:** incomplete-coverage
- **Summary:** `hashLayer` does pair-fold with odd-leaf-kept-as-is; actual Merkle tree pads with uncommitted sentinel.
- **Evidence:** `SaplingIncrementalMerkle.lean:114-128`.
- **Recommended action:** Rewrite to pad with `DEFAULT_UNCOMMITTED`; validate against `Frontier`.

### Finding 47: SaplingIncrementalMerkle.root_deterministic is rfl
- **Module:** SaplingIncrementalMerkle
- **Category:** hidden-triviality
- **Summary:** T13 (`root h u t = root h u t`) `rfl`; T14 congruence; T16 follows from singleton case.
- **Evidence:** `SaplingIncrementalMerkle.lean:239-240,256-261`.
- **Recommended action:** Delete; replace with substantive facts once Finding 46 is addressed.

### Finding 48: OrchardIncrementalMerkle has no root function
- **Module:** OrchardIncrementalMerkle
- **Category:** incomplete-coverage
- **Summary:** Module defines `MerkleScheme` and `Tree.append` but no `Tree.root`.
- **Evidence:** `OrchardIncrementalMerkle.lean:147-163,321-339`.
- **Recommended action:** Add `Tree.root`; tie `append` to root computation.

### Finding 49: HistoryTreeAppendOnly omits the NU-tag panic
- **Module:** HistoryTreeAppendOnly
- **Category:** incomplete-coverage
- **Summary:** Rust `append_leaf` panics when block's NU differs from tree's stored NU. Activation-block tree-reset rule also missing.
- **Evidence:** Rust `primitives/zcash_history.rs:187-192`.
- **Recommended action:** Add NU tag to tree state; add precondition theorems.

### Finding 50: PoolValueBalance.total sums all 5 pools, Rust sums 4
- **Module:** PoolValueBalance
- **Category:** rust-lean-mismatch
- **Summary:** Lean sums 5; Rust `remaining_transaction_value` sums 4 (deferred excluded). T5's bound fictional.
- **Evidence:** `PoolValueBalance.lean:81-83` vs Rust `value_balance.rs:170-177`.
- **Recommended action:** Split `total4` and `total5`; restate against `total4`.

### Finding 51: PoolValueBalance uses Nat, not NegativeAllowed Amount
- **Module:** PoolValueBalance
- **Category:** rust-lean-mismatch
- **Summary:** Sapling `valueBalanceSapling` can be negative. `to_le_bytes` of `-1: i64` is `[0xff; 8]`; Lean's `toLE8` cannot produce this.
- **Evidence:** `PoolValueBalance.lean:57-63` vs Rust `value_balance.rs:22-29`, `amount.rs:109`.
- **Recommended action:** Model `Amount<NegativeAllowed>` as Int; two's-complement LE encoder.

### Finding 52: Zip243SaplingSighash preimage has 12 sections, ZIP-243 has 13
- **Module:** Zip243SaplingSighash
- **Category:** rust-lean-mismatch
- **Summary:** Lean conflates `header` and `nVersionGroupId` into one 4-byte field; ZIP-243 has two separate fields. True preimage 220 + |input| bytes; Lean's 216.
- **Evidence:** `Zip243SaplingSighash.lean:13-26,160-165` vs `zip-0243.rst:43-58`, librustzcash `sighash_v4.rs:149-150`.
- **Recommended action:** Split header section into two 4-byte sections; update T1 and dependents.

### Finding 53: Zip243SaplingSighash ignores hash_type-driven section masking
- **Module:** Zip243SaplingSighash
- **Category:** incomplete-coverage
- **Summary:** Lean unconditionally concatenates all sections; Rust uses `update_hash!` conditionally on hash_type bits.
- **Evidence:** `Zip243SaplingSighash.lean:105-117` vs librustzcash `sighash_v4.rs:151-194`.
- **Recommended action:** Parameterise preimage by `hash_type`.

### Finding 54: Zip243SaplingSighash omits pre-Sapling V3 value_balance omission
- **Module:** Zip243SaplingSighash
- **Category:** incomplete-coverage
- **Summary:** `valueBalanceSapling` unconditional in Lean; Rust gates by `tx.version.has_sapling()`.
- **Evidence:** `Zip243SaplingSighash.lean:78-79` vs librustzcash `sighash_v4.rs:227-229`.
- **Recommended action:** Add `version` discriminator; two preimage shapes.

### Finding 55: Zip244TxIdDigest models BLAKE2b personalisation as prefix bytes
- **Module:** Zip244TxIdDigest
- **Category:** rust-lean-mismatch
- **Summary:** Lean: `H.hash (tag ++ payload)`. Real BLAKE2b: 16-byte personal in IV during state init. Different collision profile.
- **Evidence:** `Zip244TxIdDigest.lean:137-138` vs librustzcash `txid.rs:404-410`.
- **Recommended action:** Reify BLAKE2b personal-in-IV semantics, or state additional assumption explicitly.

### Finding 56: Zip244TxIdDigest models top-level tree only
- **Module:** Zip244TxIdDigest
- **Category:** incomplete-coverage
- **Summary:** Lean has 4 top-level sections; ZIP-244 has nested sub-digests. Internal sub-tree collision resistance unverified.
- **Evidence:** `Zip244TxIdDigest.lean:104-111` vs `zip-0244.rst:120-150`.
- **Recommended action:** Add nested sub-digest structure; prove injectivity recursively.

### Finding 57: Zip200BranchIdBinding hardcodes mainnet activation heights
- **Module:** Zip200BranchIdBinding
- **Category:** incomplete-coverage
- **Summary:** `currentUpgrade` mainnet only; testnet heights differ.
- **Evidence:** `Zip200BranchIdBinding.lean:50-58` vs Rust `parameters/constants.rs:51-69`.
- **Recommended action:** Add network parameter; add testnet validity-band theorem.

### Finding 58: Zip213ShieldedCoinbase models a fictional ovk field
- **Module:** Zip213ShieldedCoinbase
- **Category:** hidden-triviality
- **Summary:** Lean: `ShieldedOutput.ovk = ZERO_OVK`. Reality: ZIP-213 is a cryptographic decryption check; no `ovk` field on Output description.
- **Evidence:** `Zip213ShieldedCoinbase.lean:91-93` vs Rust `transaction/check.rs:361`.
- **Recommended action:** Model decryption check abstractly (`decrypts_successfully` predicate); abandon field-equality model.

### Finding 59: Zip216CanonicalPoint conflates "≥q" with "non-canonical"
- **Module:** Zip216CanonicalPoint
- **Category:** rust-lean-mismatch
- **Summary:** Lean rejects encoded LE values `≥ FIELD_ORDER`. ZIP-216 specifies exactly two non-canonical bit sequences (sign-bit-ambiguity for u=0 Jubjub points).
- **Evidence:** `Zip216CanonicalPoint.lean:117-118` vs `zip-0216.rst:92-101`.
- **Recommended action:** Reduce rejection set to two specific bit sequences.

### Finding 60: Zip216CanonicalPoint hides a Rust panic-on-None
- **Module:** Zip216CanonicalPoint
- **Category:** rust-lean-mismatch
- **Summary:** Rust `TransmissionKey::try_from([u8; 32])` calls `.unwrap()`; Lean treats as clean `Option`. May be a Zebra bug the model masks.
- **Evidence:** `Zip216CanonicalPoint.lean:144-146` vs Rust `sapling/keys.rs:219`.
- **Recommended action:** File Zebra issue; mark Lean as panic-equivalent until fixed.

### Finding 61: Zip216CanonicalPoint not tied to ZIP-216 enforcement sites
- **Module:** Zip216CanonicalPoint
- **Category:** incomplete-coverage
- **Summary:** Lean models generic byte-level canonicity; ZIP-216 enumerates specific fields (spendAuthSig.R, bindingSigSapling.R, pk_d, vk).
- **Evidence:** Whole module file vs `zip-0216.rst:104-122`.
- **Recommended action:** Add per-site application theorems.

### Finding 62: AddrMessageCap omits dynamic message-size cap
- **Module:** AddrMessageCap
- **Category:** incomplete-coverage
- **Summary:** Lean models static `MAX_INV_IN_RECEIVED_MESSAGE = 50_000`; Rust uses `min(message_size_limit, MAX_INV_IN_RECEIVED_MESSAGE)`.
- **Evidence:** `protocol/external/inv.rs:203-211` vs `AddrMessageCap.lean:39,73`.
- **Recommended action:** Replace constant with `min` formula.

### Finding 63: MinNetworkVersion conflates Testnet and Regtest
- **Module:** MinNetworkVersion
- **Category:** rust-lean-mismatch
- **Summary:** Lean: single `Net.testnet`. Rust differentiates default-testnet (170_007) from regtest (170_006) at Sapling.
- **Evidence:** `external/types.rs:96-98` vs `MinNetworkVersion.lean:73,42-44`.
- **Recommended action:** Add `Net.regtest`.

### Finding 64: MinNetworkVersion omits the Genesis NU variant
- **Module:** MinNetworkVersion
- **Category:** incomplete-coverage
- **Summary:** Rust handles Genesis at 170_002; Lean enum starts at `beforeOverwinter`. Monotonicity theorems off-by-one.
- **Evidence:** `external/types.rs:93` vs `MinNetworkVersion.lean:28-40`.
- **Recommended action:** Add `genesis` variant.

### Finding 65: PeerConnectionLimits omits the concurrent-dial check
- **Module:** PeerConnectionLimits
- **Category:** incomplete-coverage
- **Summary:** Lean models static caps; Rust safety check is concurrent (`update_count() >= peerset_outbound_connection_limit()`).
- **Evidence:** `peer_set/initialize.rs:895-902`.
- **Recommended action:** Add concurrent-overflow theorem.

### Finding 66: InventoryCacheSize models LRU; Rust uses insertion-order
- **Module:** InventoryCacheSize
- **Category:** rust-lean-mismatch
- **Summary:** Lean filters and appends (LRU); Rust `IndexMap::insert` preserves key's original position. `shift_remove_index(0)` drops different victims under the two policies.
- **Evidence:** `peer_set/inventory_registry.rs:403,421,431` vs `InventoryCacheSize.lean:106-107`.
- **Recommended action:** Rewrite `insertOrBump` to preserve existing index; re-prove T18/T19. Most consequential network-side finding.

### Finding 67: InventoryCacheSize understates DoS surface by ~47x
- **Module:** InventoryCacheSize
- **Category:** incomplete-coverage
- **Summary:** T15 computes 64_000 bytes per map (inv-hash table only); Rust safety comment says peers-per-inv table is ~3 MB.
- **Evidence:** `peer_set/inventory_registry.rs:42-44`.
- **Recommended action:** Extend to include per-peer dimensions.

### Finding 68: InventoryCacheSize omits the input-truncation step
- **Module:** InventoryCacheSize
- **Category:** incomplete-coverage
- **Summary:** Rust truncates incoming `hashes` to `MAX_INV_PER_MAP` at message-handling boundary (first DoS guard). Lean models only registry-internal guard.
- **Evidence:** `peer_set/inventory_registry.rs:147,165`.
- **Recommended action:** Add input-cap function and theorem.

### Finding 69: MempoolAdmission omits the legacy fee check
- **Module:** MempoolAdmission
- **Category:** incomplete-coverage
- **Summary:** Lean models only unpaid-actions check; `miner_fee >= min_fee` legacy check missing.
- **Evidence:** `unmined/zip317.rs:220-228`.
- **Recommended action:** Model both checks; prove redundancy claim under `BLOCK_UNPAID_ACTION_LIMIT = 0`.

### Finding 70: MempoolAdmission accepts conventionalActions = 0
- **Module:** MempoolAdmission
- **Category:** rust-lean-mismatch
- **Summary:** Rust always uses `max(logical_actions, GRACE_ACTIONS = 2)`; Lean allows 0.
- **Evidence:** `unmined/zip317.rs:91-93,161-169`.
- **Recommended action:** Derive `conventionalActions` from tx shape.

### Finding 71: MempoolEviction models deterministic min; Rust is weighted random
- **Module:** MempoolEviction
- **Category:** rust-lean-mismatch
- **Summary:** Lean deterministic lowest-`ratio`-first; Rust `WeightedIndex::new(weights)` proportional to `eviction_weight = cost + low_fee_penalty`.
- **Evidence:** `mempool/storage/verified_set.rs:218-239`.
- **Recommended action:** Model eviction weight; probability-bound theorem.

### Finding 72: MempoolEviction inverts the ranking direction
- **Module:** MempoolEviction
- **Category:** rust-lean-mismatch
- **Summary:** Lean ranks by fee-density (lower = worse); Rust ranks by eviction weight (higher = more likely to evict). Ranking direction inverted.
- **Evidence:** `MempoolEviction.lean:84-86,99` vs `transaction/unmined.rs:489-497`.
- **Recommended action:** Rename to eviction-weight; flip comparison.

### Finding 73: MempoolEviction.cap is tx-count; Rust caps bytes
- **Module:** MempoolEviction
- **Category:** incomplete-coverage
- **Summary:** Lean treats `cap` as transaction count; Rust caps by byte-cost (`total_cost() > tx_cost_limit`).
- **Evidence:** `mempool/storage.rs:478-484,217-218`.
- **Recommended action:** Replace `cap` with `byteCap`; sum tx costs in loop.

### Finding 74: TransparentAddress omits the Tex variant (ZIP-320)
- **Module:** TransparentAddress
- **Category:** incomplete-coverage
- **Summary:** Lean: p2pkh/p2sh only. Rust has Tex; mainnet Tex prefix `[0x1c, 0xb8]` collides with mainnet P2PKH prefix. Lean's `prefixes_pairwise_distinct` hides this.
- **Evidence:** `transparent/address.rs:31-58,175-203`, `parameters/network.rs:110-116`.
- **Recommended action:** Add Tex variant; add "prefix collision under serialise" theorem.

### Finding 75: TransparentAddress omits Regtest network kind
- **Module:** TransparentAddress
- **Category:** rust-lean-mismatch
- **Summary:** Lean: Mainnet/Testnet. Rust: + Regtest. Rust deserialiser coerces Regtest → Testnet; Lean's round-trip masks this.
- **Evidence:** `transparent/address.rs:220-225`.
- **Recommended action:** Add Regtest; add coercion theorem.

## Medium / Low

**Medium severity** (~62 findings, condensed):

- **NetworkUpgrade testnet/regtest activation:** `current` doesn't take network; testnet/regtest with configurable activation heights and same-height upgrades unmodelled. Add network parameter; pin testnet vectors.
- **Height staged-bound granularity:** Rust does `u32::try_from` then `Height::try_from`; Lean collapses to single Int bound. Stage structure invisible. Model two-stage check.
- **Amount value-balance group encoding:** `From<Amount<C>> for jubjub::Fr / pallas::Scalar` unverified. Link to future Pedersen module.
- **CompactSize MAX_PROTOCOL_MESSAGE_LEN pinning:** docstring downplays binding nature; matches production. Tighten docstring; add constant-equality theorem.
- **LockTime.Time chrono panic:** `Utc.timestamp_opt(n, 0).single().expect(...)` panic site unmodelled.
- **LockTime.encode height bound:** roundtrip allows heights up to U32_MAX, outside Height invariant. Tighten to `n ≤ MAX_HEIGHT = MIN_TIMESTAMP - 1`.
- **LockTime variant collision at MIN_TIMESTAMP:** `Height(n)` with `n ≥ MIN_TIMESTAMP` decodes as `Time`. Lean precondition avoids this but doesn't prove the collision.
- **FoundersReward.foundersActive omits Canopy double-guard:** Rust `halving(h) < 1 && current(net,h) < Canopy` protects custom testnets. Lean uses one boolean.
- **FoundersReward abstract scalar:** no link to height-driven `block_subsidy`. Parameterise by height.
- **CanopyDeferredEarn cumulative-lockbox epoch width:** uses 840_000 blocks but should use post-Blossom 1_680_000.
- **Zip1014Devfund Testnet/Regtest:** Mainnet only.
- **Zip1015FundingStreams NU6.1 height range:** model conflates NU6 and NU6.1 range theorems; ranges differ 3x.
- **Zip2001Lockbox module name:** no published ZIP-2001 governs lockboxes; ZIP-1015 does. Rename to `Zip1015Lockbox`.
- **Zip2001Lockbox cumulative bounds too loose:** uses MAX_MONEY per block rather than 12% of MAX_BLOCK_SUBSIDY.
- **SlowStartSubsidy/Subsidy non-composition:** Lean has two functions, Rust has one. Add bridge theorem.
- **Subsidy.halvingDivisor shift boundary:** `< 64` matches `checked_shl >= 64` but reframed differently.
- **Bech32 HRP charset:** `hrpExpand` accepts arbitrary Nat HRP bytes; BIP-173 requires ASCII lowercase.
- **BlockHeader Equihash omission:** `encodeFixed` skips Equihash solution.
- **TransactionV5Header T2 redundancy:** `v5_header_lt_u32` overlaps with `Zip225V5Layout`.
- **TransactionMaxSize prefix worst-case:** `TX_COUNT_COMPACTSIZE_MAX = 9` is unreachable.
- **TransactionMaxSize SOLUTION_COMPACTSIZE:** pinned by assumption not theorem.
- **Zip225V5Layout T20:** proves shared prefix but not that bytes 8..12 differ.
- **BlockMaxTime Nat timestamps:** elides DateTime + u32 overflow at year 2106.
- **ReorgWindow Nat-truncation accident:** Rust uses i32 HeightDiff.
- **AnchorValidity two-source check:** Lean one KnownRoots list; Rust parent-chain + finalized DB.
- **AnchorValidity Sprout interstitial:** Rust tracks per-JoinSplit interstitial treestates.
- **OrchardActionBounds binding-sig omission:** module references binding verification but proves only Int partial-sum invariant.
- **OrchardIncrementalMerkle UNCOMMITTED:** modelled as `Nat = 2`; Rust uses `pallas::Base::one().double()`.
- **PoolValueBalance 32/40-byte deserialisation:** Rust accepts both for backward compatibility.
- **JoinSplitProof Canopy gating:** `NoSproutPoolAddition` unconditional in Lean; Rust gates by height.
- **JoinSplitProof sproutPoolAddition perspective:** chain vs transaction sign conventions conflated.
- **PedersenAbstract binding only under shared randomness:** general Pedersen binding reduces to DL between bases.
- **PedersenAbstract small-order rejection unmodelled:** ZIP-216 `from_bytes_not_small_order` part of value-commitment check.
- **SighashTypes V4 raw byte semantics:** `sighash_v4_raw` preserves non-canonical bits like 0x41; Lean rejects them.
- **SighashTypes encoding uses +:** sound for 6-value table but fragile to extension.
- **SighashTypes byte vs u32 carrier:** Rust `HashType: u32`; model implicitly assumes only 6 canonical values.
- **Zip200BranchIdBinding Genesis/BeforeOverwinter:** Lean returns None for pre-Overwinter; Rust returns `Some(BeforeOverwinter)`.
- **Zip203Expiry V1/V2 None handling:** Lean conflates field=0 with field absence.
- **Zip203Expiry coinbase exemption:** NU5-onward coinbase has stricter rule.
- **Zip209NegativeValuePool single-pool:** Rust operates on 4-pool ValueBalance struct. AUDIT.md C-7.
- **Zip209NegativeValuePool Amount overflow:** Lean uses unbounded Int; Rust caps at ±MAX_MONEY.
- **Zip211SproutClosed weak headline T1:** sums to ≤ 0; Rust rule is per-JoinSplit `vpub_old = 0`.
- **Zip213ShieldedCoinbase coinbase check absent:** Lean skips `is_coinbase()` runtime check.
- **Zip213ShieldedCoinbase Canopy lead-byte rule:** ZIP-213 also requires note plaintext lead byte = 0x02.
- **Zip244TxIdDigest T15 rfl:** docstring oversells deterministic txid claim.
- **Zip244TxIdDigest root personalization opaque:** loses `consensus_branch_id` cross-binding.
- **PeerConnectionLimits per-IP asymmetry:** Rust accepts multiple inbound to same IP but limits outbound; Lean's T11 elides asymmetry.
- **Bip34CoinbaseHeight non-canonicity rejection:** only 1-byte band proved (T12); 2/3/4-byte missing.
- **Bip34CoinbaseHeight signed-i64 encoding:** uses Nat arithmetic; Rust uses i64 with high-bit handling.
- **TransparentAddress docstring:** says "exactly the bytes ZcashSerialize operates on" but excludes Tex.
- **NetworkUpgrade.current_total hidden-trivial:** `∃ nu, current h = nu` is `rfl`.
- **NetworkUpgradeBridge brittle to Nu7 addition:** 11 by_cases needs 12th.
- **CompactSize decode_total:** `isSome ∨ none` tautological; Rust panic freedom on IO.
- **CompactSize byte-range hostile input:** `[0xfd, 256, 0]` decodes; hostile-input safety silent.
- **LockTime decode_total triviality:** same shape.
- **PowAveragingWindow stale citation:** cites `zebra-chain/src/work/difficulty.rs:52` for `POW_MEDIAN_BLOCK_SPAN`; that's a doc-comment. Real source is `zebra-state/src/service/check/difficulty.rs:22`.
- **PowAveragingWindow 6 of 11 theorems are constant pins:** higher density than 10-15% pinning ratio.

**Low severity** (~74 findings, very condensed):

- Height T2 `subH_eq` is `rfl` on its definition.
- Height `MAX_EXPIRY_HEIGHT` not modelled (see Zip203Expiry).
- Amount `div_exact` panic boundary unmodelled.
- Amount B4 `checkedSub_as_add` is `rfl` after unfolding.
- CanopyDeferredEarn T4 `cumulativeLockbox_eq` is `rfl` (definitional unfold).
- CanopyDeferredEarn T15 `deferred_ratio` (`12 * 25 = 100 * 3`) is integer identity.
- Zip1015FundingStreams T20 `post_nu6_total_unchanged` is `20 = 20`.
- Zip2001Lockbox T1 `lockboxPerBlock_eq` is `rfl`; should be `@[simp]`.
- SlowStartSubsidy T9 docstring overstates "at least 2*slowStartRate" but theorem is exact equality.
- EquihashParams T1-T6 are `decide`/`rfl` over Nat constants.
- EquihashParams "sapling root" naming stale (now `commitment_bytes`).
- EquihashParams Regtest 36-byte solution has no (n,k) derivation.
- EquihashSolution T1-T11 mix of `decide`/`rfl` constant pins.
- CompactDifficulty `roundtrip_zcash_main` verifies bit decomposition only.
- CompactDifficulty `e ∈ {30,31,32+,<0}` cases unmodelled.
- CoinbaseMaturity T2-T6 are 1-line `omega` proofs (mechanical monotonicity).
- Nullifiers Sprout `NullifierSeed` (rho) 32-byte type omitted.
- OrchardActionBounds T11/T12 hypothesis already implies conclusion (tautology).
- OrchardIncrementalMerkle T19/T20 conditional on injectivity hypothesis.
- HistoryTreeAppendOnly Tree/empty type distinction collapsed.
- HistoryTreeAppendOnly 11 of 21 theorems are Mathlib List lemmas.
- NoteCommitmentTreeDepth Frontier-recomputation semantics opaque.
- NoteCommitmentTreeDepth FullTree rejection not cross-linked to block rejection.
- AnchorValidity T1-T15 are `List.mem_*` consequences.
- JoinSplitProof 601-byte ciphertext not pinned separately.
- SighashTypes T17 `encodeU32LE_zero_upper` is `rfl` on definition.
- Zip200BranchIdBinding only NU5 band proven explicitly.
- Zip209NegativeValuePool T13 `finalBalance_eq_runningBalance` is `rfl`.
- Zip211SproutClosed T7 inclusive threshold tautology (unfolding).
- AddrMessageCap T11-T14 boundary theorems trivial.
- AddrMessageCap T9 compares against wrong constant (Zebra's own MAX_INV_MESSAGE_ENTRIES instead of zcashd's MAX_INV_SZ).
- MinNetworkVersion Regtest entry hidden in two-element Net function.
- InventoryCacheSize T12/T13/T14 constant pins; T7/T8 one-line unfolds.
- MempoolEviction T1 `mempool_constants_values` (3 rfl conjuncts); 4_000 vs 4.0_f32 scaling unverified.
- TransparentAddress T11/T12 concrete vectors `unfold; rfl`.
- Zip216CanonicalPoint T11/T12 round-trip definitional.

## Informational and positive confirmations

The verification meaningfully confirms several non-obvious facts that could plausibly have been wrong:

- **NetworkUpgradeBridge.current_toOrd_eq_currentOrd** closes a real algebraic gap; cascade and indicator-sum form give the same ordinal, monotonicity transfers via the bridge (avoiding 2^11 explosion under `split_ifs`).
- **SlowStartSubsidy.T5 slowStartSubsidy_at_interval_minus_one** confirms the ramp lands exactly on MAX_BLOCK_SUBSIDY at `SLOW_START_INTERVAL - 1`, validating the `(h+1)` post-shift compensation as off-by-one-free.
- **Zip1014Devfund.T8 recipients_sum_le_devfund** confirms 7%+5%+8% floor distributivity does not over-pay 20% headline.
- **CompactDifficulty.T3 compact_decompose_recompose** confirms bit-level invariant `c = mantissa(c) + sizeByte(c) * 2^24` for canonical compact words.
- **EquihashSolution.T11 prefix_payload_decodes** confirms CompactSize band-2 wire-prefix bytes `[0xfd, 0x40, 0x05]` correctly encode 1344.
- **TransactionV5Header.T6 nu5_encoding_literal** gives a concrete 20-byte vector matching wire byte order for `0x80000005 + 0x26A7270A + NU5 branch id`.
- **Zip225V5Layout.T1/T2** cleanly decomposes `V5_HEADER = (1 << 31) + 5`, capturing the `fOverwintered | version` algebra.
- **Zip243SaplingSighash.T3 preimage injectivity** peels off each section via length-based `List.append_inj` — confirms field-order matters under abstract H.
- **NU63IronwoodLayout.T8 decodeV6_agrees_on_v5_range** states wire-compatibility property NU6.3 must maintain.
- **PedersenAbstract.T2/T4** additive homomorphism uses `add_zsmul`/`abel`, not `rfl`. Substantive group-theoretic facts.
- **OrchardActionBounds.T3/T5** confirm `MAX_ACTION_ALLOCATION = 2262` satisfies Rust `static_assertions::const_assert!(MAX < (1 << 16))`.
- **JoinSplitProof.T7-T10** confirm `TrustedPreallocate` invariant `MAX_ALLOC * JOINSPLIT_SIZE ≤ MAX_BLOCK_BYTES - 1` holds for both BCTV14 (1109 × 1802 = 1_998_418) and Groth16 (1177 × 1698 = 1_998_546).
- **BlockSizeLimits T5** confirms `MAX_BLOCK_BYTES ≤ MAX_PROTOCOL_MESSAGE_LEN` with slack 97_152 across two Rust files.
- **PeerConnectionLimits T5** confirms `totalMax target = 8 * target`.
- **TransparentAddress T6** confirms (modulo Tex) the four B58 prefixes pairwise distinct.

**Spec-ambiguity clarifications surfaced:**

- **Zip2001Lockbox naming:** no published ZIP-2001 governs lockboxes; ZIP-1015 does. Rename.
- **CanopyDeferredEarn naming:** "Canopy" implies pre-NU6 coverage but module covers post-NU6 only.
- **Zip200BranchIdBinding height-band model:** pre-Overwinter epochs have NetworkUpgrade values without branch IDs — different from "no upgrade".
- **JoinSplitProof sproutPoolAddition sign:** RFC-0012 (chain) vs `value_balance()` (transaction) sign conventions differ.
- **BlockMaxTime constant:** `MAX_BLOCK_TIME_TOLERANCE = 7200` is a Lean-side label for inline `chrono::Duration::hours(2)` in Rust.

## Categorical breakdown

| Severity \\ Category | rust-lean-mismatch | incomplete-coverage | hidden-triviality | wrong-brief-corrected | spec-ambiguity | positive-confirmation |
|---|---|---|---|---|---|---|
| Critical | 8 | 4 | 2 | 0 | 1 | 0 |
| High | 13 | 22 | 4 | 2 | 1 | 0 |
| Medium | 14 | 25 | 8 | 1 | 14 | 0 |
| Low | 5 | 13 | 24 | 1 | 4 | 27 |
| Informational | 0 | 0 | 0 | 0 | 0 | 14 |

(Counts approximate; some findings span categories. Total reconciles to 207 via the structured input list.)

## How this document was produced

Findings were extracted by a fan-out wave of per-module-group adversarial review agents (max effort, structured JSON output), with separate positive-confirmation and triviality-detection passes. The orchestration emitted 207 structured findings across 62 modules; this document is the human-actionable triage layer over that JSON. Each module group received the full Rust source it claimed to verify and was instructed to find (a) wrong behaviour relative to Rust, (b) trivially-true theorems, (c) coverage gaps, and (d) genuine positive findings. The structured JSON was then mapped to severity-ordered prose for maintainer triage.