# Source anchors

Snapshots of the `zebra-chain` files this verification covers, pinned to a
specific upstream commit.

| File | Path in `ZcashFoundation/zebra` |
|---|---|
| `height.rs` | `zebra-chain/src/block/height.rs` |
| `amount.rs` | `zebra-chain/src/amount.rs` |
| `compact_size.rs` | `zebra-chain/src/serialization/compact_size.rs` |

**Pinned commit:** `ca730cb7f93b4b36d71dc9cff0c5b8773d03006e`
(`ZcashFoundation/zebra` `main`, 2026-06-25).

## Why this exists

The Lean proofs in this repo are written against a *manual* re-statement of
these Rust files (`../src/*.rs`). The CI step in
`.github/workflows/drift-check.yml` fetches the upstream files at the pinned
commit and `diff`s them against these snapshots. If `zebra-chain` changes the
source files in any way, CI fails — forcing whoever bumps the pin to either:

1. Confirm the change is semantically irrelevant (formatting, doc comments,
   added bystander methods) and re-snapshot here, or
2. Update `../src/*.rs` and the Lean proofs to track the change, then
   re-snapshot.

This is the cheaper alternative to a full Aeneas-based re-extraction pipeline
on every push: the snapshot detects drift, and a human decides whether
re-extraction is needed.
