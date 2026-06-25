# Coq backend via Aeneas

A parallel verification pipeline that emits the same Rust source as Coq,
giving foundational diversification: a Lean kernel bug doesn't compromise
the Coq proof.

## Files

- `ZebraChainArith.v` — Aeneas-emitted Coq from the `rust-crate/` source.
- `Primitives.v` — Aeneas's Coq standard library (copied verbatim from
  `aeneas/backends/coq/`).
- `Proofs.v` — proofs against the emitted definitions. Currently a single
  representative theorem; the full re-proof of every Lean theorem in Coq
  is left as future work.

## Reproducing the extraction

Requires Aeneas built locally (see the top-level [`REPORT.md`](../REPORT.md)).

```sh
cd ../rust-crate
~/aeneas/charon/bin/charon cargo --preset=aeneas
~/aeneas/bin/aeneas -backend coq -dest /tmp/out-coq zebra_chain_arith.llbc
cp /tmp/out-coq/{ZebraChainArith,Primitives}.v ../coq-pipeline/
```

## Building

Requires Coq ≥ 8.18.

```sh
coq_makefile -f _CoqProject -o Makefile
make
```
