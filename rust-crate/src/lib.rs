//! `zebrafm` — extraction crate for the Lean verification of
//! `zebra-chain` arithmetic and parsing.
//!
//! This crate mirrors the load-bearing semantic content of the corresponding
//! Rust modules in `zebra-chain`, in a form Aeneas can ingest:
//!
//! - `Amount` arithmetic and `Constraint` validation
//! - `Height` arithmetic and `try_from` range check
//! - `CompactSize64` encode/decode (the `&[u8]`-pure adaptation of the Rust
//!   `byteorder`-based reader/writer)
//!
//! The `byteorder` and `io::Read`/`io::Write` boundary in the production
//! `zebra-chain` source is replaced here by `&[u8]` slices, matching the
//! adaptation pattern the proposal calls out.

pub mod amount;
pub mod compact_size;
pub mod height;
