#![deny(missing_docs)]
//! `mmap-bitvec` is a library for using file-backed (via mmap) bit vectors and
//! includes common convenience functions and a few data structures built atop
//! the included bit vector implementation.
#[doc = include_str!("../README.md")]
/// The `bitvec` trait and some impl for built-in types
pub mod bitvec;
/// A simple implementation of a Bloom filter backed by `BitVec`
pub mod bloom;
/// All the utilities to interact with a mmap'd bitvector
pub mod mmap_bitvec;

#[doc(inline)]
pub use crate::mmap_bitvec::MmapBitVec;
#[doc(inline)]
pub use bitvec::BitVector;
#[doc(inline)]
pub use bloom::BloomFilter;
