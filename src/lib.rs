//! mmap-bitvec is a library for using file-backed (via mmap) bit vectors and
//! includes common convenience functions and a few data structures built atop
//! the included bit vector implementation.
#![cfg_attr(feature = "u128", feature(i128_type))]

extern crate memmap;
extern crate murmurhash3;

pub mod bitvec;
pub mod bloom;

#[doc(inline)]
pub use bitvec::{BitVec, BitVecSlice, BIT_VEC_SLICE_SIZE};
#[doc(inline)]
pub use bloom::BloomFilter;
