//! mmap-bitvec is a library for using file-backed (via mmap) bit vectors and
//! includes common convenience functions and a few data structures built atop
//! the included bit vector implementation.
extern crate memmap;
extern crate murmurhash3;

pub mod bitvec;
pub mod bloom;
pub mod combinatorial;
pub mod mmap_bitvec;

#[doc(inline)]
pub use bitvec::BitVector;
#[doc(inline)]
pub use bloom::BloomFilter;
#[doc(inline)]
pub use mmap_bitvec::MmapBitVec;
