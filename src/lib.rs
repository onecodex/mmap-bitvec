//! mmap-bitvec is a library for using file-backed (via mmap) bit vectors and
//! includes common convenience functions and a few data structures built atop
//! the included bit vector implementation.

pub mod bitvec;
pub mod bloom;
pub mod combinatorial;
pub mod mmap_bitvec;

#[doc(inline)]
pub use crate::mmap_bitvec::MmapBitVec;
#[doc(inline)]
pub use bitvec::BitVector;
#[doc(inline)]
pub use bloom::BloomFilter;
