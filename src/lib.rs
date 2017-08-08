//! mmap-bitvec is a library for using file-backed (via mmap) bit vectors and
//! includes common convenience functions and a few data structures built atop
//! the included bit vector implementation.
extern crate memmap;
extern crate murmurhash3;

mod bitvec;
mod bloom;

#[doc(inline)]
pub use bitvec::BitVec;
#[doc(inline)]
pub use bloom::BloomFilter;
