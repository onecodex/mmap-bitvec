use std::ops::Range;

#[cfg(not(feature = "u128"))]
pub type BitVecSlice = u64;
#[cfg(not(feature = "u128"))]
pub const BIT_VEC_SLICE_SIZE: u8 = 64;
#[cfg(feature = "u128")]
pub type BitVecSlice = u128;
#[cfg(feature = "u128")]
pub const BIT_VEC_SLICE_SIZE: u8 = 128;

pub trait BitVector {
    fn size(&self) -> usize;
    fn get(&self, i: usize) -> bool;
    fn get_range(&self, r: Range<usize>) -> BitVecSlice;
    fn set(&mut self, i: usize, x: bool);
    fn set_range(&mut self, r: Range<usize>, x: BitVecSlice);
    fn clear_range(&mut self, r: Range<usize>);
    fn rank(&self, r: Range<usize>) -> usize;
    fn select(&self, n: usize, start: usize) -> Option<usize>;
}

// TODO: impl for `std::collections::BitVec`?
