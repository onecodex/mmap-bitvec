use std::ops::Range;

/// A nasic bitvector trait that we implement for mmap
pub trait BitVector {
    /// Get the value at bit `i`
    fn get(&self, i: usize) -> bool;
    /// Set the value at bit `i`
    fn set(&mut self, i: usize, x: bool);
    /// Returns the size of the bitvector
    fn size(&self) -> usize;

    /// Returns the number of bits sets in the given range
    fn rank(&self, r: Range<usize>) -> usize {
        r.fold(0, |a, x| a + if self.get(x) { 1 } else { 0 })
    }

    /// Returns the position of the n-th bit set
    fn select(&self, n: usize, start: usize) -> Option<usize> {
        let mut bits_left = n;

        for i in start..self.size() {
            if self.get(i) {
                bits_left -= 1;
            }

            if bits_left == 0 {
                return Some(i);
            }
        }
        None
    }

    /// Return all the bits in the given range as a u128
    fn get_range(&self, r: Range<usize>) -> u128 {
        if r.end - r.start > 128 {
            panic!("Range too large (>128)")
        } else if r.end > self.size() {
            panic!("Range ends outside of BitVec")
        }

        let mut bvs = 0;
        let mut bit_pos = 127;
        for i in r {
            if self.get(i) {
                bvs += 1 << bit_pos;
            };
            bit_pos -= 1;
        }
        bvs
    }

    /// Sets all the bits in the given range from the given u128
    fn set_range(&mut self, r: Range<usize>, x: u128) {
        let mut cur = x;
        for i in r.rev() {
            self.set(i, cur & 1 == 1);
            cur >>= 1;
        }
    }

    /// Sets all the bit in the given range to false
    fn clear_range(&mut self, r: Range<usize>) {
        for i in r.rev() {
            self.set(i, false);
        }
    }
}

macro_rules! impl_bitvector {
    ( $type:ty, $type_size:expr ) => {
        impl BitVector for $type {
            fn get(&self, i: usize) -> bool {
                if i > $type_size - 1 {
                    panic!("Invalid bit vector index");
                }
                (self & 1 << ($type_size - i)) > 0
            }

            fn set(&mut self, i: usize, x: bool) {
                if x {
                    self.clone_from(&(*self | (1 << ($type_size - i))));
                } else {
                    self.clone_from(&(*self & !(1 << ($type_size - i))));
                }
            }

            fn size(&self) -> usize {
                $type_size
            }
        }
    };
}

impl_bitvector!(u8, 8);
impl_bitvector!(u16, 16);
impl_bitvector!(u32, 32);
impl_bitvector!(u64, 64);
impl_bitvector!(u128, 128);

impl BitVector for &[u8] {
    fn get(&self, i: usize) -> bool {
        if i / 8 >= self.size() {
            panic!("Invalid bit vector index");
        }
        self[i / 8] >> (8 - i % 8) & 1 == 1
    }

    fn set(&mut self, _: usize, _: bool) {
        panic!("Can not set bits on a non-mut slice");
    }

    fn size(&self) -> usize {
        self.len() / 8
    }
}

impl BitVector for Vec<u8> {
    fn get(&self, i: usize) -> bool {
        if i / 8 >= self.len() {
            panic!("Invalid bit vector index");
        }
        self[i / 8] >> (8 - i % 8) & 1 == 1
    }

    fn set(&mut self, i: usize, x: bool) {
        if i / 8 >= self.len() {
            panic!("Invalid bit vector index");
        }
        if x {
            self[i / 8] |= 1 << (8 - i);
        } else {
            self[i / 8] &= !(1 << (8 - i));
        }
    }

    fn size(&self) -> usize {
        self.len() / 8
    }
}
