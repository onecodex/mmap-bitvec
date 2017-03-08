use std::hash::{Hash, Hasher};
use std::io;
use std::path::Path;

use memmap::{Mmap, Protection};
use murmurhash3::murmurhash3_x64_128;

use bitvec::BitVec;

// we can't use the murmurhash3::Murmur3Hasher b/c it makes copies of the 
// bytes to be hashed with every single `hash` call
struct MurmurHasher(u64, u64);

impl MurmurHasher {
    pub fn new() -> Self {
        MurmurHasher(0, 0)
    }

    pub fn values(&self) -> (u64, u64) {
        (self.0, self.1)
    }
}

impl Hasher for MurmurHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        let hash = murmurhash3_x64_128(bytes, self.0);
        *self = MurmurHasher(hash.0, hash.1);
    }
    // have to provide this to fulfill the trait requirements
    fn finish(&self) -> u64 { self.0 }
}



struct BloomFilter {
    bit_vec: BitVec,
    hashes: u8,
}

impl BloomFilter {
    pub fn new<P>(filename: P, bits: usize, n_hashes: u8) -> Result<Self, io::Error> where P: AsRef<Path> {
        let bitvec = BitVec::from_file(&filename, bits, false)?;
        Ok(BloomFilter {
            bit_vec: bitvec,
            hashes: n_hashes,
        })
    }

    pub fn insert<H>(&mut self, ref item: H) where H: Hash {
        let mut hasher = MurmurHasher::new();
        for _ in 0..self.hashes {
            item.hash(&mut hasher);
            let hash: u64 = hasher.finish();
            let size = self.bit_vec.size;
            self.bit_vec.set(hash as usize % size, true);
        }
    }

    pub fn contains<H>(&self, ref item: H) -> bool where H: Hash {
        let mut hasher = MurmurHasher::new();
        for _ in 0..self.hashes {
            item.hash(&mut hasher);
            let hash: u64 = hasher.finish();
            let size = self.bit_vec.size;
            if !self.bit_vec.get(hash as usize % size) {
                return false;
            }
        }
        true
    }
}


#[test]
fn test_bloom_filter() {
    use std::fs::remove_file;
    remove_file("./test");

    let mut filter = BloomFilter::new("./test", 100, 2).unwrap();
    let (a, b) = (1, 2);
    assert!(!filter.contains(a));
    assert!(!filter.contains(b));
    filter.insert(b);
    assert!(!filter.contains(a));
    assert!(filter.contains(b));

    remove_file("./test");
}
