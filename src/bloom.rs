use std::hash::{Hash, Hasher};
use std::io;
use std::path::Path;

use murmurhash3::murmurhash3_x64_128;

use bitvec::BitVec;

// we don't want to use murmurhash3::Murmur3Hasher b/c it makes copies of the
// bytes to be hashed with every single `hash` call
struct MurmurHasher(u64, u64);

impl MurmurHasher {
    pub fn new() -> Self {
        MurmurHasher(0, 0)
    }

    // pub fn values(&self) -> (u64, u64) {
    //     (self.0, self.1)
    // }
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


/// A simple implementation of a Bloom filter backed by `BitVec`
pub struct BloomFilter {
    bit_vec: BitVec,
    hashes: u8,
}

impl BloomFilter {
    /// Creates a new Bloom filter (or opens an existing one, if the file
    /// already exists) of a given size (bits) and with a given number of
    /// hash functions for each insert (n_hashes). If a filename is not
    /// passed, the Bloom filter will be created in memory.
    pub fn new<P>(filename: Option<P>, bits: usize, n_hashes: u8) -> Result<Self, io::Error> where P: AsRef<Path> {
        let header = vec![];
        let bitvec = match filename {
            Some(filename) => {
                if Path::exists(filename.as_ref()) {
                    BitVec::from_file(&filename, Some(b"!!"), false)?
                } else {
                    BitVec::create_file(&filename, bits, b"!!", &header)?
                }
            },
            None => BitVec::from_memory(bits)?
        };
        Ok(BloomFilter {
            bit_vec: bitvec,
            hashes: n_hashes,
        })
    }

    /// Insert an item into the bloom filter.
    pub fn insert<H>(&mut self, item: H) where H: Hash {
        let mut hasher = MurmurHasher::new();
        for _ in 0..self.hashes {
            item.hash(&mut hasher);
            let hash: u64 = hasher.finish();
            let size = self.bit_vec.size();
            self.bit_vec.set(hash as usize % size, true);
        }
    }

    /// Check if an item is in the bloom filter already.
    pub fn contains<H>(&self, item: H) -> bool where H: Hash {
        let mut hasher = MurmurHasher::new();
        for _ in 0..self.hashes {
            item.hash(&mut hasher);
            let hash: u64 = hasher.finish();
            let size = self.bit_vec.size();
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
    let mut filter = BloomFilter::new(Some("./test_bloom"), 100, 2).unwrap();
    let (a, b) = (1, 2);
    assert!(!filter.contains(a));
    assert!(!filter.contains(b));
    filter.insert(b);
    assert!(!filter.contains(a));
    assert!(filter.contains(b));

    remove_file("./test_bloom").unwrap();
}
