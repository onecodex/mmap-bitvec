use std::hash::{Hash, Hasher};
use std::io;
use std::path::Path;

use murmurhash3::murmurhash3_x64_128;

use crate::bitvec::BitVector;
use crate::mmap_bitvec::MmapBitVec;

/// Newtype for murmur hashing.
/// We don't use murmurhash3::Murmur3Hasher because it makes copies of the
/// bytes to be hashed on every `hash` call
#[derive(Default)]
pub struct MurmurHasher(u64, u64);

impl MurmurHasher {
    #[allow(missing_docs)]
    pub fn new() -> Self {
        MurmurHasher(0, 0)
    }
    #[allow(missing_docs)]
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

    fn finish(&self) -> u64 {
        self.0
    }
}

/// A simple implementation of a Bloom filter backed by `BitVec`
pub struct BloomFilter {
    bit_vec: MmapBitVec,
    hashes: u8,
}

impl BloomFilter {
    /// Creates a new `BloomFilter` (or opens an existing one, if the file
    /// already exists) of a given size (in bits) and with a given number of
    /// hash functions for each insert (`n_hashes`). If a filename is not
    /// passed, the bloom filter will be created in memory.
    pub fn new<P>(filename: Option<P>, bits: usize, n_hashes: u8) -> Result<Self, io::Error>
    where
        P: AsRef<Path>,
    {
        let header = vec![];
        let bitvec = match filename {
            Some(filename) => {
                if Path::exists(filename.as_ref()) {
                    MmapBitVec::open(&filename, Some(b"!!"), false)?
                } else {
                    MmapBitVec::create(&filename, bits, *b"!!", &header)?
                }
            }
            None => MmapBitVec::from_memory(bits)?,
        };
        Ok(BloomFilter {
            bit_vec: bitvec,
            hashes: n_hashes,
        })
    }

    /// Insert an item into the bloom filter.
    pub fn insert<H>(&mut self, item: H)
    where
        H: Hash,
    {
        let size = self.bit_vec.size();
        let mut hasher = MurmurHasher::new();
        for _ in 0..self.hashes {
            item.hash(&mut hasher);
            let hash: u64 = hasher.finish();
            self.bit_vec.set(hash as usize % size, true);
        }
    }

    /// Check if an item is in the bloom filter already.
    pub fn contains<H>(&self, item: H) -> bool
    where
        H: Hash,
    {
        let size = self.bit_vec.size();
        let mut hasher = MurmurHasher::new();
        for _ in 0..self.hashes {
            item.hash(&mut hasher);
            let hash: u64 = hasher.finish();
            if !self.bit_vec.get(hash as usize % size) {
                return false;
            }
        }
        true
    }
}

#[cfg(test)]
mod test {
    use super::BloomFilter;

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
}
