# mmap-bitvec #

![ci](https://github.com/onecodex/mmap-bitvec/workflows/ci/badge.svg)

`mmap-bitvec` is a library for working with bit-vectors backed by memory-mapped files. Included is a simple Bloom filter built on top of such bit-vectors.

## Examples

Using a memory-mapped bit-vector:
```rust
    // Build an in-memory bit-vector with a capacity of 128 bits.
    use mmap_bitvec::{MmapBitVec, BitVector};

    let mut bitvec = MmapBitVec::from_memory(128).unwrap();
    bitvec.set(2, true);
    assert!(bitvec.get(2));
    assert_eq!(bitvec.get_range(0..8), 0b00100000);

    // Write the bit-vector to disk
    let dir = tempfile::tempdir().unwrap();
    bitvec.save_to_disk(dir.path().join("test"), *b"!!", &[])
        .unwrap();
    let f = MmapBitVec::open(dir.path().join("test"), Some(b"!!"), false).unwrap();
    assert_eq!(f.get(2), true);
```

Using the Bloom filter:
```rust,no_run
    use mmap_bitvec::{BloomFilter};
    // Create a Bloom filter with a capacity of 100 bits that uses 2 hash functions on each insert.
    let mut filter = BloomFilter::new(Some("./test.bloom"), 100, 2).unwrap();
    let (a, b) = (1, 2);
    assert!(!filter.contains(a));
    assert!(!filter.contains(b));

    filter.insert(b);
    assert!(!filter.contains(a));
    assert!(filter.contains(b));
```

## License

This project is licensed under the [MIT license].

[MIT license]: https://github.com/onecodex/mmap-bitvec/blob/master/LICENSE