# mmap-bitvec #

![ci](https://github.com/onecodex/mmap-bitvec/workflows/ci/badge.svg)

`mmap-bitvec` is a library for working with bit-vectors backed by memory-mapped files and some simple
data structures derived from bit-vectors.

## Benchmarks

To run benchmarks you need to download a bfield.mmap file, I used `s3://refgenomics-datafiles/dbs/mg_targeted_loci_20160517/bfield.mmap` in
the root of the repo and then run `cargo +nightly bench`.

## Example

```rust
    let mut b = BitVec::from_memory(128).unwrap();

    b.set(2, true);
    assert!(b.get(2));
    assert_eq!(b.get_range(0..8), 0b00100000);
```

