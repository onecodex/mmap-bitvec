# mmap-bitvec #

[![CircleCI](https://circleci.com/gh/onecodex/mmap-bitvec.svg?style=svg&circle-token=dcb1850cbbec3e55d28cec4cb5082bb30199cf97)](https://circleci.com/gh/onecodex/mmap-bitvec)

mmap-bitvec is a library for working with mmap-backed bit-vectors and some simple
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

