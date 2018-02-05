extern crate mmap_bitvec;

use std::env::args;

use mmap_bitvec::{MmapBitVec, BitVector};

// we could use an RNG, but I want to make sure everything is
// as comparable as possible
fn next_random(n: usize) -> usize {
    // https://en.wikipedia.org/wiki/Xorshift
    let mut x = n as u32;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    x as usize
}

fn main() {
    let filename = args().nth(1).expect("need [filename] [n_samples]");
    let n_samples = args().nth(2).expect("need [n_samples]").parse::<usize>().expect("n_samples must be an integer");

    let bitvec = MmapBitVec::open_no_header(filename, 0).unwrap();
    let mut r = 0;
    let mut i = 1;
    for _ in 0..n_samples {
        let l = i % (bitvec.size() - 64);
        r += bitvec.get_range(l..l+64).count_ones();
        i = next_random(i);
    }
    println!("{}", r);
}
