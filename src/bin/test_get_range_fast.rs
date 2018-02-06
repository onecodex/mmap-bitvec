extern crate mmap_bitvec;
extern crate memmap;

use std::fs::OpenOptions;
use std::env::args;
use std::mem::transmute;
use std::ops::Range;

use mmap_bitvec::{MmapBitVec, BitVector};
use memmap::{MmapOptions, MmapMut};

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


type BitVecSlice = u64;
const BIT_VEC_SLICE_SIZE: u8 = 64;


fn get_range(mmap: &MmapMut, size: usize, r: Range<usize>) -> BitVecSlice {
    if r.end - r.start > BIT_VEC_SLICE_SIZE as usize {
        panic!(format!("Range too large (>{})", BIT_VEC_SLICE_SIZE))
    } else if r.end > size {
        panic!("Range ends outside of BitVec")
    }
    let byte_idx_st = (r.start >> 3) as usize;
    let byte_idx_en = ((r.end - 1) >> 3) as usize;
    let new_size: u8 = (r.end - r.start) as u8;

    let mut v;
    let ptr: *const u8 = mmap.as_ptr();

    // read the last byte first
    unsafe {
        v = BitVecSlice::from(*ptr.offset(byte_idx_en as isize));
    }
    // align the end of the data with the end of the u64/u128
    v >>= 7 - ((r.end - 1) & 7);


    if r.start < size - BIT_VEC_SLICE_SIZE as usize {
        // really nasty/unsafe, but we're just reading a u64/u128 out instead of doing it
        // byte-wise --- also does not work with legacy mode!!!
        unsafe {
            let lg_ptr: *const BitVecSlice = transmute(ptr.offset(byte_idx_st as isize));
            v |= (*lg_ptr).to_be() << (r.start & 7) >> (BIT_VEC_SLICE_SIZE - new_size);
        }
    } else {
        // special case if we can't get a whole u64 out without running outside the buffer
        let bit_offset = new_size + (r.start & 7) as u8;
        for (new_idx, old_idx) in (byte_idx_st..byte_idx_en).enumerate() {
            unsafe {
                v |= BitVecSlice::from(*ptr.offset(old_idx as isize)) <<
                    (bit_offset - 8u8 * (new_idx as u8 + 1));
            }
        }
    }

    // mask out the high bits in case we copied extra
    v & (BitVecSlice::max_value() >> (BIT_VEC_SLICE_SIZE - new_size))
}


fn main() {
    let filename = args().nth(1).expect("need [filename] [n_samples]");
    let n_samples = args().nth(2).expect("need [n_samples]").parse::<usize>().expect("n_samples must be an integer");

    // let file = OpenOptions::new().read(true).write(true).open(filename).unwrap();
    // let size = (8 * file.metadata().unwrap().len()) as usize;
    // let mmap = unsafe {
    //     MmapOptions::new().map_mut(&file).unwrap()
    // };

    let bitvec = MmapBitVec::open_no_header(filename, 0).unwrap();
    let size = bitvec.size();

    let mut r = 0;
    let mut i = 1;
    for _ in 0..n_samples {
        let l = i % (size - 64);
        r += get_range(&bitvec.mmap, size, l..l+64).count_ones();
        i = next_random(i);
    }
    println!("{}", r);
}
