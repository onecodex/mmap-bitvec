extern crate criterion;
extern crate memmap;
extern crate mmap_bitvec;

use std::fs::OpenOptions;
use std::mem::transmute;
use std::ops::Range;

use memmap::{MmapMut, MmapOptions};
use mmap_bitvec::{BitVector, MmapBitVec};

use criterion::{criterion_group, criterion_main, Criterion};

type BitVecSlice = u64;
const BIT_VEC_SLICE_SIZE: u8 = 64;
const FILENAME: &str = "./bfield.mmap";

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

fn get_range_simplified(mmap: &MmapMut, size: usize, l: usize) -> BitVecSlice {
    let byte_idx_st = (l >> 3) as usize;
    let byte_idx_en = ((l + 63) >> 3) as usize;
    let new_size: u8 = 64 as u8;

    let ptr: *const u8 = mmap.as_ptr();

    // read the last byte first
    let end = unsafe { *ptr.offset(byte_idx_en as isize) };
    // align the end of the data with the end of the u64/u128
    let mut v = BitVecSlice::from(end);
    v >>= 7 - ((l + 63) & 7);

    if l < size - BIT_VEC_SLICE_SIZE as usize {
        // really nasty/unsafe, but we're just reading a u64/u128 out instead of doing it
        // byte-wise --- also does not work with legacy mode!!!
        unsafe {
            let lg_ptr: *const BitVecSlice = transmute(ptr.offset(byte_idx_st as isize));
            v |= (*lg_ptr).to_be() << (l & 7) >> (BIT_VEC_SLICE_SIZE - new_size);
        }
    } else {
        // special case if we can't get a whole u64 out without running outside the buffer
        let bit_offset = new_size + (l & 7) as u8;
        for (new_idx, old_idx) in (byte_idx_st..byte_idx_en).enumerate() {
            unsafe {
                v |= BitVecSlice::from(*ptr.offset(old_idx as isize))
                    << (bit_offset - 8u8 * (new_idx as u8 + 1));
            }
        }
    }

    // mask out the high bits in case we copied extra
    v & (BitVecSlice::max_value() >> (BIT_VEC_SLICE_SIZE - new_size))
}

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
                v |= BitVecSlice::from(*ptr.offset(old_idx as isize))
                    << (bit_offset - 8u8 * (new_idx as u8 + 1));
            }
        }
    }

    // mask out the high bits in case we copied extra
    v & (BitVecSlice::max_value() >> (BIT_VEC_SLICE_SIZE - new_size))
}

fn bench_get_range_simplified() {
    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .open(FILENAME)
        .unwrap();
    let size = file.metadata().unwrap().len() as usize;
    let mmap = unsafe { MmapOptions::new().map_mut(&file).unwrap() };

    let mut r = 0;
    let mut i = 1;
    for _ in 0..100000 {
        let l = i % (size - 64);
        r += get_range_simplified(&mmap, size, l).count_ones();
        i = next_random(i);
    }
}

fn bench_get_range() {
    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .open(FILENAME)
        .unwrap();
    let size = file.metadata().unwrap().len() as usize;
    let mmap = unsafe { MmapOptions::new().map_mut(&file).unwrap() };

    let mut r = 0;
    let mut i = 1;
    for _ in 0..100000 {
        let l = i % (size - 64);
        r += get_range(&mmap, size, l..l + 64).count_ones();
        i = next_random(i);
    }
}

fn bench_get_range_actual() {
    let bitvec = MmapBitVec::open_no_header(FILENAME, 0).unwrap();
    let mut r = 0;
    let mut i = 1;
    for _ in 0..100000 {
        let l = i % (bitvec.size() - 64);
        r += bitvec.get_range(l..l + 64).count_ones();
        i = next_random(i);
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("get_range_actual", |b| b.iter(|| bench_get_range_actual()));
    c.bench_function("get_range_simplified", |b| {
        b.iter(|| bench_get_range_simplified())
    });
    c.bench_function("get_range", |b| b.iter(|| bench_get_range()));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
