use std::fs::OpenOptions;
use std::io;
use std::io::{Read, Seek, Write};
use std::mem::transmute;
use std::ops::{Index, Range};
use std::path::Path;

use memmap::{Mmap, Protection};

pub struct BitVec {
    mmap: Mmap,
    header: Vec<u8>,
    pub size: usize,
}

impl BitVec {
    pub fn create_file<P>(filename: P, size: usize, header: &[u8]) -> Result<Self, io::Error> where P: AsRef<Path> {
        let byte_size = ((size - 1) >> 3) as u64 + 1;
        // if we're creating the file, we need to make sure it's bug enough for our
        // purposes (memmap doesn't automatically size the file)
        let mut file = OpenOptions::new().read(true).write(true).create(true).open(filename)?;
        file.set_len(header.len() as u64 + 8 + byte_size)?;
        // file.seek(io::SeekFrom::Start(0))?;
        file.write_all(header)?;
        let serialized_size: [u8; 8] = unsafe { transmute((size as u64).to_be()) };
        println!("{:?}", serialized_size);
        file.write_all(&serialized_size)?;
        let mmap = Mmap::open_with_offset(&file, Protection::ReadWrite, header.len() + 8, byte_size as usize)?;
        Ok(BitVec {
            header: header.to_vec(),
            mmap: mmap,
            size: size,
        })

    }

    pub fn from_file<P>(filename: P, header_size: usize, read_only: bool) -> Result<Self, io::Error> where P: AsRef<Path> {
        let (mut file, protection) = match read_only {
            true => {
                let f = OpenOptions::new().read(true).open(filename)?;
                (f, Protection::Read)
            },
            false => {
                let f = OpenOptions::new().read(true).write(true).open(filename)?;
                (f, Protection::ReadWrite)
            },
        };

        // read the header and the total size
        let mut header = vec![0; header_size];
        file.read_exact(&mut header)?;
        let mut serialized_size = [0; 8];
        file.read_exact(&mut serialized_size)?;
        println!("{:?} {:?}", header, serialized_size);
        let size: u64 = u64::from_be(unsafe { transmute(serialized_size) });
        println!("{}", size);

        // calculate the total numb
        let byte_size = ((size - 1) >> 3) + 1;
        if file.metadata()?.len() != header_size as u64 + 8 + byte_size {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "file not long enough"));
        }

        // load the mmap itself and return the whole shebang
        let mmap = Mmap::open_with_offset(&file, protection, header_size + 8, byte_size as usize)?;
        Ok(BitVec {
            header: header,
            mmap: mmap,
            size: size as usize,
        })
    }

    pub fn from_memory(size: usize)  -> Result<Self, io::Error> {
        let byte_size = ((size - 1) >> 3) as u64 + 1;
        let mmap = Mmap::anonymous(byte_size as usize, Protection::ReadWrite)?;
        Ok(BitVec {
            header: vec![],
            mmap: mmap,
            size: size,
        })
    }

    pub fn header(&self) -> &[u8] {
        &self.header
    }

    pub fn len(&self) -> usize {
        self.size
    }

    pub fn get(&self, ref i: usize) -> bool {
        if *i > self.size {
            panic!("Invalid bit vector index");
        }
        let byte_idx = (i >> 3) as isize;
        let bit_idx = 7 - (i & 7) as u8;
        
        let mmap: *const u8 = self.mmap.ptr();
        unsafe {
            (*mmap.offset(byte_idx) & (1 << bit_idx)) != 0
        }
    }

    pub fn get_range(&self, ref r: Range<usize>) -> Vec<u8> {
        if (r.end - 1) > self.size {
            panic!("Range ends outside of BitVec")
        }
        let byte_idx_st = (r.start >> 3) as usize;
        let byte_idx_en = ((r.end - 1) >> 3) as usize;
        let new_size: usize = (((r.end - r.start) as usize - 1) >> 3) + 1;

        let ptr: *const u8 = self.mmap.ptr();
        let mut v = vec![0; new_size];

        // `shift` is the same as the position of the last bit
        let shift = (r.end & 7) as u8; 
        for (new_idx, old_idx) in (byte_idx_st..byte_idx_en + 1).enumerate() {
            let old_val = unsafe {
                *ptr.offset(old_idx as isize)
            };
            if new_idx > 0 {
                if let Some(shifted_val) = old_val.checked_shr(shift as u32) {
                    v[new_idx - 1] |= shifted_val;
                }
            }
            if new_idx < new_size {
                v[new_idx] |= (old_val & (0xFF >> shift)) << shift;
            } 
        }
        v
    }

    pub fn get_range_u64(&self, ref r: Range<usize>) -> u64 {
        if r.end - r.start > 64 {
            panic!("Range too large (>64)")
        } else if (r.end - 1) > self.size {
            panic!("Range ends outside of BitVec")
        }
        let byte_idx_st = (r.start >> 3) as usize;
        let byte_idx_en = ((r.end - 1) >> 3) as usize;
        let new_size: u8 = (r.end - r.start) as u8;
        
        let mut v;
        let ptr: *const u8 = self.mmap.ptr();

        // read the last byte first
        unsafe {
            v = *ptr.offset(byte_idx_en as isize) as u64;
        }
        // align the end of the data with the end of the u64
        v >>= 7 - ((r.end - 1) & 7);

        let bit_offset = new_size + (r.start & 7) as u8;
        // copy over byte by byte
        // it would be faster to coerce into a u8 and a u64 (in case it spans 9 bytes) and then
        // copy over, but this doesn't work if the start is <8 bytes from the end, so we're doing
        // this for now and we can add a special case for that later
        for (new_idx, old_idx) in (byte_idx_st..byte_idx_en).enumerate() {
            unsafe {
                v |= (*ptr.offset(old_idx as isize) as u64) << (bit_offset - 8u8 * (new_idx as u8 + 1));
            }
        }

        // mask out the high bits in case we copied extra
        v & 0xFFFFFFFFFFFFFFFF >> (64 - new_size)
    }

    pub fn set(&mut self, ref i: usize, ref x: bool) {
        if *i > self.size {
            panic!("Invalid bit vector index");
        }
        let byte_idx = (i >> 3) as isize;
        let bit_idx = 7 - (i & 7) as u8;
        let mmap: *mut u8 = self.mmap.mut_ptr();
        unsafe {
            match *x {
                true => *mmap.offset(byte_idx) |= 1 << bit_idx,
                false => *mmap.offset(byte_idx) &= !(1 << bit_idx),
            }
        }
    }

    pub fn set_range(&mut self, ref r: Range<usize>, ref x: &[u8]) {
        if (r.end - 1) > self.size {
            panic!("Range ends outside of BitVec")
        }
        let new_size: usize = r.end - r.start;
        if ((new_size - 1) >> 3) + 1 != x.len() {
            panic!("Range and array passed are different sizes")
        }
        // we basically ignore r.start except for checking that it roughly 
        // matches up with the size of the byte slice. this works because
        // we're ORing the bits together, so any extra zeros at the front
        // of the first byte in x shouldn't affect the final result at all
        let max_len = 8 * x.len();
        let byte_idx_st = if r.end - 1 > max_len {
            ((r.end - 1 - max_len) >> 3) + 1
        } else {
            0
        };
        let byte_idx_en = ((r.end - 1) >> 3) as usize;

        let mmap: *mut u8 = self.mmap.mut_ptr();

        let shift = 8 - (r.end & 7) as u8; 
        let mask = 0xFFu8.checked_shr((8 - shift) as u32).unwrap_or(0xFF);
        for (val, idx) in x.iter().zip(byte_idx_st..byte_idx_en + 1) {
            let shifted_val = val.checked_shr(8 - shift as u32).unwrap_or(0);
            if idx > 0 && shift != 8{
                unsafe {
                    *mmap.offset(idx as isize - 1) |= shifted_val;
                }
            }
            let shifted_val = (val & mask).checked_shl(shift as u32).unwrap_or(*val);
            unsafe {
                *mmap.offset(idx as isize) |= shifted_val;
            }
        }
    }

    pub fn set_range_u64(&mut self, ref r: Range<usize>, ref x: u64) {
        if (r.end - 1) > self.size {
            panic!("Range ends outside of BitVec")
        }
        let byte_idx_st = (r.start >> 3) as usize;
        let byte_idx_en = ((r.end - 1) >> 3) as usize;
        let new_size: u8 = (r.end - r.start) as u8;

        // split off the front byte
        let size_front = 8u8 - (r.start & 7) as u8;
        let front_byte = if size_front >= new_size {
            (x << (size_front - new_size)) as u8
        } else {
            (x >> (new_size - size_front)) as u8
        };

        // set front with an AND mask to make sure this all the 0's in the
        // new value get masked over the existing 1's
        let mmap: *mut u8 = self.mmap.mut_ptr();
        unsafe {
            match 0xFFu8.checked_shl(size_front as u32) {
                Some(mask) => {
                    *mmap.offset(byte_idx_st as isize) &= mask;
                    *mmap.offset(byte_idx_st as isize) |= front_byte;
                },
                None => {
                    *mmap.offset(byte_idx_st as isize) = front_byte;
                },
            }
        }

        // if the front is all there is, we can bail now
        if byte_idx_st == byte_idx_en {
            return;
        }

        // set the last byte (also a "partial" byte like the first
        let mut size_back = (r.end & 7) as u8;
        if size_back == 0 {
             size_back = 8;
        }
        let back_byte = (x << (64 - new_size + size_back) >> 56) as u8;
        unsafe {
            match 0xFFu8.checked_shr(size_back as u32) {
                Some(mask) => {
                    *mmap.offset(byte_idx_en as isize) &= mask;
                    *mmap.offset(byte_idx_en as isize) |= back_byte;
                },
                None => {
                    *mmap.offset(byte_idx_en as isize) = back_byte;
                },
            }
        }

        // only two bytes long, bail out
        if byte_idx_st + 1 == byte_idx_en {
            return;
        }

        let size_main = new_size - size_front;
        // shift off the first byte (and we don't care about the last byte,
        // because we won't iterate through it) and then make sure that the
        // u64 is stored in the "right" order in memory
        let main_chunk = (x << (64 - size_main)).to_be();

        let bytes: [u8; 8];
        unsafe {
            bytes = transmute(main_chunk);
        }
        for (byte_idx, byte) in ((byte_idx_st + 1)..byte_idx_en).zip(bytes.iter()) {
            unsafe {
                *mmap.offset(byte_idx as isize) = *byte;
            }
        }
    }
}

impl Drop for BitVec {
    fn drop(&mut self) {
        let _ = self.mmap.flush();
    }
}

impl Index<usize> for BitVec {
    // fairly hacky; it would be nice to have Index<Range>, IndexMut<usize>,
    // and IndexMut<Range> methods too, but since these have to return
    // references that's a little tricky
    type Output = bool;
    fn index(&self, idx: usize) -> &Self::Output {
        const TRUE: &'static bool = &true;
        const FALSE: &'static bool = &false;
        match self.get(idx) {
            true => TRUE,
            false => FALSE,
        }
    }
}


#[test]
fn test_bitvec() {
    use std::fs::remove_file;
    // let _ = remove_file("./test");
    let header = vec![];
    let mut b = BitVec::create_file("./test", 100, &header).unwrap();
    b.set(2, true);
    assert!(!b.get(1));
    assert!(b.get(2));
    assert!(!b.get(100));
    drop(b);
    // FIXME: something incredibly weird is happening here where this
    // file gets destroyed during the drop? (sometimes before!) -> this may be
    // a VScode issue?
    assert!(Path::new("./test").exists());

    let mut b = BitVec::from_file("./test", 0, true).unwrap();
    assert!(!b.get(1));
    assert!(b.get(2));
    assert!(!b.get(100));

    let _ = remove_file("./test");
}

#[test]
fn test_bitvec_get_range_u64() {
    let mut b = BitVec::from_memory(128).unwrap();
    b.set(2, true);
    b.set(3, true);
    b.set(5, true);
    assert_eq!(b.get_range_u64(0..8), 52, "indexing within a single byte");
    assert_eq!(b.get_range_u64(0..16), 13312, "indexing multiple bytes");
    assert_eq!(b.get_range_u64(0..64), 3746994889972252672, "indexing the maximum # of bytes");
    assert_eq!(b.get_range_u64(64..128), 0, "indexing the maximum # of bytes to the end");
    assert_eq!(b.get_range_u64(2..10), 208, "indexing across bytes");
    assert_eq!(b.get_range_u64(2..66), 14987979559889010688, "indexing the maximum # of bytes across bytes");
    assert_eq!(b.get_range_u64(115..128), 0, "indexing across bytes to the end");
}

#[test]
fn test_bitvec_get_range() {
    let mut b = BitVec::from_memory(128).unwrap();
    b.set(2, true);
    b.set(3, true);
    b.set(5, true);
    assert_eq!(b.get_range(0..8), &[0x34], "indexing within a single byte");
    assert_eq!(b.get_range(0..16), &[0x34, 0x00], "indexing multiple bytes");
    assert_eq!(b.get_range(0..64), &[0x34, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00], "indexing the maximum # of bytes");
    assert_eq!(b.get_range(64..128), &[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00], "indexing the maximum # of bytes to the end");
    assert_eq!(b.get_range(2..10), &[0xD0], "indexing across bytes");
    assert_eq!(b.get_range(2..66), &[0xD0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00], "indexing the maximum # of bytes across bytes");
    assert_eq!(b.get_range(115..128), &[0x00, 0x00], "indexing across bytes to the end");
}

#[test]
fn test_bitvec_set_range_u64() {
    let mut b = BitVec::from_memory(128).unwrap();
    b.set_range_u64(0..4, 0b0101);
    assert_eq!(b.get_range_u64(0..4), 0b0101);
    b.set_range_u64(5..8, 0b0101);
    assert_eq!(b.get_range_u64(5..8), 0b0101);

    // test across a byte boundary
    b.set_range_u64(6..9, 0b111);
    assert_eq!(b.get_range_u64(6..9), 0b111);

    // test masking works on both sides of a byte boundary
    b.set_range_u64(0..16, 0xFFFF);
    assert_eq!(b.get_range_u64(0..16), 0xFFFF);
    b.set_range_u64(4..12, 0);
    assert_eq!(b.get_range_u64(0..16), 0xF00F);

    // test setting multiple bytes
    b.set_range_u64(20..36, 0xFFFF);
    assert_eq!(b.get_range_u64(20..36), 0xFFFF);

    // set an entire range
    b.set_range_u64(0..64, 0);
    assert_eq!(b.get_range_u64(0..64), 0);
}

#[test]
fn test_bitvec_set_range() {
    let mut b = BitVec::from_memory(128).unwrap();
    b.set_range(0..4, &[0x05]);
    assert_eq!(b.get_range_u64(0..4), 0b0101);
    b.set_range(5..8, &[0x05]);
    assert_eq!(b.get_range_u64(5..8), 0b0101);

    // clear the first part
    b.set_range_u64(0..16, 0);

    // test across a byte boundary
    b.set_range(6..10, &[0x0D]);
    assert_eq!(b.get_range_u64(6..10), 0x0D);

    // test setting multiple bytes
    b.set_range(0..16, &[0xFF, 0xFF]);
    assert_eq!(b.get_range_u64(0..16), 0xFFFF);

    // test setting multiple bytes across boundaries
    b.set_range(20..36, &[0xFF, 0xFF]);
    assert_eq!(b.get_range_u64(20..36), 0xFFFF);

    // testing ORing works
    b.set_range(64..80, &[0xA0, 0x0A]);
    assert_eq!(b.get_range_u64(64..80), 0xA00A);
    b.set_range(64..80, &[0x0B, 0xB0]);
    assert_eq!(b.get_range_u64(64..80), 0xABBA);
}
