use std::fs::{metadata, OpenOptions};
use std::io;
use std::io::{Read, Write};
use std::mem::transmute;
use std::ops::Range;
use std::path::Path;

use memmap::{MmapMut, MmapOptions};

use bitvec::{BitVecSlice, BitVector, BIT_VEC_SLICE_SIZE};

/// Bit vector backed by a mmap-ed file
///
/// # Examples
///
/// ```rust
/// use mmap_bitvec::{BitVector, MmapBitVec};
///
/// let mut bv = MmapBitVec::from_memory(128).unwrap();
/// bv.set_range_bytes(2..12, &[0b10, 0b01101101]);
/// assert_eq!(bv.get_range(2..12), 0b1001101101);
/// ```
pub struct MmapBitVec {
    pub mmap: MmapMut,
    pub size: usize,
    header: Box<[u8]>,
}

impl MmapBitVec {
    /// Creates a new `MmapBitVec` file
    ///
    /// The overall size of bit vector (in bits) and a fixed-size header must
    /// also be provided (although the header can be 0-length).
    pub fn create<P>(
        filename: P,
        size: usize,
        magic: [u8; 2],
        header: &[u8],
    ) -> Result<Self, io::Error>
    where
        P: AsRef<Path>,
    {
        assert!(
            header.len() < 65_536,
            "Headers longer than 65636 bytes not supported"
        );

        let byte_size = ((size - 1) >> 3) as u64 + 1;
        // if we're creating the file, we need to make sure it's bug enough for our
        // purposes (memmap doesn't automatically size the file)
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .open(filename)?;
        // two magic bytes, u16 header length, header, u64 bitvec length, bitvec
        let total_header_size = 2 + 2 + header.len() + 8;
        file.set_len(total_header_size as u64 + byte_size)?;
        // file.seek(io::SeekFrom::Start(0))?;

        file.write_all(&magic)?;
        let serialized_header_size: [u8; 2] = unsafe { transmute((header.len() as u16).to_be()) };
        file.write_all(&serialized_header_size)?;
        file.write_all(header)?;
        let serialized_size: [u8; 8] = unsafe { transmute((size as u64).to_be()) };
        file.write_all(&serialized_size)?;

        let mmap = unsafe { MmapOptions::new().offset(total_header_size).map_mut(&file) }?;
        Ok(MmapBitVec {
            mmap,
            size,
            header: header.to_vec().into_boxed_slice(),
        })
    }

    /// Opens an existing `MmapBitVec` file
    ///
    /// If magic bytes are passed, they are checked against the file.
    ///
    /// The header_size must be specified (as it isn't stored in the file to
    /// allow the magic bytes to be set) and there is an optional read_only
    /// property that will lock the underlying mmap from writing.
    pub fn open<P>(filename: P, magic: Option<&[u8; 2]>) -> Result<Self, io::Error>
    where
        P: AsRef<Path>,
    {
        // we have to open with write=true to satisfy MmapMut (which we're
        // using because there's no generic over both MmapMut and Mmap so
        // picking one simplifies the types)
        let mut file = OpenOptions::new().read(true).write(true).open(filename)?;

        // read the magic bytes and (optionally) check if it matches
        let mut file_magic = [0; 2];
        file.read_exact(&mut file_magic)?;
        if let Some(m) = magic {
            if &file_magic != m {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "file has wrong magic bytes {:x?} (expected {:x?})",
                        file_magic, m
                    ),
                ));
            }
        }

        // read the header size and the header
        let mut serialized_header_size = [0; 2];
        file.read_exact(&mut serialized_header_size)?;
        let header_size: usize =
            u16::from_be(unsafe { transmute(serialized_header_size) }) as usize;
        let mut header = vec![0; header_size];
        file.read_exact(&mut header)?;

        // read the bitvec size and calculate the total number of bytes
        let mut serialized_size = [0; 8];
        file.read_exact(&mut serialized_size)?;
        let size: u64 = u64::from_be(unsafe { transmute(serialized_size) });

        let total_header_size = 2 + 2 + header_size + 8;
        let byte_size = ((size - 1) >> 3) + 1;
        if file.metadata()?.len() != total_header_size as u64 + byte_size {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "file should be {} bytes (with {} header), but file is {} bytes",
                    byte_size + total_header_size as u64,
                    total_header_size,
                    file.metadata()?.len(),
                ),
            ));
        }

        // load the mmap itself and return the whole shebang
        let mmap = unsafe { MmapOptions::new().offset(total_header_size).map_mut(&file) }?;

        Ok(MmapBitVec {
            mmap,
            size: size as usize,
            header: header.into_boxed_slice(),
        })
    }

    /// Opens a MmapBitVec file that doesn't have our "standard" file header format
    ///
    ///  Useful for opening legacy bitvec formats.
    pub fn open_no_header<P>(filename: P, offset: usize) -> Result<Self, io::Error>
    where
        P: AsRef<Path>,
    {
        let file_size = metadata(&filename)?.len() as usize;
        let byte_size = file_size - offset;
        let f = OpenOptions::new().read(true).write(true).open(&filename)?;
        let mmap = unsafe { MmapOptions::new().offset(offset).map_mut(&f) }?;

        Ok(MmapBitVec {
            mmap,
            size: byte_size * 8,
            header: Box::new([]),
        })
    }

    /// Creates a MmapBitVec backed by memory.
    ///
    /// Note that unlike the `create` and `open` no header is set.
    /// The MmapBitVec is also read/write by default.
    pub fn from_memory(size: usize) -> Result<Self, io::Error> {
        let byte_size = ((size - 1) >> 3) as u64 + 1;
        let mmap = MmapOptions::new().len(byte_size as usize).map_anon()?;
        Ok(MmapBitVec {
            mmap,
            size,
            header: vec![].into_boxed_slice(),
        })
    }

    // Returns the header
    pub fn header(&self) -> &[u8] {
        &self.header
    }

    /// Read/copy an unaligned chunk of the MmapBitVec
    ///
    /// # Panics
    ///
    /// Explicitly panics if the end location, r.end, is outside the bounds
    /// of the bit vector. A panic may also occur if r.start is greater than
    /// r.end.
    pub fn get_range_bytes(&self, r: Range<usize>) -> Vec<u8> {
        if r.end > self.size {
            panic!("Range ends outside of BitVec")
        }
        let byte_idx_st = (r.start >> 3) as usize;
        let byte_idx_en = ((r.end - 1) >> 3) as usize;
        let new_size: usize = (((r.end - r.start) as usize - 1) >> 3) + 1;

        let ptr: *const u8 = self.mmap.as_ptr();
        let mut v = vec![0; new_size];

        // `shift` is the same as the position of the last bit
        let shift = (r.end & 7) as u8;
        for (new_idx, old_idx) in (byte_idx_st..=byte_idx_en).enumerate() {
            let old_val = unsafe { order_byte(*ptr.add(old_idx)) };
            if new_idx > 0 {
                if let Some(shifted_val) = old_val.checked_shr(u32::from(shift)) {
                    v[new_idx - 1] |= shifted_val;
                }
            }
            if new_idx < new_size {
                v[new_idx] |= (old_val & (0xFF >> shift)) << shift;
            }
        }
        v
    }

    /// Set a unaligned range of bits in the bit vector from a byte slice.
    ///
    /// Note this operation ORs the passed byteslice and the existing bitmask.
    ///
    /// # Panics
    ///
    /// Explicitly panics if the end location, r.end, is outside the bounds
    /// of the bit vector or if the byte slice passed in is a different size
    /// from the range specified. A panic may also occur if r.start is greater
    /// than r.end.
    pub fn set_range_bytes(&mut self, r: Range<usize>, x: &[u8]) {
        if r.end > self.size {
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

        let mmap: *mut u8 = self.mmap.as_mut_ptr();

        let shift = 8 - (r.end & 7) as u8;
        let mask = 0xFFu8.checked_shr(u32::from(8 - shift)).unwrap_or(0xFF);
        for (val, idx) in x.iter().zip(byte_idx_st..=byte_idx_en) {
            let shifted_val = val.checked_shr(u32::from(8 - shift)).unwrap_or(0);
            if idx > 0 && shift != 8 {
                unsafe {
                    *mmap.offset(idx as isize - 1) |= order_byte(shifted_val);
                }
            }
            let shifted_val = (val & mask).checked_shl(u32::from(shift)).unwrap_or(*val);
            unsafe {
                *mmap.add(idx) |= order_byte(shifted_val);
            }
        }
    }
}

impl BitVector for MmapBitVec {
    /// Returns the length (in bits) of the bit vector
    fn size(&self) -> usize {
        self.size
    }

    /// Check a single value in the MmapBitVec, returning its true/false status
    ///
    /// # Panics
    ///
    /// Panics if the location, i, is outside the bounds of the bit vector
    fn get(&self, i: usize) -> bool {
        if i > self.size {
            panic!("Invalid bit vector index");
        }
        let byte_idx = (i >> 3) as isize;
        #[cfg(not(feature = "backward_bytes"))]
        let bit_idx = 7 - (i & 7) as u8;
        #[cfg(feature = "backward_bytes")]
        let bit_idx = (i & 7) as u8;

        let mmap: *const u8 = self.mmap.as_ptr();
        unsafe { (*mmap.offset(byte_idx) & (1 << bit_idx)) != 0 }
    }

    /// Read an unaligned chunk of the MmapBitVec into a u64/u128
    ///
    /// # Panics
    ///
    /// Explicitly panics if the end location, r.end, is outside the bounds
    /// of the bit vector or if the range specified is greater than 64 bits.
    /// (Use `get_range` instead if you need to read larger chunks) A panic
    /// may also occur if r.start is greater than r.end.
    fn get_range(&self, r: Range<usize>) -> BitVecSlice {
        if r.end - r.start > BIT_VEC_SLICE_SIZE as usize {
            panic!(format!("Range too large (>{})", BIT_VEC_SLICE_SIZE))
        } else if r.end > self.size {
            panic!("Range ends outside of BitVec")
        }
        let byte_idx_st = (r.start >> 3) as usize;
        let byte_idx_en = ((r.end - 1) >> 3) as usize;
        let new_size: u8 = (r.end - r.start) as u8;

        let mut v;
        let ptr: *const u8 = self.mmap.as_ptr();

        // read the last byte first
        unsafe {
            v = BitVecSlice::from(order_byte(*ptr.add(byte_idx_en)));
        }
        // align the end of the data with the end of the u64/u128
        v >>= 7 - ((r.end - 1) & 7);

        if r.start < self.size - BIT_VEC_SLICE_SIZE as usize
            && cfg!(not(feature = "backward_bytes"))
        {
            // really nasty/unsafe, but we're just reading a u64/u128 out instead of doing it
            // byte-wise --- also does not work with legacy mode!!!
            unsafe {
                // we have to transmute since we don't know if it's a u64 or u128
                #[allow(clippy::transmute_ptr_to_ptr)]
                let lg_ptr: *const BitVecSlice = transmute(ptr.add(byte_idx_st));
                v |= (*lg_ptr).to_be() << (r.start & 7) >> (BIT_VEC_SLICE_SIZE - new_size);
            }
        } else {
            // special case if we can't get a whole u64 out without running outside the buffer
            let bit_offset = new_size + (r.start & 7) as u8;
            for (new_idx, old_idx) in (byte_idx_st..byte_idx_en).enumerate() {
                unsafe {
                    v |= BitVecSlice::from(order_byte(*ptr.add(old_idx)))
                        << (bit_offset - 8u8 * (new_idx as u8 + 1));
                }
            }
        }

        // mask out the high bits in case we copied extra
        v & (BitVecSlice::max_value() >> (BIT_VEC_SLICE_SIZE - new_size))
    }

    /// Set a single bit in the bit vector
    ///
    /// # Panics
    ///
    /// Panics if the location, i, is outside the bounds of the bit vector
    fn set(&mut self, i: usize, x: bool) {
        if i > self.size {
            panic!("Invalid bit vector index");
        }
        let byte_idx = (i >> 3) as isize;
        #[cfg(not(feature = "backward_bytes"))]
        let bit_idx = 7 - (i & 7) as u8;
        #[cfg(feature = "backward_bytes")]
        let bit_idx = (i & 7) as u8;

        let mmap: *mut u8 = self.mmap.as_mut_ptr();
        unsafe {
            if x {
                *mmap.offset(byte_idx) |= 1 << bit_idx
            } else {
                *mmap.offset(byte_idx) &= !(1 << bit_idx)
            }
        }
    }

    /// Set a unaligned range of bits using a u64.
    ///
    /// Note this operation ORs the passed u64 and the existing bitmask
    ///
    /// # Panics
    ///
    /// Explicitly panics if the end location, r.end, is outside the bounds
    /// of the bit vector. A panic may also occur if r.start is greater than
    /// r.end.
    fn set_range(&mut self, r: Range<usize>, x: BitVecSlice) {
        if r.end > self.size {
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
        let mmap: *mut u8 = self.mmap.as_mut_ptr();
        unsafe {
            *mmap.add(byte_idx_st) |= order_byte(front_byte);
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
        let back_byte = (x << (BIT_VEC_SLICE_SIZE - size_back) >> (BIT_VEC_SLICE_SIZE - 8)) as u8;
        unsafe {
            *mmap.add(byte_idx_en) |= order_byte(back_byte);
        }

        // only two bytes long, bail out
        if byte_idx_st + 1 == byte_idx_en {
            return;
        }

        let size_main = new_size - size_front;
        // shift off the first byte (and we don't care about the last byte,
        // because we won't iterate through it) and then make sure that the
        // u64 is stored in the "right" order in memory
        let main_chunk = (x << (BIT_VEC_SLICE_SIZE - size_main)).to_be();

        let bytes: [u8; BIT_VEC_SLICE_SIZE as usize / 8];
        unsafe {
            bytes = transmute(main_chunk);
        }
        for (byte_idx, byte) in ((byte_idx_st + 1)..byte_idx_en).zip(bytes.iter()) {
            unsafe {
                *mmap.add(byte_idx) |= order_byte(*byte);
            }
        }
    }

    /// Zeros out a chunk of the bitvector
    ///
    /// Note this operation can be used to AND a bitmask into the bitvector
    ///
    /// # Panics
    ///
    /// Explicitly panics if the end location, r.end, is outside the bounds
    /// of the bit vector. A panic may also occur if r.start is greater than
    /// r.end.
    fn clear_range(&mut self, r: Range<usize>) {
        if (r.end - 1) > self.size {
            panic!("Range ends outside of BitVec")
        }
        let byte_idx_st = (r.start >> 3) as usize;
        let byte_idx_en = ((r.end - 1) >> 3) as usize;

        let mmap: *mut u8 = self.mmap.as_mut_ptr();

        // set front with an AND mask to make sure this all the 0's in the
        // new value get masked over the existing 1's
        let size_front = 8u8 - (r.start & 7) as u8;
        if let Some(mask) = 0xFFu8.checked_shl(u32::from(size_front)) {
            unsafe {
                *mmap.add(byte_idx_st) &= order_byte(mask);
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
        if let Some(mask) = 0xFFu8.checked_shr(u32::from(size_back)) {
            unsafe {
                *mmap.add(byte_idx_en) &= order_byte(mask);
            }
        }

        // only two bytes long, bail out
        if byte_idx_st + 1 == byte_idx_en {
            return;
        }

        // zero out all the middle bytes (maybe there's a faster way?)
        for byte_idx in (byte_idx_st + 1)..byte_idx_en {
            unsafe {
                *mmap.add(byte_idx) = 0u8;
            }
        }
    }

    fn rank(&self, r: Range<usize>) -> usize {
        let byte_idx_st = (r.start >> 3) as usize;
        let byte_idx_en = ((r.end - 1) >> 3) as usize;
        let mmap: *const u8 = self.mmap.as_ptr();

        let mut bit_count = 0usize;

        let size_front = 8u8 - (r.start & 7) as u8;
        if let Some(mask) = 0xFFu8.checked_shl(u32::from(size_front)) {
            let byte = unsafe { *mmap.add(byte_idx_st) & order_byte(mask) };
            bit_count += byte.count_ones() as usize
        }

        // if the front is all there is, we can bail now
        if byte_idx_st == byte_idx_en {
            return bit_count;
        }

        // get the last byte (also a "partial" byte like the first)
        let mut size_back = (r.end & 7) as u8;
        if size_back == 0 {
            size_back = 8;
        }
        if let Some(mask) = 0xFFu8.checked_shr(u32::from(size_back)) {
            let byte = unsafe { *mmap.add(byte_idx_en) & order_byte(mask) };
            bit_count += byte.count_ones() as usize
        }

        // only two bytes long, bail out
        if byte_idx_st + 1 == byte_idx_en {
            return bit_count;
        }

        // get all the intermediate bytes (which don't need masking)
        for byte_idx in (byte_idx_st + 1)..byte_idx_en {
            let byte = unsafe { *mmap.add(byte_idx) };
            bit_count += byte.count_ones() as usize
        }

        bit_count
    }

    fn select(&self, n: usize, start: usize) -> Option<usize> {
        let byte_idx_st = (start >> 3) as usize;
        let size_front = 8u8 - (start & 7) as u8;
        let mmap: *const u8 = self.mmap.as_ptr();

        let mut rank_count = 0usize;
        for byte_idx in byte_idx_st.. {
            let mut byte = unsafe { *mmap.add(byte_idx) };
            if byte_idx == byte_idx_st {
                if let Some(mask) = 0xFFu8.checked_shl(u32::from(size_front)) {
                    byte &= mask;
                }
            }
            if rank_count + byte.count_ones() as usize >= n {
                for bit_idx in 0..8 {
                    if (0b1000_0000 >> bit_idx) & byte != 0 {
                        rank_count += 1;
                    }
                    if rank_count == n {
                        return Some((byte_idx << 3) + bit_idx);
                    }
                }
                panic!("Select failed to find enough bits (but there were!)");
            }
            rank_count += byte.count_ones() as usize;
        }
        None
    }
}

/// Drop is implemented for `BitVec` to explicitly flush any changes to the
/// file before the memory map is closed.
impl Drop for MmapBitVec {
    fn drop(&mut self) {
        let _ = self.mmap.flush();
    }
}

#[inline]
#[cfg(not(feature = "backward_bytes"))]
fn order_byte(b: u8) -> u8 {
    b
}

#[inline]
#[cfg(feature = "backward_bytes")]
fn order_byte(b: u8) -> u8 {
    // in python: ','.join(str(eval('{:08b}b0'.format(i)[::-1])) for i in range(256))
    #[rustfmt::skip]
    const BACKWARDS: [u8; 256] = [
        0,128,64,192,32,160,96,224,16,144,80,208,48,176,112,240,8,136,72,
        200,40,168,104,232,24,152,88,216,56,184,120,248,4,132,68,196,36,
        164,100,228,20,148,84,212,52,180,116,244,12,140,76,204,44,172,108,
        236,28,156,92,220,60,188,124,252,2,130,66,194,34,162,98,226,18,146,
        82,210,50,178,114,242,10,138,74,202,42,170,106,234,26,154,90,218,58,
        186,122,250,6,134,70,198,38,166,102,230,22,150,86,214,54,182,118,246,
        14,142,78,206,46,174,110,238,30,158,94,222,62,190,126,254,1,129,65,
        193,33,161,97,225,17,145,81,209,49,177,113,241,9,137,73,201,41,169,
        105,233,25,153,89,217,57,185,121,249,5,133,69,197,37,165,101,229,21,
        149,85,213,53,181,117,245,13,141,77,205,45,173,109,237,29,157,93,221,
        61,189,125,253,3,131,67,195,35,163,99,227,19,147,83,211,51,179,115,
        243,11,139,75,203,43,171,107,235,27,155,91,219,59,187,123,251,7,135,
        71,199,39,167,103,231,23,151,87,215,55,183,119,247,15,143,79,207,47,
        175,111,239,31,159,95,223,63,191,127,255
    ];
    BACKWARDS[b as usize]
}

#[cfg(test)]
mod test {
    use std::path::Path;

    use super::MmapBitVec;
    use bitvec::BitVector;

    #[test]
    fn test_bitvec() {
        use std::fs::remove_file;

        let header = vec![];
        let mut b = MmapBitVec::create("./test", 100, *b"!!", &header).unwrap();
        b.set(2, true);
        assert!(!b.get(1));
        assert!(b.get(2));
        assert!(!b.get(100));
        drop(b);
        assert!(Path::new("./test").exists());

        let b = MmapBitVec::open("./test", Some(b"!!")).unwrap();
        assert!(!b.get(1));
        assert!(b.get(2));
        assert!(!b.get(100));

        remove_file("./test").unwrap();
    }

    #[test]
    fn test_open_no_header() {
        use std::fs::remove_file;

        let header = vec![];
        // the bitvector has to be a size with a multiple of 8 because the
        // no_header code always opens to the end of the last byte
        let _ = MmapBitVec::create("./test_headerless", 80, *b"!!", &header).unwrap();
        assert!(Path::new("./test_headerless").exists());
        let b = MmapBitVec::open_no_header("./test_headerless", 12).unwrap();
        assert_eq!(b.size(), 80);
        remove_file("./test_headerless").unwrap();
    }

    #[test]
    fn test_bitvec_get_range() {
        let mut b = MmapBitVec::from_memory(128).unwrap();
        b.set(2, true);
        b.set(3, true);
        b.set(5, true);
        assert_eq!(b.get_range(0..8), 52, "indexing within a single byte");
        assert_eq!(b.get_range(0..16), 13312, "indexing multiple bytes");
        assert_eq!(
            b.get_range(0..64),
            3_746_994_889_972_252_672,
            "indexing the maximum # of bytes"
        );
        assert_eq!(
            b.get_range(64..128),
            0,
            "indexing the maximum # of bytes to the end"
        );
        assert_eq!(b.get_range(2..10), 208, "indexing across bytes");
        assert_eq!(
            b.get_range(2..66),
            14_987_979_559_889_010_688,
            "indexing the maximum # of bytes across bytes"
        );
        assert_eq!(b.get_range(115..128), 0, "indexing across bytes to the end");
    }

    #[test]
    fn test_bitvec_get_range_bytes() {
        let mut b = MmapBitVec::from_memory(128).unwrap();
        b.set(2, true);
        b.set(3, true);
        b.set(5, true);
        assert_eq!(
            b.get_range_bytes(0..8),
            &[0x34],
            "indexing within a single byte"
        );
        assert_eq!(
            b.get_range_bytes(0..16),
            &[0x34, 0x00],
            "indexing multiple bytes"
        );
        assert_eq!(
            b.get_range_bytes(0..64),
            &[0x34, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
            "indexing the maximum # of bytes"
        );
        assert_eq!(
            b.get_range_bytes(64..128),
            &[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
            "indexing the maximum # of bytes to the end"
        );
        assert_eq!(b.get_range_bytes(2..10), &[0xD0], "indexing across bytes");
        assert_eq!(
            b.get_range_bytes(2..66),
            &[0xD0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
            "indexing the maximum # of bytes across bytes"
        );
        assert_eq!(
            b.get_range_bytes(115..128),
            &[0x00, 0x00],
            "indexing across bytes to the end"
        );
    }

    #[test]
    fn test_bitvec_set_range() {
        let mut b = MmapBitVec::from_memory(128).unwrap();
        b.set_range(0..4, 0b0101);
        assert_eq!(b.get_range(0..4), 0b0101);
        b.set_range(5..8, 0b0101);
        assert_eq!(b.get_range(5..8), 0b0101);
        b.set_range(123..127, 0b0101);
        assert_eq!(b.get_range(123..127), 0b0101);

        // test across a byte boundary
        b.set_range(6..9, 0b111);
        assert_eq!(b.get_range(6..9), 0b111);

        // test zeroing works on both sides of a byte boundary
        b.set_range(0..16, 0xFFFF);
        assert_eq!(b.get_range(0..16), 0xFFFF);
        b.clear_range(4..12);
        assert_eq!(b.get_range(0..16), 0xF00F);

        // test setting multiple bytes (and that overflow doesn't happen)
        b.set_range(20..36, 0xFFFF);
        assert_eq!(b.get_range(16..20), 0x0);
        assert_eq!(b.get_range(20..36), 0xFFFF);
        assert_eq!(b.get_range(36..44), 0x0);

        // set an entire range
        assert_eq!(b.get_range(39..103), 0x0);
        b.set_range(39..103, 0xABCD1234);
        assert_eq!(b.get_range(39..103), 0xABCD1234);
    }

    #[test]
    fn test_bitvec_set_range_bytes() {
        let mut b = MmapBitVec::from_memory(128).unwrap();
        b.set_range_bytes(0..4, &[0x05]);
        assert_eq!(b.get_range(0..4), 0b0101);
        b.set_range_bytes(5..8, &[0x05]);
        assert_eq!(b.get_range(5..8), 0b0101);

        // clear the first part
        b.clear_range(0..16);

        // test across a byte boundary
        b.set_range_bytes(6..10, &[0x0D]);
        assert_eq!(b.get_range(6..10), 0x0D);

        // test setting multiple bytes
        b.set_range_bytes(0..16, &[0xFF, 0xFF]);
        assert_eq!(b.get_range(0..16), 0xFFFF);

        // test setting multiple bytes across boundaries
        b.set_range_bytes(20..36, &[0xFF, 0xFF]);
        assert_eq!(b.get_range(20..36), 0xFFFF);

        // testing ORing works
        b.set_range_bytes(64..80, &[0xA0, 0x0A]);
        assert_eq!(b.get_range(64..80), 0xA00A);
        b.set_range_bytes(64..80, &[0x0B, 0xB0]);
        assert_eq!(b.get_range(64..80), 0xABBA);
    }
}
