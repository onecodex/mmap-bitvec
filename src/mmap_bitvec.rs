use std::fs::{metadata, OpenOptions};
use std::io;
use std::io::{Read, Write};
use std::mem::transmute;
use std::ops::Range;
use std::path::Path;

use memmap2::{Mmap, MmapMut, MmapOptions};

use crate::bitvec::BitVector;

/// Enum representing either a read-only mmap or a mutable mmap
pub enum MmapKind {
    /// A mutable mmap
    MmapMut(MmapMut),
    /// A read-only mmap
    Mmap(Mmap),
}

impl MmapKind {
    /// Get a non-mutable pointer to the mmap
    #[inline]
    pub fn as_ptr(&self) -> *const u8 {
        match self {
            MmapKind::MmapMut(x) => x.as_ptr(),
            MmapKind::Mmap(x) => x.as_ptr(),
        }
    }

    /// Get a mutable pointer to the mmap
    #[inline]
    pub fn as_mut_ptr(&mut self) -> Result<*mut u8, io::Error> {
        match self {
            MmapKind::MmapMut(x) => Ok(x.as_mut_ptr()),
            MmapKind::Mmap(_) => Err(io::Error::new(
                io::ErrorKind::Other,
                "attempted to get a mutable pointer to a read-only mmap",
            )),
        }
    }

    /// Flush to disk. A no-op if the mmap is read-only
    #[inline]
    pub fn flush(&mut self) -> Result<(), io::Error> {
        match self {
            MmapKind::MmapMut(x) => x.flush(),
            MmapKind::Mmap(_) => Ok(()),
        }
    }

    /// Gets the slice
    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        match self {
            MmapKind::MmapMut(x) => x.as_ref(),
            MmapKind::Mmap(x) => x.as_ref(),
        }
    }
}

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
    /// The mmap we are using, either a mutable or read-only one
    pub mmap: MmapKind,
    /// Number of bits in the bitvector
    pub size: usize,
    /// Arbitrary data prepended to file (when file-backed)
    header: Box<[u8]>,
    /// controls whether the mapping is backed by a file (see `MAP_ANONYMOUS` here: <https://man7.org/linux/man-pages/man2/mmap.2.html>)
    is_map_anonymous: bool,
}

fn create_bitvec_file(
    filename: &Path,
    size: usize,
    magic: Option<[u8; 2]>,
    header: &[u8],
) -> Result<(std::fs::File, u64), io::Error> {
    let byte_size = ((size - 1) >> 3) as u64 + 1;
    let mut file = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .open(filename)?;
    let magic_len = if let Some(m) = magic { m.len() } else { 0 };
    // two magic bytes indicating file type (if passed in), u16 header length, header, u64 bitvec length, bitvec
    let total_header_size = (magic_len + 2 + header.len() + 8) as u64;
    file.set_len(total_header_size + byte_size)?;

    if let Some(m) = magic {
        file.write_all(&m)?;
    }

    let serialized_header_size: [u8; 2] = (header.len() as u16).to_be_bytes();
    file.write_all(&serialized_header_size)?;
    file.write_all(header)?;
    let serialized_size: [u8; 8] = (size as u64).to_be_bytes();
    file.write_all(&serialized_size)?;

    Ok((file, total_header_size))
}

impl MmapBitVec {
    /// Creates a new `MmapBitVec` file
    ///
    /// The overall size of bit vector (in bits) and a fixed-size header must
    /// also be provided (although the header can be 0-length).
    pub fn create<P: AsRef<Path>>(
        filename: P,
        size: usize,
        magic: Option<[u8; 2]>,
        header: &[u8],
    ) -> Result<Self, io::Error> {
        assert!(
            header.len() < 65_536,
            "Headers longer than 65636 bytes not supported"
        );

        let (file, total_header_size) = create_bitvec_file(filename.as_ref(), size, magic, header)?;
        let mmap = unsafe { MmapOptions::new().offset(total_header_size).map_mut(&file) }?;
        Ok(MmapBitVec {
            mmap: MmapKind::MmapMut(mmap),
            size,
            header: header.to_vec().into_boxed_slice(),
            is_map_anonymous: false,
        })
    }

    /// Opens an existing `MmapBitVec` file
    ///
    /// If magic bytes are passed to indicate file type, they are checked against the file.
    ///
    /// The header size must be specified (as it isn't stored in the file to
    /// allow the magic bytes to be set) and there is an optional `read_only`
    /// property that will lock the underlying mmap from writing.
    pub fn open<P>(filename: P, magic: Option<&[u8; 2]>, read_only: bool) -> Result<Self, io::Error>
    where
        P: AsRef<Path>,
    {
        // we have to open with write access to satisfy `MmapMut` (which we're
        // using because there's no generic over both MmapMut and Mmap so
        // picking one simplifies the types)
        let mut file = OpenOptions::new()
            .read(true)
            .write(!read_only)
            .open(filename)?;

        if let Some(m) = magic {
            // read the magic bytes and (optionally) check if it matches
            let mut file_magic = [0; 2];
            file.read_exact(&mut file_magic)?;

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

        let magic_len = if let Some(m) = magic { m.len() } else { 0 };
        let total_header_size = (magic_len + 2 + header_size + 8) as u64;
        let byte_size = ((size - 1) >> 3) + 1;
        if file.metadata()?.len() != total_header_size + byte_size {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "file should be {} bytes (with {} header), but file is {} bytes",
                    byte_size + total_header_size,
                    total_header_size,
                    file.metadata()?.len(),
                ),
            ));
        }

        let mmap = if read_only {
            let mmap = unsafe { MmapOptions::new().offset(total_header_size).map(&file) }?;
            MmapKind::Mmap(mmap)
        } else {
            let mmap = unsafe { MmapOptions::new().offset(total_header_size).map_mut(&file) }?;
            MmapKind::MmapMut(mmap)
        };

        Ok(MmapBitVec {
            mmap,
            size: size as usize,
            header: header.into_boxed_slice(),
            is_map_anonymous: false,
        })
    }

    /// Opens a `MmapBitVec` file that doesn't have our "standard" file header format
    /// TODO: what is the standard file header? if we put in the docstring on the struct we can say to refer to that here
    pub fn open_no_header<P>(filename: P, offset: usize) -> Result<Self, io::Error>
    where
        P: AsRef<Path>,
    {
        let file_size = metadata(&filename)?.len() as usize;
        let byte_size = file_size - offset;
        let f = OpenOptions::new().read(true).write(false).open(&filename)?;
        let mmap = unsafe { MmapOptions::new().offset(offset as u64).map(&f) }?;

        Ok(MmapBitVec {
            mmap: MmapKind::Mmap(mmap),
            size: byte_size * 8,
            header: Box::new([]),
            is_map_anonymous: false,
        })
    }

    /// Creates an in-memory  `MmapBitVec` (not backed by a file).
    ///
    /// Note that unlike the `create` and `open` no header is set.
    /// The MmapBitVec is also read/write by default.
    pub fn from_memory(size: usize) -> Result<Self, io::Error> {
        let byte_size = ((size - 1) >> 3) as u64 + 1;
        let mmap = MmapOptions::new().len(byte_size as usize).map_anon()?;
        Ok(MmapBitVec {
            mmap: MmapKind::MmapMut(mmap),
            size,
            header: vec![].into_boxed_slice(),
            is_map_anonymous: true,
        })
    }

    /// Save in-memory mmap bitvector to disk.
    /// This is a no-op if the mmap is already file-backed.
    pub fn save_to_disk<P: AsRef<Path>>(
        &self,
        filename: P,
        magic: Option<[u8; 2]>,
        header: &[u8],
    ) -> Result<(), io::Error> {
        if !self.is_map_anonymous {
            return Ok(());
        }
        let (mut file, _) = create_bitvec_file(filename.as_ref(), self.size, magic, header)?;
        // We should already be at the right byte to write the content
        file.write_all(self.mmap.as_slice())?;
        Ok(())
    }

    /// Returns the header
    pub fn header(&self) -> &[u8] {
        &self.header
    }

    /// Read/copy an unaligned chunk of the `MmapBitVec`
    ///
    /// # Panics
    ///
    /// Explicitly panics if the end location, `r.end`, is outside the bounds
    /// of the bit vector. A panic may also occur if `r.start` is greater than
    /// `r.end`.
    pub fn get_range_bytes(&self, r: Range<usize>) -> Vec<u8> {
        if r.end > self.size {
            panic!("Range ends outside of BitVec")
        }
        let byte_idx_st = r.start >> 3;
        let byte_idx_en = (r.end - 1) >> 3;
        let new_size: usize = (((r.end - r.start) - 1) >> 3) + 1;

        let ptr: *const u8 = self.mmap.as_ptr();
        let mut v = vec![0; new_size];

        // `shift` is the same as the position of the last bit
        let shift = (r.end & 7) as u8;
        for (new_idx, old_idx) in (byte_idx_st..=byte_idx_en).enumerate() {
            let old_val = unsafe { *ptr.add(old_idx) };
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

    /// Set an unaligned range of bits in the bit vector from a byte slice.
    ///
    /// Note this operation ORs the passed byteslice and the existing bitmask.
    ///
    /// # Panics
    ///
    /// Explicitly panics if the end location, `r.end`, is outside the bounds
    /// of the bit vector or if the byte slice passed in is a different size
    /// from the range specified. A panic may also occur if `r.start` is greater
    /// than `r.end`.
    pub fn set_range_bytes(&mut self, r: Range<usize>, x: &[u8]) {
        if r.end > self.size {
            panic!("Range ends outside of BitVec")
        }
        let new_size: usize = r.end - r.start;
        if ((new_size - 1) >> 3) + 1 != x.len() {
            panic!("Range and array passed are different sizes")
        }
        // Ignoring r.start except for checking that it roughly
        // matches up with the size of the byte slice. This works because
        // we're ORing the bits together, so any extra zeros at the front
        // of the first byte in x shouldn't affect the final result
        let max_len = 8 * x.len();
        let byte_idx_st = if r.end - 1 > max_len {
            ((r.end - 1 - max_len) >> 3) + 1
        } else {
            0
        };
        let byte_idx_en = (r.end - 1) >> 3;

        let mmap: *mut u8 = self
            .mmap
            .as_mut_ptr()
            .expect("set_range_bytes can only be called on a mutable mmap");

        let shift = 8 - (r.end & 7) as u8;
        let mask = 0xFFu8.checked_shr(u32::from(8 - shift)).unwrap_or(0xFF);
        for (val, idx) in x.iter().zip(byte_idx_st..=byte_idx_en) {
            let shifted_val = val.checked_shr(u32::from(8 - shift)).unwrap_or(0);
            if idx > 0 && shift != 8 {
                unsafe {
                    *mmap.offset(idx as isize - 1) |= shifted_val;
                }
            }
            let shifted_val = (val & mask).checked_shl(u32::from(shift)).unwrap_or(*val);
            unsafe {
                *mmap.add(idx) |= shifted_val;
            }
        }
    }
}

impl BitVector for MmapBitVec {
    /// Check a single value in the `MmapBitVec`, returning its true/false status
    ///
    /// # Panics
    ///
    /// Panics if the location, `i`, is outside the bounds of the bit vector
    fn get(&self, i: usize) -> bool {
        if i > self.size {
            panic!("Invalid bit vector index");
        }
        let byte_idx = (i >> 3) as isize;
        let bit_idx = 7 - (i & 7) as u8;

        let mmap: *const u8 = self.mmap.as_ptr();
        unsafe { (*mmap.offset(byte_idx) & (1 << bit_idx)) != 0 }
    }

    /// Set a single bit in the bit vector
    ///
    /// # Panics
    ///
    /// Panics if the location, `i`, is outside the bounds of the bit vector
    fn set(&mut self, i: usize, x: bool) {
        if i > self.size {
            panic!("Invalid bit vector index");
        }
        let byte_idx = (i >> 3) as isize;
        let bit_idx = 7 - (i & 7) as u8;

        let mmap: *mut u8 = self
            .mmap
            .as_mut_ptr()
            .expect("set can only be called on a mutable mmap");
        unsafe {
            if x {
                *mmap.offset(byte_idx) |= 1 << bit_idx
            } else {
                *mmap.offset(byte_idx) &= !(1 << bit_idx)
            }
        }
    }

    /// Returns the length (in bits) of the bit vector
    fn size(&self) -> usize {
        self.size
    }

    /// Return the number of set bits in the range `r`
    fn rank(&self, r: Range<usize>) -> usize {
        let byte_idx_st = r.start >> 3;
        let byte_idx_en = (r.end - 1) >> 3;
        let mmap: *const u8 = self.mmap.as_ptr();

        let mut bit_count = 0usize;

        let mut size_front = 8u8 - (r.start & 7) as u8;
        if size_front == 8 {
            size_front = 0;
        }
        if let Some(mask) = 0xFFu8.checked_shl(u32::from(size_front)) {
            let byte = unsafe { *mmap.add(byte_idx_st) & mask };
            bit_count += byte.count_ones() as usize
        }

        // if the front is all there is, we can bail now
        if byte_idx_st == byte_idx_en {
            return bit_count;
        }

        // get the last byte (also a "partial" byte like the first)
        let mut size_back = (r.end & 7) as u8;
        if size_back == 8 {
            size_back = 0;
        }
        if let Some(mask) = 0xFFu8.checked_shr(u32::from(size_back)) {
            let byte = unsafe { *mmap.add(byte_idx_en) & mask };
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

    /// Return the position of the `nth` set bit with `start` treated as the 0th position, or `None` if there is no set bit
    fn select(&self, n: usize, start: usize) -> Option<usize> {
        let byte_idx_st = start >> 3;
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

    /// Read an unaligned chunk of the `MmapBitVec` into a `u128`
    ///
    /// # Panics
    ///
    /// Explicitly panics if the end location, `r.end`, is outside the bounds
    /// of the bit vector or if the range specified is greater than 128 bits.
    /// (Use `get_range_bytes` instead if you need to read larger chunks) A panic
    /// will also occur when `r.start` is greater than `r.end`.
    fn get_range(&self, r: Range<usize>) -> u128 {
        if r.end - r.start > 128usize {
            panic!("Range too large (>128)")
        } else if r.end > self.size {
            panic!("Range ends outside of BitVec")
        }
        let byte_idx_st = r.start >> 3;
        let byte_idx_en = (r.end - 1) >> 3;
        let new_size: u8 = (r.end - r.start) as u8;

        let mut v;
        let ptr: *const u8 = self.mmap.as_ptr();

        // read the last byte first
        unsafe {
            v = u128::from(*ptr.add(byte_idx_en));
        }
        // align the end of the data with the end of the u128
        v >>= 7 - ((r.end - 1) & 7);

        if r.start < self.size - 128usize {
            unsafe {
                // we have to transmute since we don't know if it's a u64 or u128
                #[allow(clippy::transmute_ptr_to_ptr)]
                let lg_ptr: *const u128 = transmute(ptr.add(byte_idx_st));
                v |= lg_ptr.read_unaligned().to_be() << (r.start & 7) >> (128 - new_size);
            }
        } else {
            // special case if we can't get a whole u64 out without running outside the buffer
            let bit_offset = new_size + (r.start & 7) as u8;
            for (new_idx, old_idx) in (byte_idx_st..byte_idx_en).enumerate() {
                unsafe {
                    v |= u128::from(*ptr.add(old_idx)) << (bit_offset - 8u8 * (new_idx as u8 + 1));
                }
            }
        }

        // mask out the high bits in case we copied extra
        v & (u128::MAX >> (128 - new_size))
    }

    /// Set an unaligned range of bits using a `u64`.
    ///
    /// Note this operation ORs the passed u64 and the existing bitmask
    ///
    /// # Panics
    ///
    /// Explicitly panics if the end location, `r.end`, is outside the bounds
    /// of the bit vector. A panic will also occur when `r.start` is greater than
    /// `r.end`.
    fn set_range(&mut self, r: Range<usize>, x: u128) {
        if r.end > self.size {
            panic!("Range ends outside of BitVec")
        }
        let byte_idx_st = r.start >> 3;
        let byte_idx_en = (r.end - 1) >> 3;
        let new_size: u8 = (r.end - r.start) as u8;

        // split off the front byte
        let size_front = 8u8 - (r.start & 7) as u8;
        let front_byte = if size_front >= new_size {
            (x << (size_front - new_size)) as u8
        } else {
            (x >> (new_size - size_front)) as u8
        };

        // set front with an AND mask to make sure all the 0s in the
        // new value get masked over the existing 1s
        let mmap: *mut u8 = self
            .mmap
            .as_mut_ptr()
            .expect("set_range can only be called on a mutable mmap");
        unsafe {
            *mmap.add(byte_idx_st) |= front_byte;
        }

        // if the front is all there is, we can bail now
        if byte_idx_st == byte_idx_en {
            return;
        }

        // set the last byte (also a "partial" byte like the first)
        let mut size_back = (r.end & 7) as u8;
        if size_back == 0 {
            size_back = 8;
        }
        let back_byte = (x << (128 - size_back) >> 120) as u8;
        unsafe {
            *mmap.add(byte_idx_en) |= back_byte;
        }

        // only two bytes long, bail out
        if byte_idx_st + 1 == byte_idx_en {
            return;
        }

        let size_main = new_size - size_front;
        // shift off the first byte (and we don't care about the last byte,
        // because we won't iterate through it) and then make sure that the
        // u64 is stored in the "right" order in memory
        let main_chunk = (x << (128 - size_main)).to_be();

        let bytes: [u8; 16] = main_chunk.to_le_bytes();
        for (byte_idx, byte) in ((byte_idx_st + 1)..byte_idx_en).zip(bytes.iter()) {
            unsafe {
                *mmap.add(byte_idx) |= *byte;
            }
        }
    }

    fn clear_range(&mut self, r: Range<usize>) {
        if (r.end - 1) > self.size {
            panic!("Range ends outside of BitVec")
        }
        let byte_idx_st = r.start >> 3;
        let byte_idx_en = (r.end - 1) >> 3;

        let mmap: *mut u8 = self
            .mmap
            .as_mut_ptr()
            .expect("clear range can only be called on a mutable mmap");

        // set front with an AND mask to make sure all the 0s in the
        // new value get masked over the existing 1s
        let size_front = 8u8 - (r.start & 7) as u8;
        if let Some(mask) = 0xFFu8.checked_shl(u32::from(size_front)) {
            unsafe {
                *mmap.add(byte_idx_st) &= mask;
            }
        }

        // if the front is all there is, we can bail now
        if byte_idx_st == byte_idx_en {
            return;
        }

        // set the last byte (also a "partial" byte like the first)
        let mut size_back = (r.end & 7) as u8;
        if size_back == 0 {
            size_back = 8;
        }
        if let Some(mask) = 0xFFu8.checked_shr(u32::from(size_back)) {
            unsafe {
                *mmap.add(byte_idx_en) &= mask;
            }
        }

        // only two bytes long, bail out
        if byte_idx_st + 1 == byte_idx_en {
            return;
        }

        // zero out all the middle bytes
        for byte_idx in (byte_idx_st + 1)..byte_idx_en {
            unsafe {
                *mmap.add(byte_idx) = 0u8;
            }
        }
    }
}

/// Drop is implemented for `BitVec` to explicitly flush any changes to the
/// file before the memory map is closed.
impl Drop for MmapBitVec {
    fn drop(&mut self) {
        let _ = self.mmap.flush();
    }
}

#[cfg(test)]
mod test {
    use std::path::Path;

    use super::MmapBitVec;
    use crate::bitvec::BitVector;

    #[test]
    fn test_bitvec() {
        use std::fs::remove_file;

        let header = vec![];
        let mut b = MmapBitVec::create("./test", 100, None, &header).unwrap();
        b.set(2, true);
        assert!(!b.get(1));
        assert!(b.get(2));
        assert!(!b.get(100));
        drop(b);
        assert!(Path::new("./test").exists());

        let b = MmapBitVec::open("./test", None, true).unwrap();
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
        let _ = MmapBitVec::create("./test_headerless", 80, None, &header).unwrap();
        assert!(Path::new("./test_headerless").exists());
        let b = MmapBitVec::open_no_header("./test_headerless", 12).unwrap();
        assert_eq!(b.size(), 64);
        remove_file("./test_headerless").unwrap();
    }

    #[test]
    fn test_bitvec_get_range() {
        let mut b = MmapBitVec::from_memory(1024).unwrap();
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
        b.set_range_bytes(0..4, &[0x05u8]);
        assert_eq!(b.get_range(0..4), 0b0101);
        b.set_range_bytes(5..8, &[0x05u8]);
        assert_eq!(b.get_range(5..8), 0b0101);

        // clear the first part
        b.clear_range(0..16);

        // test across a byte boundary
        b.set_range_bytes(6..10, &[0x0Du8]);
        assert_eq!(b.get_range(6..10), 0x0D);

        // test setting multiple bytes
        b.set_range_bytes(0..16, &[0xFFu8, 0xFFu8]);
        assert_eq!(b.get_range(0..16), 0xFFFF);

        // test setting multiple bytes across boundaries
        b.set_range_bytes(20..36, &[0xFFu8, 0xFFu8]);
        assert_eq!(b.get_range(20..36), 0xFFFF);

        // testing ORing works
        b.set_range_bytes(64..80, &[0xA0u8, 0x0Au8]);
        assert_eq!(b.get_range(64..80), 0xA00A);
        b.set_range_bytes(64..80, &[0x0Bu8, 0xB0u8]);
        assert_eq!(b.get_range(64..80), 0xABBA);
    }

    #[test]
    fn test_rank_select() {
        let mut b = MmapBitVec::from_memory(128).unwrap();
        b.set(7, true);
        b.set(56, true);
        b.set(127, true);

        assert_eq!(b.rank(0..8), 1);
        assert_eq!(b.rank(0..128), 3);

        assert_eq!(b.select(1, 0), Some(7));
        assert_eq!(b.select(3, 0), Some(127));
    }

    #[test]
    fn can_write_anon_mmap_to_disk() {
        let mut b = MmapBitVec::from_memory(128).unwrap();
        b.set(0, true);
        b.set(7, true);
        b.set(56, true);
        b.set(127, true);
        let dir = tempfile::tempdir().unwrap();
        b.save_to_disk(dir.path().join("test"), None, &[]).unwrap();
        let f = MmapBitVec::open(dir.path().join("test"), None, false).unwrap();
        assert_eq!(f.get(0), true);
        assert_eq!(f.get(7), true);
        assert_eq!(f.get(56), true);
        assert_eq!(f.get(127), true);
        assert_eq!(f.get(10), false);
    }
}
