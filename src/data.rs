// File storage
/*
store data aligned correctly

*/
use memmap::{Mmap, Protection};
use std::{mem, ptr, slice};
use std::fs::File;
use std::io::Write;
use arena::{Arena, Cell, RcCell};

pub struct Reader<'a> {
    data:       &'a [u8]
}
impl<'a> Reader<'a> {
    pub fn read(&mut self, len: usize) -> &[u8] {
        let (buf, remaining) = self.data.split_at(len);
        self.data = remaining;
        buf
    }
    pub fn decode<T: Copy>(&mut self) -> T {
        let size = mem::size_of::<T>();
        let buf = self.read(size);
        let mut val: T;
        unsafe {
            val = mem::uninitialized();
            ptr::copy_nonoverlapping(buf.as_ptr(), &mut val as *mut T as *mut u8, size);
        }
        val
    }
}
pub struct Writer<'a> {
    data:   &'a mut [u8]
}
impl<'a> Writer<'a> {
    pub fn write(&mut self, n: usize) -> &'a mut [u8] {
        let ptr = self.data.as_mut_ptr();
        let len = self.data.len();
        assert!(n <= len);
        // both sides are still valid for 'a
        unsafe {
            // [n .. len]
            self.data = slice::from_raw_parts_mut(ptr.offset(n as isize), len - n);
            
            // [0.. n]
            slice::from_raw_parts_mut(ptr, n)
        }
    }
    pub fn encode<T: Copy>(&mut self, val: &T) {
        let size = mem::size_of::<T>();
        
        let buf = self.write(size);
        unsafe {
            ptr::copy_nonoverlapping(val as *const T as *const u8, buf.as_mut_ptr(), size);
        }
    }
}
pub enum Offset {
    Close(u8),  // 8 bit
    Near(u16),   // 16 bit
    Mid(u32),    // 32 bit
    Far(u64)     // 64 bit
}    

struct FileHeader<T> {
    magic:      [u8; 4], // b"barn"
    version:    u32,
    root:       Cell<T>,
    arena:      Arena
}

pub struct Barn {
    mmap:   Mmap,
}
impl Barn {
    pub fn load(file: &str) -> Barn {
        Barn {
            mmap: Mmap::open_path(file, Protection::ReadWrite).expect("mmap failed")
        }
    }
    pub fn create(file: &str, size: u64) -> Barn {
        {
            let mut f = File::create(file).unwrap();
            
            let arena_size = size as u32 - mem::size_of::<FileHeader<()>>() as u32;
            let default = FileHeader::<()> {
                magic:      *b"barn",                               //  4 bytes
                version:    0,                                      //  4 bytes
                root:       Cell::empty(),                          //  4 bytes
                arena:      Arena::with_size(arena_size)     // 16 bytes
            };
            let data: [u8; 28] = unsafe {
                mem::transmute(default)
            };
            f.write(&data);
            f.set_len(size);
        }
        Barn::load(file)
    }
    pub fn root<T>(&self) -> RcCell<T> {
        let header = unsafe { &*(self.mmap.ptr() as *const FileHeader<T>) };
        assert_eq!(header.magic, *b"barn");
        assert_eq!(header.version, 0);
        unsafe { header.root.wrap(&header.arena) }
    }
}

#[test]
fn test_read() {
    let b = Barn::create("foo.barn", 1024*1024);
    {
        let root = b.root::<Vec<u8>>();
        match root.get() {
            Some(d) => println!("{:?}", d),
            None => println!("nothing")
        }
    }
}
