// File storage
/*
store data aligned correctly

*/
use memmap::{Mmap, Protection};
use std::{mem, ptr, slice};
use std::fs::{File, OpenOptions};
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

#[repr(packed)]
struct FileHeader<T> {
    magic:      [u8; 4], // b"barn"
    version:    u32,
    root:       Cell<T>,
    arena:      Arena
}

pub struct Barn<T> {
    mmap:   Mmap,
    header: *const FileHeader<T>,
    file:   File
}
impl<T> Barn<T> {
    pub fn load_file(mut file: File, create: bool) -> Barn<T> {
        let default_size = 1024 * 1024;
        let mut file_size = file.metadata().expect("can't read metadata").len() as usize;
        let mut needs_init = false;
        if file_size == 0 {
            assert_eq!(create, true);
            println!("initializing");
            file.set_len(default_size as u64);
            file_size = default_size;
            needs_init = true;
        }
        let mut mmap = Mmap::open_with_offset(&file, Protection::ReadWrite, 0, file_size)
        .expect("mmap failed");
        println!("mmap at {:p}", mmap.ptr());
        
        if needs_init {
            let arena_size = file_size - mem::size_of::<FileHeader<()>>();
            let header = unsafe { &mut *(mmap.mut_ptr() as *mut FileHeader<T>) };
            header.magic = *b"barn";
            header.version = 0;
            header.root = Cell::empty();
            header.arena = Arena::with_size(arena_size as u32);
            mmap.flush().unwrap();
        }
        let header = unsafe { &*(mmap.ptr() as *const FileHeader<T>) };
        
        assert_eq!(header.magic, *b"barn");
        assert_eq!(header.version, 0);
        
        Barn {
            mmap: mmap,
            header: header,
            file: file
        }
    }
    
    pub fn load_path(path: &str, create: bool) -> Barn<T> {
        let f = OpenOptions::new()
        .read(true)
        .write(true)
        .create(create)
        .open(path)
        .expect("faild to open file");
        
        Barn::load_file(f, create)
    }
    
    fn header(&self) -> &FileHeader<T> {
        unsafe { &*self.header }
    }
    pub fn root(&self) -> RcCell<T> {
        let header = self.header();
        assert_eq!(header.magic, *b"barn");
        assert_eq!(header.version, 0);
        unsafe {
            header.root.wrap(&header.arena)
        }
    }
    pub fn arena(&self) -> &Arena {
        let header = self.header();
        assert_eq!(header.magic, *b"barn");
        assert_eq!(header.version, 0);
        &header.arena
    }
}

#[test]
fn test_read() {
    let b: Barn<[u8; 4]> = Barn::load_path("foo.barn", true);
    {
        let arena = b.arena();
        let root = b.root();
        match root.get() {
            Some(d) => println!("read 1: {:?}", d),
            None => println!("read 1: nothing")
        }
        
        let data = arena <- [1, 2, 3, 4u8];
        println!("data: {:?}", data);
        
        root.swap(data.into_rc());
        
        match root.get() {
            Some(d) => println!("read 2: {:?}", d),
            None => println!("read 2: nothing")
        }
    };
}
