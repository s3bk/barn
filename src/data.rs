// File storage
/*
store data aligned correctly

*/
use memmap::{Mmap, Protection};
use std::{mem};
use std::fs::{File, OpenOptions};
use super::{Arena, Cell, RcCell};

#[repr(C, packed)] // need repr(C), as we rely on Arena being the last field
struct FileHeader<T> {
    magic:      [u8; 4], // b"barn"
    version:    u32,
    root:       Cell<T>,
    arena:      Arena
}

pub struct Barn<T> {
    header: *const FileHeader<T>,
    _mmap:   Mmap, // both mmap and
    _file:   File  // file need to stay alive!
}
impl<T> Barn<T> {
    pub fn load_file(file: File, create: bool) -> Barn<T> {
        let default_size = 1024 * 1024;
        let mut file_size = file.metadata().expect("can't read metadata").len() as usize;
        let mut needs_init = false;
        if file_size == 0 {
            assert_eq!(create, true);
            println!("initializing");
            file.set_len(default_size as u64).expect("failed to resize file");
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
            header: header,
            _mmap: mmap,
            _file: file
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
