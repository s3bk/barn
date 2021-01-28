// File storage
/*
store data aligned correctly

*/
use memmap2::{self, MmapMut, MmapOptions};
use std::{mem};
use std::fs::{File, OpenOptions};
use std::sync::Arc;
use std::fmt::Debug;
use super::*;
use parking_lot::Mutex;

pub struct BarnInner {
    size:   usize,
    mmap:  MmapMut, // both mmap and
    file:   File  // file need to stay alive!
}
pub struct Barn {
    arena:  *const Arena,
    inner:  Mutex<BarnInner>,
}
impl Barn {
    pub fn load_file(file: File, create: bool, min_size: usize) -> Arc<Barn> {
        assert!(size!(Arena) <= SUPER_BLOCK_SIZE);
    
        let mut needs_init = false;
        let mut file_size = file.metadata().expect("can't read metadata").len() as usize;
        if file_size == 0 {
            assert_eq!(create, true);
            println!("initializing");
            file.set_len(min_size as u64).expect("failed to resize file");
            file_size = min_size;
            needs_init = true;
        } else if file_size < min_size {
            panic!("file too small");
        }
        let mut cfg = MmapOptions::new();
        cfg.len(file_size);
        let mut mmap = unsafe {
            cfg.map_mut(&file).expect("failed to mmap")
        };
        println!("mmap at {:p}", mmap.as_ptr());

        let arena = unsafe {
            if needs_init {
                let arena = &mut *(mmap.as_mut_ptr() as *mut Arena);
                arena.init(file_size);
            }

            let ptr = mmap.as_ptr();
            let arena = ptr as *const Arena;

            (*arena).check_header();
            arena
        };
        
        Arc::new(Barn {
            arena:  arena,
            inner:  Mutex::new(BarnInner{
                file:   file,
                size:   file_size,
                mmap
            })
        })
    }
    
    pub fn load_path(path: &str, create: bool) -> Arc<Barn> {
        let f = OpenOptions::new()
        .read(true)
        .write(true)
        .create(create)
        .open(path)
        .expect("faild to open file");
        
        Barn::load_file(f, create, 128 * SUPER_BLOCK_SIZE)
    }
    
    pub fn inner(&self) -> &Mutex<BarnInner> {
        &self.inner
    }
    
    pub fn arena(&self) -> &Arena {
        unsafe { &*self.arena }
    }
    
    pub fn root<T>(&self) -> RcCell<T> {
        self.arena().root()
    }
}

#[test]
fn test_read() {
    let b = Barn::load_path("foo.barn", true);
    {
        let root = b.root();
        match root.get() {
            Some(d) => println!("read 1: {:?}", d),
            None => println!("read 1: nothing")
        }
        let heap = Heap::new(b.clone());
        
        use crate::stash::Vec;
        let mut v = Vec::with_capacity(&heap, 4);
        v.extend_from_slice(&[1, 2, 3, 4u8]);
        let data = Box::new(&heap, v).unwrap();
        println!("data: {:?}", data);
        
        root.swap(data.into_rc());
        
        match root.get() {
            Some(d) => println!("read 2: {:?}", d),
            None => println!("read 2: nothing")
        }
    };
}
