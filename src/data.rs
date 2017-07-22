// File storage
/*
store data aligned correctly

*/
use memmap::{self, MmapMut, Protection};
use std::{mem};
use std::fs::{File, OpenOptions};
use std::sync::Arc;
use std::fmt::Debug;
use super::*;
use parking_lot::Mutex;

fn try_n<F, T, E>(n: usize, mut f: F) -> Result<T, E> where F: FnMut() -> Result<T, E>, E: Debug {
    let mut res = f();
    for _ in 1 .. n-1 {
        match res {
            Ok(v) => return Ok(v),
            Err(e) => println!("Err: {:?}", e)
        }
        res = f();
    }
    f()
}

pub struct BarnInner {
    size:   usize,
    mmaps:  Vec<MmapMut>, // both mmap and
    file:   File  // file need to stay alive!
}
pub struct Barn {
    arena:  *const Arena,
    inner:  Mutex<BarnInner>,
}
impl Barn {
    pub fn load_file(file: File, create: bool) -> Arc<Barn> {
        assert!(size!(Arena) <= SUPER_BLOCK_SIZE);
    
        let default_size = 128 * SUPER_BLOCK_SIZE;
        let mut file_size = file.metadata().expect("can't read metadata").len() as usize;
        let mut needs_init = false;
        if file_size == 0 {
            assert_eq!(create, true);
            println!("initializing");
            file.set_len(default_size as u64).expect("failed to resize file");
            file_size = default_size;
            needs_init = true;
        }
        let (mmap, arena) = {
            let mut base = 0;
            let mut mmap = try_n(10, || {
                let mut cfg = unsafe { memmap::file(&file) };
                cfg.len(file_size);
                cfg.protection(Protection::ReadWrite);
                cfg.addr(base as *mut u8);
                let mmap = cfg.map_mut().expect("failed to mmap");
                let p = mmap.as_ptr() as usize;
                log!("requested: {:16x}, got: {:16x}", base, p);
                if p % SUPER_BLOCK_SIZE == 0 {
                    Ok(mmap)
                } else {
                    base = round_up(p, SUPER_BLOCK_SIZE);
                    Err(())
                }
            }).expect("failed to open mmap");
            println!("mmap at {:p}", mmap.as_ptr());

            unsafe {
                if needs_init {
                    let arena = &mut *(mmap.as_mut_ptr() as *mut Arena);
                    arena.init(file_size);
                }

                let ptr = mmap.as_ptr();
                assert_eq!((ptr as usize) % SUPER_BLOCK_SIZE, 0);
                let arena = ptr as *const Arena;
                (mem::transmute(mmap), arena)
            }
        };
                
        Arc::new(Barn {
            arena:  arena,
            inner:  Mutex::new(BarnInner{
                file:   file,
                size:   file_size,
                mmaps:  vec![mmap]
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
        
        Barn::load_file(f, create)
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
impl BarnInner {
    pub fn grow(&mut self) -> (usize, usize) {
        let base = self.mmaps.last().unwrap().as_ptr();
        let additional = round_up(self.size / 4, SUPER_BLOCK_SIZE);
        let old_size = self.size;
        let new_size = self.size + additional;
        let mut cfg = unsafe { memmap::file(&self.file) };
        cfg.offset(self.size);
        cfg.len(additional);
        cfg.protection(Protection::ReadWrite);
        cfg.addr(unsafe { base.offset(additional as isize) as *mut u8 });
        let mmap = cfg.map_mut().expect("failed to grow");
        println!("growing mmap at {:p}", mmap.as_ptr());
        self.mmaps.push(mmap);
        self.size = new_size;
        
        
        (old_size, additional)
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
        let heap = Heap::new(&b);
        
        let data = &heap <- [1, 2, 3, 4u8];
        println!("data: {:?}", data);
        
        root.swap(data.into_rc());
        
        match root.get() {
            Some(d) => println!("read 2: {:?}", d),
            None => println!("read 2: nothing")
        }
    };
}
