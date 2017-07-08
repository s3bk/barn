use std::fmt;
use alloc::allocator::{Alloc, Layout, AllocErr};
use std::sync::atomic::AtomicU32;
use std::sync::atomic::Ordering::*;
use std::mem;
use std::marker::PhantomData;
use std::mem::{size_of, align_of};
use std::ops::{Place, Placer, InPlace, Deref, DerefMut};
use std::u32;
use core::nonzero::NonZero;

// may only be created in the file
pub struct Arena {
    size:           u32,       // total size in bytes
   // granularity:    usize    // minimum size of allocations,
    high:           AtomicU32, // everything >= high is free
    low:            AtomicU32, // everything < low is used
    live:           AtomicU32
}
impl Arena {
    #[inline]
    pub fn with_size(size: u32) -> Arena {
        Arena {
            size:   size,
            high:   AtomicU32::new(size_of::<Arena>() as u32),
            low:    AtomicU32::new(size_of::<Arena>() as u32),
            live:   AtomicU32::new(0)
        }
    }
    #[inline(always)]
    pub fn byte_offset(&self, bytes: u32) -> usize {
        self as *const Arena as usize + bytes as usize
    }
    #[inline(always)]
    pub fn pos_for_ptr<T>(&self, ptr: *const T) -> u32 {
        (ptr as usize - self as *const Arena as usize) as u32
    }
    #[inline(always)]
    pub fn ptr_for_pos<T>(&self, pos: u32) -> *const T {
        self.byte_offset(pos) as *const T
    }
    pub fn allocate(&self, size: u32, align: u32) -> u32 {
        self.live.fetch_add(1, Relaxed);
        loop {
            let old_pos = self.high.load(Relaxed);
            let start = old_pos + align - (old_pos - 1) % align - 1;
            let new_pos = start + size;
            if self.high.compare_and_swap(old_pos, new_pos, Relaxed) == old_pos {
                return start;
            }
        }
    }
    #[inline]
    pub unsafe fn deallocate(&self, pos: u32, _size: u32, _align: u32) {
        self.live.fetch_sub(1, Relaxed);
    }
    
    #[inline(always)]
    pub fn allocate_one<T>(&self) -> *mut T {
        let pos = self.allocate(mem::size_of::<T>() as u32, mem::align_of::<T>() as u32);
        self.ptr_for_pos::<T>(pos) as *mut T
    }
    #[inline(always)]
    pub unsafe fn deallocate_one<T>(&self, ptr: *mut T) {
        let pos = self.pos_for_ptr(ptr as *const T);
        self.deallocate(pos, mem::size_of::<T>() as u32, mem::align_of::<T>() as u32);
    }
}

unsafe impl<'a> Alloc for &'a Arena {
    unsafe fn alloc(&mut self, layout: Layout) -> Result<*mut u8, AllocErr> {
        let size = layout.size();
        let align = layout.align();
        assert!(size < u32::MAX as usize);
        assert!(align < u32::MAX as usize);
        match self.allocate(size as u32, align as u32) {
            0 => Err(AllocErr::Exhausted { request: layout }),
            p => Ok(self.byte_offset(p) as *mut u8)
        }
    }
    unsafe fn dealloc(&mut self, ptr: *mut u8, layout: Layout) {
        let pos = ptr as isize - *self as *const Arena as isize;
        assert!(pos > 0 && pos < self.size as isize);
        self.deallocate(pos as u32, layout.size() as u32, layout.align() as u32)
    }
}

pub struct Hole<'a, T: 'a> {
    inner:  *mut Data<T>,
    arena:  &'a Arena
}
impl<'a, T: 'a> Placer<T> for &'a Arena {
    type Place = Hole<'a, T>;
    #[inline(always)]
    fn make_place(self) -> Self::Place {
        Hole { inner: self.allocate_one(), arena: self }
    }
}
impl<'a, T> Place<T> for Hole<'a, T> {
    #[inline(always)]
    fn pointer(&mut self) -> *mut T {
        unsafe { &mut (*self.inner).data }
    }
}
impl<'a, T> InPlace<T> for Hole<'a, T> {
    type Owner = Box<'a, T>;
    #[inline(always)]
    unsafe fn finalize(self) -> Box<'a, T> {
        Box { inner: self.inner, arena: self.arena }
    }
}

struct Unique<T> {
    pos:    NonZero<u32>,
    _m:     PhantomData<T>
}
impl<T> Unique<T> {
    #[inline(always)]
    pub fn pos(&self) -> u32 { self.pos.get() }
    
    #[inline(always)]
    unsafe fn from_pos(pos: u32) -> Unique<T> {
        Unique { pos: NonZero::new(pos), _m: PhantomData }
    }
    
    #[inline(always)]
    pub fn ptr(self, arena: &Arena) -> *mut T {
        arena.ptr_for_pos::<T>(self.pos.get()) as *mut T
    }
}

/*
refcount = 1 -> one active user
refcount = 0 locked by one user, refcount can't be increased by others
*/
#[derive(Copy, Clone)]
struct Shared<T> {
    pos:    NonZero<u32>,
    _m:     PhantomData<T>
}
impl<T> Shared<T> {
    #[inline(always)]
    unsafe fn from_pos(pos: u32) -> Shared<T> {
        Shared { pos: NonZero::new(pos), _m: PhantomData }
    }
    #[inline(always)]
    fn pos(self) -> u32 {
        self.pos.get()
    }
    #[inline(always)]
    pub fn ptr(self, arena: &Arena) -> *const T {
        arena.ptr_for_pos(self.pos.get()) as *const T
    }
}

pub struct Data<T> {
    rc:     AtomicU32,
    data:   T
}

pub struct Box<'a, T: 'a> {
    inner:  *mut Data<T>,
    arena:  &'a Arena
}
impl<'a, T: 'a> Box<'a, T> {
    fn inner(&self) -> &Data<T> {
        unsafe { &(*self.inner) }
    }
    pub fn into_rc(self) -> Rc<'a, T> {
        // set refcount to one
        self.inner().rc.store(1, Release);
        Rc {
            inner: self.inner,
            arena: self.arena
        }
    }
}
impl<'a, T: 'a> Drop for Box<'a, T> {
    #[inline(always)]
    fn drop(&mut self) {
        unsafe { self.arena.deallocate_one(self.inner as *mut Data<T>) }
    }
}
impl<'a, T> Deref for Box<'a, T> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &T {
        &self.inner().data
    }
}
impl<'a, T> DerefMut for Box<'a, T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut (*self.inner).data }
    }
}
impl<'a, T, U> PartialEq<U> for Box<'a, T> where T: PartialEq<U> {
    fn eq(&self, rhs: &U) -> bool {
        (self as &T).eq(rhs)
    }
}
impl<'a, T: fmt::Debug> fmt::Debug for Box<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (self as &T).fmt(f)
    }
}

#[derive(Clone)]
pub struct Rc<'a, T> {
    inner: *const Data<T>,
    arena: &'a Arena
}
impl<'a, T> Rc<'a, T> {
    fn from_shared(arena: &Arena, pos: Shared<Data<T>>) -> Rc<T> {
        Rc {
            inner: pos.ptr(arena),
            arena: arena
        }
    }
    fn inner(&self) -> &Data<T> {
        unsafe { &*self.inner }
    }
    pub fn lock(self) -> Result<Box<'a, T>, Rc<'a, T>> {
        match self.inner().rc.compare_exchange(1, 0, Acquire, Relaxed) {
            Ok(0) => Ok(Box {
                inner: self.inner as *mut Data<T>,
                arena: self.arena
            }),
            Err(_) => Err(self),
            _ => unreachable!()
        }
    }
    pub fn clone(&self) -> Rc<'a, T> {
        self.inner().rc.fetch_add(1, Relaxed);
        Rc {
            inner: self.inner,
            arena: self.arena
        }
    }
    fn to_shared(self) -> Shared<Data<T>> {
        unsafe {
            Shared::from_pos(self.arena.pos_for_ptr(self.inner))
        }
    }
}
impl<'a, T> Drop for Rc<'a, T> {
    fn drop(&mut self) {
        // if the refcount was one, we have to drop it
        if self.inner().rc.fetch_sub(1, Release) == 1 {
            unsafe {
                self.arena.deallocate_one(self.inner as *mut Data<T>);
            }
        }
    }
}
impl<'a, T> Deref for Rc<'a, T> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &T {
        &self.inner().data
    }
}
impl<'a, T: fmt::Debug> fmt::Debug for Rc<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.inner().data.fmt(f)
    }
}

pub struct Cell<T> {
    pos:    AtomicU32, // points to a shared Data<T>
    _m:     PhantomData<T>
}
impl<T> Cell<T> {
    // 0 -> empty
    // 1 -> being swapped
    
    pub fn empty() -> Self {
        Cell {
            pos: AtomicU32::new(0),
            _m:  PhantomData
        }
    }
    
    // temporarily steal the value
    // must be paired with put
    #[inline]
    fn take(&self) -> Option<Shared<Data<T>>> {
        loop {
            match self.pos.swap(1, Acquire) {
                0 => return None,
                1 => continue,
                p => return Some(unsafe { Shared::from_pos(p) })
            } 
        }
    }
    // must be paird with take
    #[inline]
    fn put(&self, p: Option<Shared<Data<T>>>) {
        let v = match p {
            None => 0,
            Some(s) => s.pos()
        };
        self.pos.store(v, Release);
    }
    
    #[inline]
    pub fn swap<F, O>(&self, f: F) -> O
    where F: FnOnce(Option<Shared<Data<T>>>) -> (Option<Shared<Data<T>>>, O)
    {
        let old = self.take();
        let (new, out) = f(old);
        self.put(new);
        out
    }
    
    pub unsafe fn wrap<'a>(&'a self, arena: &'a Arena) -> RcCell<'a, T> {
        RcCell {
            cell:  self,
            arena: arena
        }
    }
}

pub struct RcCell<'a, T: 'a> {
    cell:   &'a Cell<T>,
    arena:  &'a Arena
}
impl<'a, T: 'a> RcCell<'a, T> {
    pub fn get(&self) -> Option<Rc<'a, T>> {
        self.cell.swap(|c| match c {
            None => (None, None),
            Some(p) => {
                let rc = Rc::from_shared(self.arena, p);
                (Some(rc.clone().to_shared()), Some(rc))
            }
        })
    }
    
    pub fn swap(&self, rc: Rc<'a, T>) -> Option<Rc<'a, T>> {
        self.cell.swap(|c| (
            Some(rc.to_shared()),                       // value to be stored
            c.map(|p| Rc::from_shared(self.arena, p))   // value returned
        ))
    }
}
