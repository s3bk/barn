use std::{fmt, ptr, u32, cmp, mem};
use std::alloc::{Allocator, Layout, AllocError};
use std::sync::atomic::{AtomicU32, AtomicU64};
use std::sync::atomic::Ordering::*;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::hash::{Hash, Hasher};
use std::cmp::{PartialEq, Eq};
use std::cell::Cell;
use std::time::Duration;
use std::clone::Clone;
use std::ptr::NonNull;
use std::num::NonZeroU32;
use super::*;
use linux::*;
use std::sync::Arc;

pub type HeaderType = [u8; 4];
pub const HEADER_MAGIC: HeaderType = *b"barn";

pub trait OffsetScale {
    fn scale(n: u32) -> usize;
    fn unscale(n: usize) -> u32;
}
pub struct Unity{}
impl OffsetScale for Unity {
    #[inline(always)]
    fn scale(n: u32) -> usize { n as usize }
    #[inline(always)]
    fn unscale(n: usize) -> u32 { n as u32 }
}
pub struct SuperBlockScale {}
impl OffsetScale for SuperBlockScale {
    #[inline(always)]
    fn scale(n: u32) -> usize {
        (n as usize) * SUPER_BLOCK_SIZE
    }
    #[inline(always)]
    fn unscale(n: usize) -> u32 {
        (n / SUPER_BLOCK_SIZE) as u32
    }
}

#[repr(C)]
pub struct RelOffset<I, O, S: OffsetScale> {
    pos:    NonZeroU32,
    _i:     PhantomData<I>,
    _o:     PhantomData<O>,
    _s:     PhantomData<S>
}
impl<I, O, S: OffsetScale> RelOffset<I, O, S> {
    #[inline(always)]
    fn new(off: u32) -> Self {
        RelOffset {
            pos:    NonZeroU32::new(off).unwrap(),
            _i:     PhantomData,
            _o:     PhantomData,
            _s:     PhantomData
        }
    }
    #[inline(always)]
    unsafe fn get(self, base: &I) -> &O {
        &*((base as *const I as usize + self.offset()) as *const O)
    }
    #[inline(always)]
    fn get_shared(self, base: &I) -> NonNull<O> {
        unsafe { NonNull::new(self.get(base) as *const O as *mut O).unwrap() }
    }
    #[inline(always)]
    unsafe fn get_as_mut(self, base: &I) -> &mut O {
        &mut *((base as *const I as usize + self.offset()) as *mut O)
    }
    #[inline(always)]
    fn pos(self) -> u32 {
        self.pos.get()
    }
    #[inline(always)]
    fn offset(self) -> usize {
        S::scale(self.pos())
    }
    #[inline(always)]
    fn from_ptr(base: *const I, ptr: *const O) -> Self {
        RelOffset::new(S::unscale(ptr as usize - base as usize))
    }
}
impl<I, O, S: OffsetScale> cmp::PartialEq for RelOffset<I, O, S> {
    fn eq(&self, rhs: &Self) -> bool {
        self.pos() == rhs.pos()
    }
}
impl<I, O, S: OffsetScale> fmt::Debug for RelOffset<I, O, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "RelOffset({} -> {})", self.pos(), self.offset())
    }
}
impl<I, O, S: OffsetScale> Clone for RelOffset<I, O, S>  {
    fn clone(&self) -> Self {
        RelOffset { 
            pos:    self.pos,
            _i:     PhantomData,
            _o:     PhantomData,
            _s:     PhantomData,
        }
    }
}
impl<I, O, S: OffsetScale> Copy for RelOffset<I, O, S> {}

trait ListTarget {
    fn next(&self) -> &AtomicU32;
}
impl ListTarget for AtomicU32 {
    fn next(&self) -> &AtomicU32 { self }
}

struct List<B:?Sized, T:?Sized, S> {
    head:   AtomicU32,
    _b:     PhantomData<B>,
    _t:     PhantomData<T>,
    _s:     PhantomData<S>
}
impl<B, T, S> List<B, T, S> where T: ListTarget, S: OffsetScale {
    #[inline(always)]
    fn translate_pos(pos: u32) -> Option<RelOffset<B, T, S>> {
        match pos {
            0 => None,
            n => Some(RelOffset::new(n))
        }
    }
    /// add a node to the list
    /// this means we have ownership of this position
    #[inline(always)]
    fn push(&self, base: &B, pos: RelOffset<B, T, S>) {
        log!("push({:?})", pos);
        // get the old head
        let mut old_head = self.head.load(Relaxed);
        loop {
            //vlog!(old_head);
            // write the old head as the next offset of the node we are about to push
            let node: &T = unsafe { pos.get_as_mut(base) };
            node.next().store(old_head, Relaxed);
            //log!("node at {:p}, AtomicU32 at {:p} {:?}", node, node.next(), node.next());
            
            // now store the offset to the current node in the list head
            match self.head.compare_exchange(old_head, pos.pos(), Relaxed, Relaxed) {
                Ok(_) => break,
                Err(p) => old_head = p
            }
        }
    }
    
    
    fn pop(&self, base: &B) -> Option<RelOffset<B, T, S>> {
        let v = self._pop(base);
        vlog!(self.head);
        log!("pop() -> {:?}", v);
        v
    }
    
    #[inline(always)]
    fn _pop(&self, base: &B) -> Option<RelOffset<B, T, S>> {
        let mut old_head = self.head.load(Relaxed);
        vlog!(old_head);
        loop {
            // if old_head isn't NULL
            let head: RelOffset<B, T, S> = match old_head {
                0 => return None,
                n => RelOffset::new(n)
            };
            
            // the node the head points to
            let node = unsafe { head.get(base) };
            log!("node at {:p}, AtomicU32 at {:p} {:?}", node, node.next(), node.next());
            
            // fetch the next offset
            let next_off = node.next().load(Relaxed);
            vlog!(next_off);
            
            // and write it to the list head
            match self.head.compare_exchange(old_head, next_off, Relaxed, Relaxed) {
                Ok(_) => return Some(head), // success. return old head
                Err(p) => old_head = p
            }
        }
    }
    
    // assumes the the supplied head isn't shared.
    fn append(&self, base: &B, head: RelOffset<B, T, S>) {
        // the one we have to modify
        let mut tail = &self.head;
        while let Some(off) = Self::translate_pos(tail.load(Relaxed)) {
            // still another link
            tail = unsafe { off.get(base) }.next();
        }
        
        tail.store(head.pos(), Relaxed);
    }
    
    #[inline(always)]
    fn init(&mut self) {
        *self.head.get_mut() = 0;
    }
}


#[repr(C)]
struct SuperBlock {
    free:   List<SuperBlock, AtomicU32, Unity>,
    used:   AtomicU32,
    next:   AtomicU32,
    num:    u32,
    cap:    u32,
    class:  SizeClass,
}
impl ListTarget for SuperBlock {
    #[inline(always)]
    fn next(&self) -> &AtomicU32 { &self.next }
}
impl SuperBlock {
    #[inline(always)]
    pub fn init_num(&mut self, num: u32) {
        log!("init block #{} at {:p}", num, self);
        self.num = num;
        self.cap = 0;
    }

    pub unsafe fn init_class(&mut self, class: SizeClass) {
        let chunk_size = class.size();
        vlog!(chunk_size);
        assert!(chunk_size >= 4);
        let first_chunk = div_ceil(size!(SuperBlock), chunk_size) as u32;
        let last_chunk = (SUPER_BLOCK_SIZE / chunk_size) as u32;
        
        self.free.init();
        for i in (first_chunk .. last_chunk).rev() {
            self.free.push(self, RelOffset::new(i * chunk_size as u32));
        }
        
        *self.used.get_mut() = 0;
        self.cap = last_chunk - first_chunk;
        self.class = class;
    }
    
    pub fn arena(&self) -> &Arena {
        let ptr = (self as *const SuperBlock as usize - self.num as usize * SUPER_BLOCK_SIZE) as *const Arena;
        unsafe { &*ptr }
    }
    
    #[inline(always)]
    fn _free(&self, pos: u32) {
        assert_eq!(pos % self.class.size() as u32, 0);
        self.free.push(self, RelOffset::new(pos));
        let used = self.used.fetch_sub(1, Relaxed);
        self.arena().level_trigger(self, used, self.cap);
    }
    
    #[inline(always)]
    pub fn alloc(&self) -> Option<*mut u8> {
        log!("alloc(self: {:p})", self);
        self.free.pop(self).map(|p| {
            self.used.fetch_add(1, Relaxed);
            let off = RelOffset::from(p);
            assert_eq!(off.pos() as usize % self.class.size(), 0);
            vlog!(off.pos());
            unsafe { off.get_as_mut(self) as *const AtomicU32 as *mut u8 }
        })
    }
    
    pub fn report(&self) {
        if self.cap == 0 {
            println!("Block #{:3}  not used", self.num);
        } else {
            println!("Block #{:3}  {:?} ({}/{})", self.num, self.class, self.used.load(Relaxed), self.cap);
        }
    }
}

const USIZE_BITS: u32 = 64;
const MIN_BITS: u32 = 2;
const MAX_EXP: u32 = 12;
const MANTISSA_BITS: u32 = 2;
const MANTISSA_FAC: usize = 1 << MANTISSA_BITS;
const MAX_ALLOC_SIZE: usize = 1 << MAX_EXP;
const NUM_SIZE_CLASSES: usize = (MAX_EXP as usize - MANTISSA_FAC + 1) * MANTISSA_FAC;

#[derive(Copy, Clone)]
struct SizeClass(u8);
impl SizeClass {
    #[inline(always)]
    fn idx(&self) -> usize { 
        self.0 as usize - 1
    }

    #[inline(always)]
    fn from_idx(idx: usize) -> SizeClass {
        assert!(idx < NUM_SIZE_CLASSES);
        SizeClass((idx + 1) as u8)
    }

    #[inline(always)]
    fn size(&self) -> usize {
        //  exp | mantissa
        // (1 + mantissa) << exp
        let exp_ = (self.0 >> MANTISSA_BITS) as u32;
        let mantissa_ = (self.0 as usize) & (MANTISSA_FAC - 1);
        let (exp, mantissa) = if exp_ == 0 {
            (MIN_BITS, mantissa_)
        } else {
            (exp_ - 1 + MIN_BITS, mantissa_ + MANTISSA_FAC)
        };
        mantissa << exp
    }
    
    #[inline(always)]
    fn from_size(size: usize) -> SizeClass {
        vlog!(size);
        if size <= 1 << (MIN_BITS * MANTISSA_BITS) {
            let size = round_up(size, 1 << MIN_BITS);
            SizeClass(((size >> MIN_BITS)) as u8)
        } else {
            let shift = USIZE_BITS - MANTISSA_BITS - 1 - size.leading_zeros();
            let size = round_up(size, 1 << shift);
            let class_a = (shift as usize - MIN_BITS as usize)* MANTISSA_FAC;
            let class_b = size >> shift;
            //println!("size: {}, shift: {}, class: {} + {}", size, shift, class_a, class_b);
            SizeClass((class_a + class_b) as u8)
        }
    }
    
    fn from_layout(layout: Layout) -> SizeClass {
        let size = round_up(layout.size(), layout.align());
        SizeClass::from_size(size)
    }
}
impl fmt::Debug for SizeClass {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "SizeClass(#{} {}b)", self.idx(), self.size())
    }
}

#[test]
fn test_size_classes() {
    for &s in [4, 8, 12, 16, 20, 24, 32, 64, 128, 160].iter() {
        assert_eq!(SizeClass::from_size(s).size(), s);
    }
    assert_eq!(SizeClass::from_size(4).idx(), 0);
    assert_eq!(SizeClass::from_size(MAX_ALLOC_SIZE).idx(), NUM_SIZE_CLASSES-1);
}

// this lives in the file and can't use pointers
// we have two conflicting requirements:
// a) return blocks with as many free items as possible
// b) avoid allocating at the end of the file (and try to free the last block)
#[repr(C)]
pub struct Arena {
    header:     HeaderType,
    version:    u32,
    
    // free SuperBlocks (can be reused for any size class)
    // ordered by adress
    free:       List<Arena, SuperBlock, SuperBlockScale>,
    capacity:   AtomicU32, // in SuperBlocks
    
    root:       RcDataCell<()>,
    // bit is zero: not partially full (either in free or managed by a heap)
    // bit is one: not managed by a heap an and not in free
    partial:    [[AtomicU64; (SUPER_BLOCK_SIZE - 12) / NUM_SIZE_CLASSES / 8]; NUM_SIZE_CLASSES] // put highest possible number here…
    
}

impl Arena {
    pub unsafe fn init(&mut self, size: usize) {
        log!("Arena::init({})", size);
        let cap = (size / SUPER_BLOCK_SIZE) as u32;
        
        *self.capacity.get_mut() = cap;
        self.free.init();
        for i in (1 .. cap).rev() {
            let off: RelOffset<Arena, SuperBlock, SuperBlockScale> = RelOffset::new(i);
            off.get_as_mut(self).init_num(i);
            self.free.push(self, off);
        }
        for partial in self.partial.iter_mut() {
            for e in partial.iter_mut() {
                *e.get_mut() = 0;
            }
        }

        self.header = *b"barn";
        self.version = 1;
    }

    pub fn check_header(&self) {
        assert_eq!(self.header, HEADER_MAGIC);
        assert_eq!(self.version, 1);
    }
    
    pub fn root<T>(&self) -> RcCell<T> {
        self.check_header();
        let cell = unsafe { &*(&self.root as *const RcDataCell<()> as *const RcDataCell<T>) };
        RcCell::from_raw(cell, self)
    }

    pub fn report(&self) {
        println!("Arena REPORT");
        let cap = self.capacity.load(Relaxed) as usize;
        for (class_idx, ref partial) in self.partial.iter().enumerate() {
            let class = SizeClass::from_idx(class_idx);
            println!("class: {:?}", class);
            for (i, ref mask) in partial.iter().take(cap).enumerate() {
                let val = mask.load(Relaxed);
                if val != 0 {
                    log!("{:4}: {:064b}", i, val);
                    for bit in 0 .. 64 {
                        if (val & (1 << bit)) != 0 {
                            println!("bit: {}", bit);
                            let block_num = i as u32 * 64 + bit;
                            let rel: RelOffset<Arena, SuperBlock, SuperBlockScale> =
                                RelOffset::new(block_num);
                            unsafe { rel.get(self).report() }
                        }
                    }
                }
            }
        }
    }
    
    // this should be rather fast, in the normal case
    fn get_block(&self, class: SizeClass) -> Option<RelOffset<Arena, SuperBlock, SuperBlockScale>> {
        log!("Arena::get_block(self={:p}, class={:?})", self, class);
        // get one from the freelist using atomics
        let cap = self.capacity.load(Relaxed) as usize;
        for (i, ref mask) in self.partial[class.idx()].iter().take(cap).enumerate() {
            let val = mask.load(Relaxed);
            if val != 0 {
                log!("{:4}: {:064b}", i, val);
                let bit = val.trailing_zeros();
                // clear that bit
                mask.fetch_and(!(1 << bit), Relaxed);
                
                let block_num = i as u32 * 64 + bit;
                let rel: RelOffset<Arena, SuperBlock, SuperBlockScale> = RelOffset::new(block_num);
                let num2 = unsafe { rel.get(self).num };
                assert_eq!(num2, block_num);
                return Some(rel);
            }
        }
        if let Some(off) = self.free.pop(self) {
            unsafe {
                let block: &mut SuperBlock = off.get_as_mut(self);
                assert_eq!(block.num, off.pos());
                block.init_class(class)
            };
            log!("got one from the free list");
            return Some(off);
        }
        log!("nothing");
        None
    }
    
    fn add_memory(&self, (base, additional): (usize, usize)) {
        let base = (base / SUPER_BLOCK_SIZE) as u32;
        let additional = (additional / SUPER_BLOCK_SIZE) as u32;
        
        let mut prev: Option<RelOffset<Arena, SuperBlock, SuperBlockScale>> = None;
        // all of this is fresh memory, so no other threads can access it
        for num in (base .. base + additional).rev() {
            let rel: RelOffset<Arena, SuperBlock, SuperBlockScale> = RelOffset::new(num);
            let pos = prev.map(|p| p.pos()).unwrap_or(0);
            unsafe { rel.get(self).next().store(pos, Relaxed); }
            prev = Some(rel);
        }
        // the reason this method was called, is that we ran out of memory,
        // so the free list will be empty or very short.
        // append to it.
        self.free.append(self, prev.unwrap());
    }
    
    #[inline(always)]
    fn mark_unmanaged(&self, block: &SuperBlock) {
        println!("mark_unmanaged({})", block.num);
        assert_eq!(block.num, RelOffset::<_, _, SuperBlockScale>::from_ptr(self, block).pos());
        assert!(block.num > 0);
        // set bit
        self.partial[block.class.idx()][block.num as usize / 64].fetch_or(1 << (block.num % 64), Relaxed);
    }
    
    #[inline(always)]
    fn level_trigger(&self, block: &SuperBlock, fill: u32, cap: u32) {
        assert_eq!(block.num, RelOffset::<_, _, SuperBlockScale>::from_ptr(self, block).pos());
        assert!(block.num > 0);
        if fill == cap / 2 {
            self.mark_unmanaged(block);
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

    unsafe fn deallocate(&self, mut ptr: NonNull<u8>, layout: Layout) {
        let pos = ptr.as_ptr() as usize - self as *const Arena as usize;

        log!("deallocate({:p}) layout={:?}", ptr, layout);

        let block_pos = pos & (SUPER_BLOCK_SIZE-1); // position within the block;
        let block_off = pos & !(SUPER_BLOCK_SIZE-1);
        let block_ptr = &*((block_off + self as *const Arena as usize) as *const SuperBlock);
        let block = unsafe { &*block_ptr };
        block._free(block_pos as u32);
    }
}

pub unsafe trait AllocExt: Allocator {
    fn allocate_val<T>(&self, val: T) -> Result<NonNull<T>, AllocError> {
        let mut ptr = self.allocate_one()?;
        unsafe {
            ptr::write(ptr.as_mut(), val);
        }
        Ok(ptr.cast())
    }

    fn allocate_one<T>(&self) -> Result<NonNull<T>, AllocError> {
        let layout = Layout::new::<T>();
        let slice = self.allocate(layout)?;
        Ok(slice.as_non_null_ptr().cast())
    }
    unsafe fn deallocate_one<T>(&self, ptr: NonNull<T>) {
        let layout = Layout::new::<T>();
        log!("deallocate_one({:p}) layout={:?}", ptr, layout);
        self.deallocate(ptr.cast(), layout)
    }
}
unsafe impl<A: Allocator> AllocExt for A {}

pub struct Heap {
    barn:  Arc<Barn>,
    classes: [Cell<Option<NonNull<SuperBlock>>>; NUM_SIZE_CLASSES]
}
impl Heap {
    pub fn new(barn: Arc<Barn>) -> Heap {
        Heap {
            barn:       barn,
            classes:    repeat!(Cell::new(None); 3 6)
        }
    }
    
    #[inline(always)]
    pub fn arena(&self) -> &Arena {
        self.barn.arena()
    }
}
impl Drop for Heap {
    fn drop(&mut self) {
        for block in self.classes.iter().filter_map(|x| x.get()) {
            self.arena().mark_unmanaged(unsafe { block.as_ref() });
        }
    }
}

unsafe impl Allocator for Heap {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        unsafe {
            log!("allocate({:?})", layout);
            let size = layout.size();
            if size == 0 {
                return Ok(NonNull::slice_from_raw_parts(
                    NonNull::new_unchecked(layout.align() as *mut u8),
                    0
                ));
            }
            if size <= MAX_ALLOC_SIZE {
                let class = SizeClass::from_layout(layout);
                
                // fast path
                if let Some(block) = self.classes[class.idx()].get() {
                    let block = block.as_ref();
                    if let Some(ptr) = block.alloc() {
                        log!("allocated {} bytes in block #{} at {:p}", size, block.num, ptr);
                        return Ok(NonNull::slice_from_raw_parts(
                            NonNull::new_unchecked(ptr),
                            class.size()
                        ));
                    } else {
                        // return it
                        self.arena().mark_unmanaged(block);
                    }
                }
                
                // slow path
                // we need a new block.
                let off = match self.arena().get_block(class) {
                    Some(block) => block,
                    None => panic!("OOM")
                };
                
                let block = off.get_shared(self.arena());
                // the only possible race is another thread clearing this
                self.classes[class.idx()].set(Some(block));

                let block = block.as_ref();
                // everything is in place now ...
                let ptr = block.alloc().expect("newly obtained block nas no space");
                log!("allocated {} bytes in block #{} at {:p}", size, block.num, ptr);

                Ok(NonNull::slice_from_raw_parts(
                    NonNull::new_unchecked(ptr),
                    class.size()
                ))
            } else {
                unimplemented!()
                //self.arena().alloc(layout)
            }
        }
    }
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        self.arena().deallocate(ptr, layout)
    }
}

#[derive(Copy, Clone)]
#[repr(C)]
pub struct Unique<T> {
    off:    RelOffset<Arena, T, Unity>
}
impl<T> Unique<T> {
    #[inline(always)]
    pub fn pos(&self) -> RelOffset<Arena, T, Unity> { self.off }
    
    #[inline(always)]
    pub fn from_ptr(arena: &Arena, ptr: NonNull<T>) -> Unique<T> {
        Unique::from_pos(RelOffset::from_ptr(arena, ptr.as_ptr()))
    }
    
    #[inline(always)]
    pub fn from_pos(off: RelOffset<Arena, T, Unity>) -> Unique<T> {
        Unique { off: off }
    }
    
    #[inline(always)]
    pub fn ptr(&self, arena: &Arena) -> NonNull<T> {
        unsafe { NonNull::new(self.off.get_as_mut(arena)).unwrap() }
    }
}
impl<T> cmp::PartialEq for Unique<T> {
    fn eq(&self, rhs: &Self) -> bool {
        self.off == rhs.off
    }
}


/*
refcount = 1 -> one active user
refcount = 0 locked by one user, refcount can't be increased by others
*/

#[repr(C, packed)]
pub struct Shared<T> {
    off:    RelOffset<Arena, T, Unity>
}
impl<T> Shared<T> {
    #[inline(always)]
    fn from_pos(off: RelOffset<Arena, T, Unity>) -> Shared<T> {
        Shared { off: off }
    }
    #[inline(always)]
    pub fn from_ptr(arena: &Arena, ptr: *const T) -> Shared<T> {
        Shared { off: RelOffset::from_ptr(arena, ptr) }
    }
    #[inline(always)]
    fn pos(self) -> u32 {
        self.off.pos()
    }
    #[inline(always)]
    pub fn ptr(self, arena: &Arena) -> NonNull<T> {
        unsafe {
            NonNull::new(self.off.get(arena) as *const T as *mut T).unwrap()
        }
    }
}
impl<T> cmp::PartialEq for Shared<T> {
    fn eq(&self, rhs: &Self) -> bool {
        self.off == rhs.off
    }
}
impl<T> Clone for Shared<T> {
    fn clone(&self) -> Shared<T> {
        Shared { off: self.off }
    }
}
impl<T> Copy for Shared<T> {}

#[repr(C)]
pub struct Data<T: ?Sized> {
    rc:     AtomicU32,
    data:   T
}

pub struct Box<'a, T: 'a> {
    inner:  NonNull<Data<T>>,
    arena:  &'a Arena,
}
impl<'a, T: 'a> Box<'a, T> {
    fn inner(&self) -> &Data<T> {
        unsafe { self.inner.as_ref() }
    }
    pub fn new(heap: &'a Heap, inner: T) -> Result<Box<'a, T>, AllocError> {
        let mut ptr = heap.allocate_val(Data {
            data: inner,
            rc: AtomicU32::new(1)
        })?;
        unsafe {
            Ok(Box {
                inner: ptr,
                arena: heap.arena()
            })
        }
    }
    pub fn into_rc(self) -> Rc<'a, T> {
        // set refcount to one
        self.inner().rc.store(1, Release);
        let rc = Rc {
            inner:  self.inner,
            arena:  self.arena,
        };
        mem::forget(self);
        rc
    }
}
impl<'a, T: 'a> Drop for Box<'a, T> {
    #[inline(always)]
    fn drop(&mut self) {
        unsafe { 
            let layout = Layout::new::<Data<T>>();
            self.arena.deallocate(self.inner.cast(), layout);
        }
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
        unsafe { &mut self.inner.as_mut().data }
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
pub struct Rc<'a, T: 'a> {
    inner: NonNull<Data<T>>,
    arena: &'a Arena
}
impl<'a, T: 'a> Rc<'a, T> {
    pub fn new(heap: &'a Heap, inner: T) -> Result<Rc<'a, T>, AllocError> {
        let ptr = heap.allocate_val(Data {
            data: inner,
            rc: AtomicU32::new(1)
        })?;
        unsafe {
            Ok(Rc {
                inner: ptr,
                arena: heap.arena()
            })
        }
    }
    fn from_shared(arena: &'a Arena, pos: Shared<Data<T>>) -> Rc<'a, T> {
        Rc {
            inner: pos.ptr(arena),
            arena
        }
    }
    fn inner(&self) -> &Data<T> {
        unsafe { self.inner.as_ref() }
    }
    pub fn lock(self) -> Result<Box<'a, T>, Rc<'a, T>> {
        match self.inner().rc.compare_exchange(1, 0, Acquire, Relaxed) {
            Ok(0) => Ok(Box {
                inner: self.inner,
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
        let s = Shared::from_pos(self.offset());
        mem::forget(self);
        s
    }
    fn offset(&self) -> RelOffset<Arena, Data<T>, Unity> {
        RelOffset::from_ptr(self.arena, self.inner.as_ptr())
    }
}
impl<'a, T> Drop for Rc<'a, T> {
    fn drop(&mut self) {
        log!("Rc::drop");

        // if the refcount was one, we have to drop it
        let refcount = self.inner().rc.fetch_sub(1, Release);
        assert!(refcount > 0);

        if refcount == 1 {
            log!("deallocating");
            unsafe {
                let layout = Layout::new::<Data<T>>();
                self.arena.deallocate(self.inner.cast(), layout);
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

impl<'a, T: Relative + 'a> Packable for Box<'a, T> {
    type Packed = Unique<Data<T>>;
}
unsafe impl<'a, T: Relative + 'a> Stash<'a> for Box<'a, T> {
    fn pack(self, heap: &'a Heap) -> Self::Packed {    
        let p = Unique::from_ptr(self.arena, self.inner);
        mem::forget(self);
        p
    }
    fn unpack(heap: &'a Heap, p: Self::Packed) -> Self {
        Box { inner: p.ptr(heap.arena()), arena: heap.arena() }
    }
}
impl<'a, T: Relative + 'a> Packable for Rc<'a, T> {
     type Packed = Shared<Data<T>>;
}
unsafe impl<'a, T: Relative + 'a> Stash<'a> for Rc<'a, T> {   
    fn pack(self, heap: &'a Heap) -> Self::Packed {
        let p = Shared::from_ptr(self.arena, self.inner.as_ptr());
        mem::forget(self);
        p
    }
    fn unpack(heap: &'a Heap, p: Self::Packed) -> Self {
        Rc { inner: p.ptr(heap.arena()), arena: heap.arena() }
    }
}
impl<'a, T: Relative + 'a> PartialEq for Rc<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
    fn ne(&self, other: &Self) -> bool {
        self.inner != other.inner
    }
}
impl<'a, T: Relative + 'a> Eq for Rc<'a, T> {}
impl<'a, T: Relative + 'a> Hash for Rc<'a, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.inner.hash(state)
    }
}

pub struct DataCell<T> {
    pos:    AtomicU32, // points to a shared Data<T>
    _m:     PhantomData<T>
}
impl<T> DataCell<T> {
    // 0 -> empty
    // 1 -> being swapped
    
    pub fn empty() -> Self {
        DataCell {
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
                p => return Some(Shared::from_pos(RelOffset::new(p)))
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
}

pub struct RcDataCell<T> {
    cell:    DataCell<T>,
    waiting: AtomicU32
}

pub struct WaitError;

/// Reference counted cell
/// 
/// This uses an Arena reference instead of a Heap as it can only deallocate
pub struct RcCell<'a, T: 'a> {
    inner:  &'a RcDataCell<T>,
    arena:  &'a Arena
}
impl<'a, T: 'a> RcCell<'a, T> {
    pub fn from_raw(inner: &'a RcDataCell<T>, arena: &'a Arena) -> RcCell<'a, T> {
        RcCell {
            inner,
            arena
        }
    }

    pub fn get(&self) -> Option<Rc<'a, T>> {
        self.inner.cell.swap(|c| match c {
            None => (None, None),
            Some(p) => {
                let rc = Rc::from_shared(self.arena, p);
                (Some(rc.clone().to_shared()), Some(rc))
            }
        })
    }
    
    pub fn swap(&self, rc: Rc<'a, T>) -> Option<Rc<'a, T>> {
        let new_val = Some(rc.to_shared());
        let old_val = self.inner.cell.swap(|c| (
            new_val,   // value to be stored
            c          // value returned
        ));

        if new_val != old_val {
            let waiting = self.inner.waiting.load(Relaxed);
            vlog!(waiting);
            if waiting != 0 {
                futex::wake_all(&self.inner.cell.pos).unwrap();
            }
        }

        old_val.map(|v| Rc::from_shared(self.arena, v))
    }

    pub fn wait(&self, old: Option<&Rc<'a, T>>, timeout: Option<Duration>) -> Option<Rc<'a, T>> {
        let old_val = old.map(|p| p.offset().pos()).unwrap_or(0);
        with(&self.inner.waiting, move || {
            // current value
            let val = self.inner.cell.pos.load(Relaxed);

            // it already changed
            if val != old_val {
                return Ok(());
            }

            futex::wait(&self.inner.cell.pos, val, timeout)
        }).expect("failed to wait");
        
        self.get()
    }
}

fn with<F: FnOnce() -> O, O>(counter: &AtomicU32, f: F) -> O {
    counter.fetch_add(1, Acquire);
    let o = f();
    counter.fetch_sub(1, Release);
    o
}
