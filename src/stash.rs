pub use std::{ptr, mem};
use alloc::raw_vec::RawVec;
use istring::{self, IString};
use arena::{Heap, Unique, Shared, Data};
use tuple;

/// Marker trait for Position independend Data
///
/// I.e. anything that does not include absolute addresses is consiered to be relative.
pub unsafe trait Relative {}

macro_rules! impl_relative {
    ($($t:ty),*) => ($(unsafe impl Relative for $t {})*)
}
impl_relative!((), bool, u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, f32, f64);
macro_rules! impl_array {
    ($($n:tt)*) => ( $(
        unsafe impl<T: Relative> Relative for [T; $n] {}
    )* )
}
impl_array!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32);
unsafe impl<T: Relative> Relative for Unique<T> {}
unsafe impl<T: Relative> Relative for Shared<T> {}
unsafe impl<T: Relative> Relative for Data<T> {}

pub trait Packable {
    type Packed: Relative;
}
impl<T: Relative> Packable for T {
    type Packed = T;
}

/// Utility trait to transition between Relative and Absolute references
pub unsafe trait Stash<'a>: Packable {
    fn pack(self) -> Self::Packed;
    fn unpack(a: &'a Heap, p: Self::Packed) -> Self;
}
unsafe impl<'a, T> Stash<'a> for T where T: Relative + Packable<Packed=T> {
    fn pack(self) -> Self::Packed { self }
    fn unpack(_: &'a Heap, p: Self::Packed) -> Self { p }
}

#[repr(C)]
pub struct PackedRawVec<T: Relative> {
    pos:   Unique<T>,
    cap:   u32
}
unsafe impl<T: Relative> Relative for PackedRawVec<T> {}
impl<'a, T: Relative> Packable for RawVec<T, &'a Heap> {
    type Packed = PackedRawVec<T>;
}
unsafe impl<'a, T: Relative> Stash<'a> for RawVec<T, &'a Heap> {   
    fn pack(self) -> Self::Packed {
        let (ptr, cap, a) = self.into_raw_parts();
        PackedRawVec {
            pos: Unique::from_ptr(a.arena(), ptr),
            cap: cap as u32
        }
    }
    fn unpack(a: &'a Heap, p: Self::Packed) -> Self {
        unsafe {
            RawVec::from_raw_parts_in(p.pos.ptr(a.arena()), p.cap as usize, a)
        }
    }
}

#[repr(C)]
pub struct PackedVec<T: Relative> {
    raw: PackedRawVec<T>,
    len: u32
}
unsafe impl<T: Relative> Relative for PackedVec<T> {}
impl<'a, T: Relative> Packable for Vec<T, &'a Heap> {
    type Packed = PackedVec<T>;
}
unsafe impl<'a, T: Relative> Stash<'a> for Vec<T, &'a Heap> {
    fn pack(self) -> Self::Packed {
        let (raw, len) = self.into_raw_vec_and_len();
        PackedVec {
            raw: raw.pack(),
            len: len as u32
        }
    }
    
    fn unpack(a: &'a Heap, p: Self::Packed) -> Self {
        unsafe {
            Vec::from_raw_vec_and_len(RawVec::unpack(a, p.raw), p.len as usize)
        }
    }
}

#[cfg(target_endian = "little")]
#[derive(Copy, Clone)]
#[repr(C)]
struct PackedStringInline {
    data: [u8; 11],
    len: u8
}

#[cfg(target_endian = "little")]
#[derive(Copy, Clone)]
#[repr(C)]
struct PackedStringHeap {
    pos: Unique<u8>,
    cap: u32,
    len: u32
}

union PackedStringUnion {
    inline: PackedStringInline,
    heap:   PackedStringHeap
}

#[repr(C)]
pub struct PackedString {
    union: PackedStringUnion
}
impl_relative!(PackedString);
impl<'a> Packable for IString<&'a Heap> {
    type Packed = PackedString;
}
unsafe impl<'a> Stash<'a> for IString<&'a Heap> {
    fn pack(mut self) -> Self::Packed {
        // there are 3 cases:
        // a) already on the heap -> keep it that way
        // b) inlined and fits in 11 bytes -> keep it inlined
        // c) inlined and does not fit -> move to heap

        let len = self.len();
        assert!(len < (1usize << 31));
        
        if self.is_inline() && len > 11 {
            self.move_to_heap(len); // eliminates case 'c'
        }

        let u = if self.is_inline() { // case 'b'
            let mut inline = PackedStringInline {
                data: [0; 11],
                len:  len as u8 | 1 << 7
            };
            inline.data[0..len].copy_from_slice(self.as_bytes());
            PackedStringUnion { inline: inline }
        } else { // case 'a'
            let (data, heap) = self.to_heap();
            let packed_heap = PackedStringHeap {
                pos: Unique::from_ptr(heap.arena(), data.ptr.as_ptr()),
                cap: data.cap as u32,
                len: data.len as u32
            };
            PackedStringUnion { heap: packed_heap }
        };

        PackedString { union: u }
    }
    fn unpack(heap: &'a Heap, p: Self::Packed) -> Self {
        unsafe {
            if p.union.heap.len & (1 << 31) == 0 { // not inlined
                let string_heap = istring::Heap {
                    ptr: ptr::Unique::new(p.union.heap.pos.ptr(heap.arena())),
                    cap: p.union.heap.cap as usize,
                    len: p.union.heap.len as usize
                };
                IString::from_heap(string_heap, heap)
            } else { // inlined
                let len = p.union.inline.len & !(1 << 7);
                let mut inline = istring::Inline {
                    data: [0; 23],
                    len:  len
                };
                inline.data[..11].copy_from_slice(&p.union.inline.data); // don't bother to use len here.
                IString::from_inline(inline, heap)
            }
        }

    }
}

macro_rules! impl_stash {
    ($($Tuple:ident { $($T:ident . $t:ident . $idx:tt),* } )*) => ($(
        #[repr(C, packed)]
        pub struct $Tuple<$($T: Relative),*>( $( pub $T ),* );
        unsafe impl<$($T: Relative),*> Relative for $Tuple<$($T),*> {}
        impl<$($T: Packable),*> Packable for tuple::$Tuple<$($T),*> {
            type Packed = $Tuple<$($T::Packed),*>;
        }
        unsafe impl<'a $(,$T: Stash<'a>)*> Stash<'a> for tuple::$Tuple<$($T),*> {
            fn pack(self) -> Self::Packed {
                let tuple::$Tuple($($t),*) = self;
                $Tuple($($t.pack()),*)
            }
            fn unpack(heap: &'a Heap, p: Self::Packed) -> Self {
                let $Tuple($($t),*) = p;
                tuple::$Tuple($($T::unpack(heap, $t)),*)
            }
        }
        impl<$($T: $crate::Packable),*> Packable for ($($T,)*) {
            type Packed = $Tuple<$($T::Packed),*>;
        }
        unsafe impl<'a $(,$T: Stash<'a>)*> Stash<'a> for ($($T,)*) {
            fn pack(self) -> Self::Packed {
                let ($($t,)*) = self;
                $Tuple($($t.pack()),*)
            }
            fn unpack(heap: &'a Heap, p: Self::Packed) -> Self {
                let $Tuple($($t),*) = p;
                ($($T::unpack(heap, $t),)*)
            }
        }
        
    )*)
}

impl_tuple!(impl_stash);
