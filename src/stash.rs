use alloc::raw_vec::RawVec;
use super::{Arena, Unique};

pub unsafe trait Stash<'a> {
    type Packed;
    
    fn pack(self) -> Self::Packed;
    fn unpack(a: &'a Arena, p: Self::Packed) -> Self;
}

#[macro_export]
macro_rules! impl_copy_stash {
    ($t:ident $(< $( $g:ident ),* > )+ ) => (
        unsafe impl<'a $(, $( $g ),* )+> Stash<'a> for $t $(< $( $g ),* > )+ {
            type Packed = Self;
            
            fn pack(self) -> Self { self }
            fn unpack(a: &'a Arena, p: Self) -> Self { p }
        }
    )
}


#[repr(C, packed)]
pub struct PackedRawVec<T> {
    pos:   Unique<T>,
    cap:    u32
}

unsafe impl<'a, T> Stash<'a> for RawVec<T, &'a Arena> {
    type Packed = PackedRawVec<T>;
    
    fn pack(self) -> Self::Packed {
        let (ptr, cap, a) = self.into_raw_parts();
        PackedRawVec {
            pos: Unique::from_ptr(a, ptr),
            cap: cap as u32
        }
    }
    fn unpack(a: &'a Arena, p: Self::Packed) -> Self {
        unsafe {
            RawVec::from_raw_parts_in(p.pos.ptr(a), p.cap as usize, a)
        }
    }
}

#[repr(C, packed)]
pub struct PackedVec<T> {
    raw: PackedRawVec<T>,
    len: u32
}
unsafe impl<'a, T> Stash<'a> for Vec<T, &'a Arena> {
    type Packed = PackedVec<T>;
    
    fn pack(self) -> Self::Packed {
        let (raw, len) = self.into_raw_vec_and_len();
        PackedVec {
            raw: raw.pack(),
            len: len as u32
        }
    }
    
    fn unpack(a: &'a Arena, p: Self::Packed) -> Self {
        unsafe {
            Vec::from_raw_vec_and_len(RawVec::unpack(a, p.raw), p.len as usize)
        }
    }
}
