use alloc::raw_vec::RawVec;
use arena::Arena;

use Stash;

type RefId = u32;
/*
pub struct Encoder {
    known: &mut OrderMap
}
impl Encoder {
    pub fn add_field<T: Stash>(&mut self, name: &str, offset: usize, _: &T) {
    
    }
    pub fn add_type<T>(&mut self, typ: TypeInfo);
    
    fn insert(&mut self, typ: TypeInfo) -> Rc<TypeInfo>;
    
    fn add_vec<T: Stash>(&mut self) -> TypeInfo {
        let t = T::encode_type(self);
        self.insert(t)
}
*/
macro_rules! primitives {
    ($($ty:ty => $name:ident),*) => ( $(
        unsafe impl<'a> Stash<'a> for $ty {
            type Packed = Self;
            #[inline(always)]
            fn pack(self) -> Self { self }
            #[inline(always)]
            fn unpack(_: &'a Arena, p: Self) -> Self { p }
            /*
            fn encode_type(t: &mut Encoder) -> TypeInfo {
                t.add_type(stringify!($ty), TypeInfo :: $name);
            }
            */
        }
    )* )
}

struct StructInfo {
    fields: Vec<(String, TypeInfo)>,
    name:   String
}

struct TupleInfo {
    fields: Vec<TypeInfo>
}

struct ArrayInfo {
    len:    u32,
    inner:  TypeInfo
}


// len 8
enum TypeInfo {
    Unit,
    Bool,
    U8, I8, U16, I16, U32, I32, U64, I64, U128, I128,
    F32, F64,
    Vec(u32),       // pos of Shared<TypeInfo> for inner type
    String(u32),    // pos of Shared<String>
    Tuple(u32),     // pos of Shared<TupleInfo>
    Struct(u32),    // pos of Shared<StructInfo>
}

primitives!(
    ()  => Unit,
    u8  => U8,
    i8  => I8,
    u16 => U16,
    i16 => I16,
    u32 => U32,
    i32 => I32,
    u64 => U64,
    i64 => I65,
    u128 => U128,
    i128 => I128,
    f32 => F32,
    f64 => F64,
    bool => Bool
);

#[derive(Copy, Clone)]
pub struct PackedRawVec {
    pos:    u32,
    cap:    u32
}

unsafe impl<'a, T> Stash<'a> for RawVec<T, &'a Arena> {
    type Packed = PackedRawVec;
    
    fn pack(self) -> PackedRawVec {
        let (ptr, cap, a) = self.into_raw_parts();
        PackedRawVec {
            pos: a.pos_for_ptr(ptr),
            cap: cap as u32
        }
    }
    fn unpack(a: &'a Arena, p: PackedRawVec) -> Self {
        unsafe {
            RawVec::from_raw_parts_in(a.ptr_for_pos::<T>(p.pos) as *mut T, p.cap as usize, a)
        }
    }
}

#[derive(Copy, Clone)]
pub struct PackedVec {
    raw: PackedRawVec,
    len: u32
}
unsafe impl<'a, T> Stash<'a> for Vec<T, &'a Arena> {
    type Packed = PackedVec;
    
    fn pack(self) -> PackedVec {
        let (raw, len) = self.into_raw_vec_and_len();
        PackedVec {
            raw: raw.pack(),
            len: len as u32
        }
    }
    
    fn unpack(a: &'a Arena, p: PackedVec) -> Self {
        unsafe {
            Vec::from_raw_vec_and_len(RawVec::unpack(a, p.raw), p.len as usize)
        }
    }
}
