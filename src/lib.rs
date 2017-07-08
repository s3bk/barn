#![feature(integer_atomics, allocator_api, i128_type, alloc)]
#![feature(placement_new_protocol, nonzero, placement_in_syntax)]
/**
## Type safety
Type safety is ensured by storing all used types in the database.

```ignore
Items
    Primitives (numbers)            1 - 13
    bool
    String                          65
    Vec<Item>                       64
    Tuple<Len, Items>               32
    Array<Len, Item>                33
    Map                             
        HashMap (bloom filter)      128
        BTreeMap                    129
    Unit                            0
    Type
Rc

Species encoding

## File format

### header
    0-3     b"Barn"
    4-7     barn version (32 bit, unsigned, little-endian)
    8-15    root
    
    
### Section (sendable)
Shared Section (immutable, rc>=1)
 - can be cloned to a Owned Section

Owned Section (mutable, rc=1)
    
    
Root (shared)
```

*/

extern crate memmap;
extern crate alloc;
extern crate core;

mod data;
mod arena;
mod types;

use data::{Writer, Reader};
use arena::*;
//use types::Encoder;

/// stores information about a type
pub struct Species {}

pub unsafe trait Stash<'a> {
    type Packed: Copy;
    
    //fn get_type(t: &mut TypeWriter);
    
    fn pack(self) -> Self::Packed;
    fn unpack(a: &'a Arena, p: Self::Packed) -> Self;
}

macro_rules! field {
    ($typewriter:ident, $selv:ident . $field:ident) => (
        t.add_field(stringify!($field), $field as usize - $selv as usize, &$selv.$field);
    )
}

#[test]
fn increment() {
    
}
/*
#[test]
fn test_barn() {

    #[derive(Barn)]
    struct Adress {
        house_nr:   u16,
        street:     String,
        city:       String,
        country:    String
    }
    impl Stash for Adress {
        fn encode_type(&self, t: &mut Encoder) {
            t.add_struct("Adress", |t| {
                field!(t, self.housr_nr);
                field!(t, self.street);
                field!(t, self.city);
                field!(t, self.country);
            });
        }
    }

    #[derive(Barn)]
    struct Letter {
        sender: (String, Adress),
        recipient: (String, Adress),
        content:    Vec<String>
    }
}
*/
