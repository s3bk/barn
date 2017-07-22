
#![feature(integer_atomics, allocator_api, i128_type, alloc, unique)]
#![feature(placement_new_protocol, nonzero, placement_in_syntax, shared)]
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
extern crate parking_lot;

#[macro_use]
mod util;
#[macro_use]
mod stash;
mod data;
mod arena;

pub use arena::*;
pub use stash::*;
pub use data::*;

const SUPER_BLOCK_SIZE: usize = 16 * 1024;

#[inline(always)]
fn round_up(n: usize, k: usize) -> usize {
    let c = n % k;
    if c == 0 {
        n
    } else {
        (n + k) - c
    }
}

fn div_ceil(n: usize, div: usize) -> usize {
    round_up(n, div) / div // could be faster?
}
