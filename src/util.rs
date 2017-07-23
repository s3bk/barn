macro_rules! repeat {
    // DONE
    (@ [], [$($args:expr,)*]; $arg:expr) => ([$($args,)*]);
    // accumulate                                                              1         2         3         4         5         6         7         8         9         10
    (@ [0 $($t:tt)*], [$($acc:expr,)*]; $arg:expr) => (repeat!(@ [$($t)*], [$($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)*      ]; $arg));
    (@ [1 $($t:tt)*], [$($acc:expr,)*]; $arg:expr) => (repeat!(@ [$($t)*], [$($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $arg,]; $arg));
    (@ [2 $($t:tt)*], [$($acc:expr,)*]; $arg:expr) => (repeat!(@ [$($t)*], [$($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $arg, $arg,]; $arg));
    (@ [3 $($t:tt)*], [$($acc:expr,)*]; $arg:expr) => (repeat!(@ [$($t)*], [$($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $arg, $arg, $arg, ]; $arg));
    (@ [4 $($t:tt)*], [$($acc:expr,)*]; $arg:expr) => (repeat!(@ [$($t)*], [$($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $arg, $arg, $arg, $arg, ]; $arg));
    (@ [5 $($t:tt)*], [$($acc:expr,)*]; $arg:expr) => (repeat!(@ [$($t)*], [$($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $arg, $arg, $arg, $arg, $arg, ]; $arg));
    (@ [6 $($t:tt)*], [$($acc:expr,)*]; $arg:expr) => (repeat!(@ [$($t)*], [$($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $arg, $arg, $arg, $arg, $arg, $arg, ]; $arg));
    (@ [7 $($t:tt)*], [$($acc:expr,)*]; $arg:expr) => (repeat!(@ [$($t)*], [$($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $arg, $arg, $arg, $arg, $arg, $arg, $arg, ]; $arg));
    (@ [8 $($t:tt)*], [$($acc:expr,)*]; $arg:expr) => (repeat!(@ [$($t)*], [$($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $arg, $arg, $arg, $arg, $arg, $arg, $arg, $arg, ]; $arg));
    (@ [9 $($t:tt)*], [$($acc:expr,)*]; $arg:expr) => (repeat!(@ [$($t)*], [$($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $($acc,)* $arg, $arg, $arg, $arg, $arg, $arg, $arg, $arg, $arg, ]; $arg));
    // input
    ($arg:expr; $($bits:tt)*) => (repeat!(@ [$($bits)*], []; $arg));
}


macro_rules! size {
    ($t:ty) => (::std::mem::size_of::<$t>())
}
macro_rules! vlog {
    ($var:expr) => (
        eprintln!(concat!(stringify!($var), ": {:?}"), $var)
    )
}
macro_rules! log {
    ($msg:expr $(,$args:expr)*) => (eprintln!($msg $(, $args)*))
}

use libc;
use std::{time, ptr};

#[inline(always)]
pub fn ptr_opt<T>(r: Option<&T>) -> *const T {
    r.map(|r| r as *const T).unwrap_or(ptr::null())
}

#[inline(always)]
pub fn timespec(t: time::Duration) -> libc::timespec {
    libc::timespec {
        tv_sec:  t.as_secs() as i64,
        tv_nsec: t.subsec_nanos() as i64
    }
}
