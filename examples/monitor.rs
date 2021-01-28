#![feature(box_syntax, core_intrinsics)]

use barn::*;

fn main() {
    ::std::panic::set_hook(box |i| {
        let msg = i.payload().downcast_ref::<&str>().map(|&s| s).unwrap_or("");
        match i.location() {
            Some(loc) => eprintln!("PANIC at {}:{}: {}", loc.file(), loc.line(), msg),
            None => eprintln!("PANIC at ???: {}", msg)
        }
        unsafe { std::intrinsics::breakpoint() }
    });
    simple_signal::set_handler(&[simple_signal::Signal::Segv], |_| {
        eprintln!("Segfault");
        unsafe { std::intrinsics::breakpoint() }
    });

    let b = Barn::load_path("foo.barn", true);
    {
        let root: RcCell<[u8; 4]> = b.root();
        let mut val = root.get();
        loop {
            println!("value: {:?}", val);
            val = root.wait(val.as_ref(), None);
        }
    };
}
