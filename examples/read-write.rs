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
        let root = b.root();
        match root.get() {
            Some(d) => println!("read 1: {:?}", d),
            None => println!("read 1: nothing")
        }
        let heap = Heap::new(b.clone());
        
        let data = Box::new(&heap, [1, 2, 3, 4u8]).unwrap();
        println!("data: {:?}", data);
        
        root.swap(data.into_rc());
        
        match root.get() {
            Some(d) => println!("read 2: {:?}", d),
            None => println!("read 2: nothing")
        }
    };
    
    b.arena().report();
}
