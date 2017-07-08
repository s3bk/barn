# barn
Provides space for Copy-On-Write structures, and other animals.

This is basically your normal Rust Heap, except that it is backed by a MemoryMap and made relocatable (by using relative offsets).
