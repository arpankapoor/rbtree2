# red-black tree in rust

an attempt to create a drop-in replacement for a [`BTreeMap`](https://doc.rust-lang.org/std/collections/struct.BTreeMap.html) backed
by a [red-black tree](https://en.wikipedia.org/wiki/Red%E2%80%93black_tree).

Current status: removal functions seem to have a few bugs

# references

- [CLRS](https://en.wikipedia.org/wiki/Introduction_to_Algorithms)
- Linux kernel's [rbtree implementation](https://www.kernel.org/doc/Documentation/rbtree.txt)
- [Learn Rust with Entirely Too Many Linked Lists](https://rust-unofficial.github.io/too-many-lists/index.html)
