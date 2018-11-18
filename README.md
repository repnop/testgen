# `testgen`

**This library is still very early in development!**

Generate simple tests with `testgen`!

## Examples

```rust
extern crate testgen;
use testgen::{pass, multi_fail, multi_pass};
#[pass(name="optional", 1 => 2)]
#[multi_fail(1 => 1, 2 => 2, 3 => 3)]
fn add_one(n: i32) -> i32 {
    n + 1
}
#[multi_pass((1, 2) => 3, (3, 4) => 7)]
fn add(n: i32, m: i32) -> i32 {
    n + m
}
fn main() {}
```

Output:

```
   Compiling testgen v0.0.1 (/mnt/F/Development/Rust/testgen)
    Finished dev [unoptimized + debuginfo] target(s) in 4.57s
     Running target/debug/examples/doc_example-79f4317fab9ffdf5

running 3 tests
test add_multitest_pass ... ok
test optional ... ok
test add_one_multitest_fail ... ok

test result: ok. 3 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out
```

## License

`testgen` is licensed under both MIT and Apache 2.0