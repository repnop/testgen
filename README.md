# `testgen`

_**This crate is very early in development! The API will change. Not ready for production use at all.**_

A proc macro crate to generate a variety of test functions.

## Example

```rust
extern crate testgen;
use testgen::inplace_test;

#[inplace_test(optional_name, 1 => 2)]
fn add_one(n: i32) -> i32 {
    n + 1
}

fn main() {}
```

## License

`testgen` is licensed under both MIT and Apache 2.0