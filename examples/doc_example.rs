extern crate testgen;
use testgen::{fail, multi_fail, multi_pass, pass};

#[pass(name="optional", 1 => 2)]
#[multi_fail(1 => 1, 2 => 2, 3 => 3)]
fn add_one(n: i32) -> i32 {
    n + 1
}

// Multiple arguments are passed in like a tuple.
// Though to use an actual tuple use `((a, b))`.
// Single-argument functions can have the parenthesis elided in most cases.
#[multi_pass((1, 2) => 3, (3, 4) => 7)]
#[fail((1, 2) => 10)]
fn add(n: i32, m: i32) -> i32 {
    n + m
}

fn main() {}
