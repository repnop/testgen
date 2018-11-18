extern crate testgen;
use testgen::{multi_fail, multi_pass, pass};

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
