#![allow(warnings)]

extern crate testgen;

use std::ops::Range;
use testgen::{fail, fn_test, multi_fail, multi_pass, pass};

#[fn_test(input = foo(1), expect = 2)]
#[fn_test(name = "non_default_test", input = 2, expect = 3)]
fn add_one(n: i32) -> i32 {
    n + 1
}

fn foo(n: i32) -> i32 {
    n
}

#[fn_test(input = [1, 2, 3], expect = [2, 3, 4])]
fn multi_test(n: i32) -> i32 {
    n + 1
}

#[fn_test(input = 1..3, expect = 2..4)]
fn range_test(mut r: Range<i32>) -> Range<i32> {
    r.start += 1;
    r.end += 1;

    r
}

#[pass((2, 3) => 6)]
#[fail((2, 2) => 6)]
fn times(n: i32, m: i32) -> i32 {
    n * m
}

#[multi_pass(1 => 2, 2 => 4, 5 => 10)]
#[multi_fail(1 => 1, 2 => 2, 5 => 5)]
fn times_two(n: i32) -> i32 {
    n * 2
}

#[pass(name="ayy", 1 => 0)]
#[fail(name="lmao", 1 => 1)]
fn minus_one(n: i32) -> i32 {
    n - 1
}

#[multi_pass(name="hella", 1 => 0, 2 => 1, 3 => 2)]
#[multi_fail(name="rad", 1 => 1, 2 => 2, 3 => 3)]
fn minus(n: i32) -> i32 {
    n - 1
}

#[pass(name="sum", vec![1,2,3] => 6)]
fn vec_sum(i: Vec<u32>) -> u32 {
    i.iter().sum()
}

#[pass(name="calling_fns", Dummy::new() => 2)]
fn extract_dummy(d: Dummy) -> i32 {
    d.x
}

struct Dummy {
    x: i32,
}

impl Dummy {
    fn new() -> Dummy {
        Dummy {
            x: 2
        }   
    }
}

fn main() {}
