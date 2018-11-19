#![allow(warnings)]

extern crate testgen;

use testgen::pass;

struct Foo {
    f: i32,
}

fn cmp_f(a: Foo, b: Foo) -> bool {
    a.f == b.f
}

#[pass(cmp_fn="cmp_f", Foo { f: 0 } => Foo { f: 1 })]
fn inc_f(mut foo: Foo) -> Foo {
    foo.f += 1;
    foo
}
