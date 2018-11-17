//! **This library is still very early in development!**
//!
//! As of this published (0.0.1) version, you can make very basic generated
//! tests only on free functions by importing the `inplace_test` macro and using
//! it like so:
//!
//! ```rust
//! extern crate testgen;
//! use testgen::inplace_test;
//!
//! #[inplace_test(optional_name, 1 => 2)]
//! fn add_one(n: i32) -> i32 {
//!     n + 1
//! }
//!
//! fn main() {}
//! ```
//!
//! The macro name and usage **will** change, so its recommended to wait for
//! more progress to be made before considering using this outside of toy
//! projects.

extern crate proc_macro;
extern crate proc_macro2;
extern crate quote;
extern crate syn;

use self::proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn::parse::{Parse, ParseStream, Result};
use syn::punctuated::Punctuated;
use syn::{parse_macro_input, Expr, Ident, ItemFn, Token};

struct Args {
    name: Option<Ident>,
    input: Expr,
    expected: Expr,
}

impl Parse for Args {
    fn parse(input: ParseStream) -> Result<Self> {
        let named = input.peek(Ident) && input.peek2(Token![,]);

        let name = if named {
            let name = Some(input.parse::<Ident>()?);
            input.parse::<Token![,]>()?;

            name
        } else {
            None
        };

        let mut vars = Punctuated::<Expr, Token![=>]>::parse_terminated(input)?.into_iter();
        let input = vars.next().unwrap();
        let expected = vars.next().unwrap();
        Ok(Args {
            name,
            input,
            expected,
        })
    }
}

/// Generates a test function that `assert_eq!`s the before and after
/// expressions given.
#[proc_macro_attribute]
pub fn inplace_test(args: TokenStream, input: TokenStream) -> TokenStream {
    let input_fn = parse_macro_input!(input as ItemFn);
    let Args {
        name,
        input: input_expr,
        expected,
    } = parse_macro_input!(args as Args);

    let test_fn = name
        .unwrap_or_else(|| Ident::new(&format!("testing_{}", input_fn.ident), Span::call_site()));

    let fn_ident = input_fn.ident.clone();

    TokenStream::from(quote! {
        #input_fn
        #[test]
        fn #test_fn() {
            assert_eq!( crate::#fn_ident(#input_expr), #expected);
        }
    })
}
