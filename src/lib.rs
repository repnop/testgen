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

enum Either<T, U> {
    Left(T),
    Right(U),
}

struct Args {
    name: Option<syn::LitStr>,
    input: Either<Expr, Vec<Expr>>,
    expected: Either<Expr, Vec<Expr>>,
    _should_fails: Option<(Vec<Expr>, Vec<Expr>)>,
}

impl Parse for Args {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut name = None;
        let mut _input = None;
        let mut expected = None;
        let mut _should_fails = None;

        loop {
            let ident = input.parse::<Ident>()?;

            match &*ident.to_string() {
                "name" => {
                    input.parse::<Token![=]>()?;
                    name = Some(input.parse::<syn::LitStr>()?);
                }
                "input" => {
                    input.parse::<Token![=]>()?;
                    if input.peek(syn::token::Bracket) {
                        let contents;
                        syn::bracketed!(contents in input);

                        let exprs = Punctuated::<Expr, Token![,]>::parse_terminated(&contents)?
                            .into_iter()
                            .collect();

                        _input = Some(Either::Right(exprs));
                    } else {
                        _input = Some(Either::Left(input.parse::<Expr>()?));
                    }
                }
                "expect" => {
                    input.parse::<Token![=]>()?;

                    if input.peek(syn::token::Bracket) {
                        let contents;
                        syn::bracketed!(contents in input);

                        let exprs = Punctuated::<Expr, Token![,]>::parse_terminated(&contents)?
                            .into_iter()
                            .collect();;

                        expected = Some(Either::Right(exprs));
                    } else {
                        expected = Some(Either::Left(input.parse::<Expr>()?));
                    }
                }
                "should_fail" => {}
                _ => {}
            }

            if input.is_empty() {
                break;
            } else {
                input.parse::<Token![,]>()?;
            }
        }

        Ok(Args {
            name,
            input: _input.unwrap(),
            expected: expected.unwrap(),
            _should_fails,
        })
    }
}

#[derive(Clone)]
struct PassFailArgs {
    named: Option<syn::LitStr>,
    args: Vec<Expr>,
    expected: Expr,
}

impl Parse for PassFailArgs {
    fn parse(input: ParseStream) -> Result<Self> {
        let named = if input.peek(Ident) && input.peek2(Token![=]) {
            let ident = input.parse::<Ident>()?;

            if &ident != "name" {
                panic!("You must enclose this expression in parenthesis.");
            }

            input.parse::<Token![=]>()?;

            let name = input.parse::<syn::LitStr>()?;

            input.parse::<Token![,]>()?;

            Some(name)
        } else {
            None
        };

        let args = if input.peek(syn::token::Paren) {
            let inner_exprs;

            syn::parenthesized!(inner_exprs in input);

            Punctuated::<Expr, Token![,]>::parse_separated_nonempty(&inner_exprs)?
                .into_iter()
                .collect()
        } else {
            vec![input.parse::<Expr>()?]
        };

        input.parse::<Token![=>]>()?;

        let expected = input.parse::<Expr>()?;

        Ok(PassFailArgs {
            named,
            args,
            expected,
        })
    }
}

#[proc_macro_attribute]
pub fn pass(args: TokenStream, input: TokenStream) -> TokenStream {
    let PassFailArgs {
        named,
        args,
        expected,
    } = parse_macro_input!(args as PassFailArgs);
    let input = parse_macro_input!(input as ItemFn);

    let fn_ident = input.ident.clone();
    let test_name = named
        .map(|named| Ident::new(&named.value(), Span::call_site()))
        .unwrap_or_else(|| Ident::new(&format!("{}_test_pass", fn_ident), Span::call_site()));

    let args = quote! {
        #(#args,)*
    };

    TokenStream::from(quote! {
        #input

        #[test]
        fn #test_name() {
            assert_eq!(#fn_ident(#args), #expected);
        }
    })
}

#[proc_macro_attribute]
pub fn fail(args: TokenStream, input: TokenStream) -> TokenStream {
    let PassFailArgs {
        named,
        args,
        expected,
    } = parse_macro_input!(args as PassFailArgs);
    let input = parse_macro_input!(input as ItemFn);

    let fn_ident = input.ident.clone();
    let test_name = named
        .map(|named| Ident::new(&named.value(), Span::call_site()))
        .unwrap_or_else(|| Ident::new(&format!("{}_test_fail", fn_ident), Span::call_site()));

    let args = quote! {
        #(#args,)*
    };

    TokenStream::from(quote! {
        #input

        #[test]
        #[should_panic]
        fn #test_name() {
            assert_eq!(#fn_ident(#args), #expected);
        }
    })
}

struct MultiPassFailArgs {
    named: Option<syn::LitStr>,
    tests: Vec<PassFailArgs>,
}

impl Parse for MultiPassFailArgs {
    fn parse(input: ParseStream) -> Result<Self> {
        let named = if input.peek(Ident) && input.peek2(Token![=]) {
            let ident = input.parse::<Ident>()?;

            if &ident != "name" {
                panic!("You must enclose this expression in parenthesis.");
            }

            input.parse::<Token![=]>()?;

            let name = input.parse::<syn::LitStr>()?;

            input.parse::<Token![,]>()?;

            Some(name)
        } else {
            None
        };

        let tests = Punctuated::<PassFailArgs, Token![,]>::parse_terminated(&input)?
            .into_iter()
            .collect();

        Ok(MultiPassFailArgs { named, tests })
    }
}

#[proc_macro_attribute]
pub fn multi_pass(args: TokenStream, input: TokenStream) -> TokenStream {
    let MultiPassFailArgs { named, tests } = parse_macro_input!(args as MultiPassFailArgs);
    let input = parse_macro_input!(input as ItemFn);

    let fn_ident = input.ident.clone();
    let test_name = named
        .map(|named| Ident::new(&named.value(), Span::call_site()))
        .unwrap_or_else(|| Ident::new(&format!("{}_multitest_pass", fn_ident), Span::call_site()));

    let args = tests.iter().map(|PassFailArgs { args, .. }| {
        quote! {
            #(#args,)*
        }
    });

    let expecteds = tests.iter().map(|PassFailArgs { expected, .. }| {
        quote!{
            #expected
        }
    });

    let fn_ident = &[fn_ident];

    TokenStream::from(quote! {
        #input

        #[test]
        fn #test_name() {
            #(
                assert_eq!(#fn_ident(#args), #expecteds);
            )*
        }
    })
}

#[proc_macro_attribute]
pub fn multi_fail(args: TokenStream, input: TokenStream) -> TokenStream {
    let MultiPassFailArgs { named, tests } = parse_macro_input!(args as MultiPassFailArgs);
    let input = parse_macro_input!(input as ItemFn);

    let fn_ident = input.ident.clone();
    let test_name = named
        .map(|named| Ident::new(&named.value(), Span::call_site()))
        .unwrap_or_else(|| Ident::new(&format!("{}_multitest_fail", fn_ident), Span::call_site()));

    let args = tests.iter().map(|PassFailArgs { args, .. }| {
        quote! {
            #(#args,)*
        }
    });

    let expecteds = tests.iter().map(|PassFailArgs { expected, .. }| {
        quote!{
            #expected
        }
    });

    let fn_ident = &[fn_ident];

    TokenStream::from(quote! {
        #input

        #[test]
        #[should_panic]
        fn #test_name() {
            #(
                assert_eq!(#fn_ident(#args), #expecteds);
            )*
        }
    })
}

/// Generates a test function that `assert_eq!`s the before and after
/// expressions given.
#[proc_macro_attribute]
pub fn fn_test(args: TokenStream, input: TokenStream) -> TokenStream {
    let input_fn = parse_macro_input!(input as ItemFn);
    let Args {
        name,
        input: input_expr,
        expected,
        _should_fails,
    } = parse_macro_input!(args as Args);

    let test_fn = name
        .map(|s| Ident::new(&s.value(), Span::call_site()))
        .unwrap_or_else(|| {
            Ident::new(
                &format!("{}_generated_test", input_fn.ident),
                Span::call_site(),
            )
        });

    let fn_ident = input_fn.ident.clone();

    match (&input_expr, &expected) {
        (Either::Left(e1), Either::Left(e2)) => TokenStream::from(quote! {
            #input_fn
            #[test]
            fn #test_fn() {
                assert_eq!( crate::#fn_ident(#e1), #e2);
            }
        }),
        (Either::Right(e1), Either::Right(e2)) if e1.len() == e2.len() => {
            let fn_ident = &[fn_ident][..];

            TokenStream::from(quote! {
                #input_fn
                #[test]
                fn #test_fn() {
                    #(
                        assert_eq!( crate::#fn_ident(#e1), #e2);
                    )*
                }
            })
        }
        _ => panic!("wtf u doin"),
    }
}
