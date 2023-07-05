# bigdecimal-rs


[![crate](https://img.shields.io/crates/v/bigdecimal.svg)](https://crates.io/crates/bigdecimal)
[![Documentation](https://docs.rs/bigdecimal/badge.svg)](https://docs.rs/bigdecimal)

[![minimum rustc 1.43](https://img.shields.io/badge/rustc-1.43+-red.svg)](https://rust-lang.github.io/rfcs/2495-min-rust-version.html)

[![codecov](https://codecov.io/gh/akubera/bigdecimal-rs/branch/feature/circleci/graph/badge.svg?token=YTwyxrxJ3S)](https://codecov.io/gh/akubera/bigdecimal-rs)
[![build status - master](https://gitlab.com/akubera/bigdecimal-rs/badges/master/pipeline.svg?ignore_skipped=true&key_text=status:master&key_width=96)](https://gitlab.com/akubera/bigdecimal-rs/-/pipelines)
[![build status - trunk](https://gitlab.com/akubera/bigdecimal-rs/badges/trunk/pipeline.svg?ignore_skipped=true&key_text=status:trunk&key_width=96)](https://gitlab.com/akubera/bigdecimal-rs/-/pipelines)



Arbitary-precision decimal numbers implemented in pure Rust.

## Usage

Add bigdecimal as a dependency to your `Cargo.toml` file:

```toml
[dependencies]
bigdecimal = "0.4"
```

Import and use the `BigDecimal` struct to solve your problems:

```rust
use bigdecimal::BigDecimal;

fn main() {
    let two = BigDecimal::from(2);
    println!("sqrt(2) = {}", two.sqrt().unwrap());
}
```

this code will print

```
sqrt(2) = 1.414213562373095048801688724209698078569671875376948073176679737990732478462107038850387534327641573
```


#### Default precision

Default precision may be set at compile time with the environment variable `RUST_BIGDECIMAL_DEFAULT_PRECISION`.
The default value of this variable is 100.

This will be used as maximum precision for operations which may produce infinite digits (inverse, sqrt, ...).

Note that other operations, such as multiplication, will preserve all digits, so multiplying two 70 digit numbers
will result in one 140 digit number.
The user will have to manually trim the number of digits after calculations to reasonable amounts using the
`x.with_prec(30)` method.

A new set of methods with explicit precision and rounding modes is being worked on, but even after those
are introduced the default precision will have to be used as the implicit value.

## Improvements

Work is being done on this codebase again and there are many features
and improvements on the way.


## About

This repository contains code originally meant for a bigdecimal module
in the popular [num](https://crates.io/crates/num) crate, but was not
merged due to uncertainty of what the best design for such a crate
should be.


## License

This code is dual-licensed under the permissive
[MIT](https://opensource.org/licenses/MIT) &
[Apache 2.0](https://opensource.org/licenses/Apache-2.0) licenses.

###  Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the
Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.


##  Community

Join the conversation on Zulip: https://bigdecimal-rs.zulipchat.com
