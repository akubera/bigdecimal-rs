# bigdecimal-rs


[![crate](https://img.shields.io/crates/v/bigdecimal.svg)](https://crates.io/crates/bigdecimal)
[![Documentation](https://docs.rs/bigdecimal/badge.svg)](https://docs.rs/bigdecimal)

[![minimum rustc 1.34](https://img.shields.io/badge/rustc-1.34+-red.svg)](https://rust-lang.github.io/rfcs/2495-min-rust-version.html)

[![coverage](https://gitlab.com/akubera/bigdecimal-rs/badges/master/coverage.svg)](https://gitlab.com/akubera/bigdecimal-rs/-/pipelines)
[![build status - master](https://gitlab.com/akubera/bigdecimal-rs/badges/master/pipeline.svg?ignore_skipped=true)](https://gitlab.com/akubera/bigdecimal-rs/-/pipelines)
[![build status - dev](https://gitlab.com/akubera/bigdecimal-rs/badges/devel/pipeline.svg?ignore_skipped=true)](https://gitlab.com/akubera/bigdecimal-rs/-/pipelines)


Arbitary-precision decimal numbers implemented in pure Rust.

## Usage

Add bigdecimal as a dependency to your `Cargo.toml` file:

```toml
[dependencies]
bigdecimal = "0.3"
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
