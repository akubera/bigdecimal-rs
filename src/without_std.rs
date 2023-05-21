use core::{
    cmp,
    convert,
    default,
    fmt,
    hash,
    mem,
    num,
    ops,
    iter,
    str,
    i8,
    f32,
    f64,
};

#[cfg(test)]
extern crate siphasher;

#[cfg(test)]
use siphasher::sip::SipHasher as DefaultHasher;

// Without this import we get the following error:
// error[E0599]: no method named `powi` found for type `f64` in the current scope
#[allow(unused_imports)]
use num_traits::float::FloatCore;

#[allow(unused_imports)]
#[macro_use]
extern crate alloc;

use alloc::string;
