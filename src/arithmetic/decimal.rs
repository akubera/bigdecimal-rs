//! Algorithms for manipulating decimal digits
//!
//! Note: Many bit-optimizations don't apply when doing decimal
//!       math, as high-order bits affect low-order decimals
//!
#![allow(dead_code)]


/// Shift u32 right by *n* decimal digits
pub fn dec_shift_right_u32(x: u32, n: usize) -> u32 {
    match n {
        0 => x,
        1 => x / 10,
        2 => x / 100,
        3 => x / 1000,
        4 => x / 10_000,
        5 => x / 100_000,
        6 => x / 1000_000,
        7 => x / 10_000_000,
        8 => x / 100_000_000,
        9 => x / 1000_000_000,
        _ => 0,
    }
}


/// Shift u64 right by *n* decimal digits
pub fn dec_shift_right_u64(x: u64, n: usize) -> u64 {
    match n {
        0 => x,
        1 => x / 10,
        2 => x / 100,
        3 => x / 1000,
        4 => x / 10_000,
        5 => x / 100_000,
        6 => x / 1000_000,
        7 => x / 10_000_000,
        8 => x / 100_000_000,
        9 => x / 1000_000_000,
        10 => x / 10_000_000_000,
        11 => x / 100_000_000_000,
        12 => x / 1000_000_000_000,
        13 => x / 10_000_000_000_000,
        14 => x / 100_000_000_000_000,
        15 => x / 1000_000_000_000_000,
        16 => x / 10_000_000_000_000_000,
        17 => x / 100_000_000_000_000_000,
        18 => x / 1000_000_000_000_000_000,
        19 => x / 10_000_000_000_000_000_000,
        _ => 0,
    }
}


#[cfg(test)]
mod test {
    use super::*;
    include!("decimal.tests.rs");
}
