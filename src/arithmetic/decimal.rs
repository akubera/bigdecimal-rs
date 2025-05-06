//! Algorithms for manipulating decimal digits
//!
//! Note: Many bit-optimizations don't apply when doing decimal
//!       math, as high-order bits affect low-order decimals
//!
#![allow(dead_code)]

use crate::*;


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


macro_rules! count_digits {
    ($n:ident : u64) => {
               if $n >= 10000000000000000000 {
            20
        } else if $n >= 1000000000000000000 {
            19
        } else if $n >= 100000000000000000 {
            18
        } else if $n >= 10000000000000000 {
            17
        } else if $n >= 1000000000000000 {
            16
        } else if $n >= 100000000000000 {
            15
        } else if $n >= 10000000000000 {
            14
        } else if $n >= 1000000000000 {
            13
        } else if $n >= 100000000000 {
            12
        } else if $n >= 10000000000 {
            11
        } else if $n >= 1000000000 {
            10
        } else {
            count_digits!($n:u32)
        }
    };
    ($n:ident : u32) => {
               if $n >= 1000000000 {
            10
        } else if $n >= 100000000 {
            9
        } else if $n >= 10000000 {
            8
        } else if $n >= 1000000 {
            7
        } else if $n >= 100000 {
            6
        } else {
            count_digits!($n:u16)
        }
    };
    ($n:ident : u16) => {
               if $n >= 100000 {
            6
        } else if $n >= 10000 {
            5
        } else if $n >= 1000 {
            4
        } else {
            count_digits!($n:u8)
        }
    };
    ($n:ident : u8) => {
               if $n >= 100 {
            3
        } else if $n >= 10 {
            2
        } else {
            1
        }
    };
}

/// Count digits in u32 (excluding leading-zeros)
pub(crate) fn count_digits_u32(n: u32) -> usize {
    count_digits!(n:u32)

}

/// Count digits in u64 (excluding leading-zeros)
pub(crate) fn count_digits_u64(n: u64) -> usize {
    count_digits!(n:u64)
}

/// Return number of decimal digits in integer
pub(crate) fn count_decimal_digits_bigint(int: &BigInt) -> u64 {
    count_decimal_digits_biguint(int.magnitude())
}

/// Return number of decimal digits in unsigned integer
pub(crate) fn count_decimal_digits_biguint(uint: &BigUint) -> u64 {
    if uint.is_zero() {
        return 1;
    }
    if uint.bits() <= 64 {
        return count_digits_u64(uint.iter_u64_digits().next().unwrap()) as _;
    }

    let mut digits = (uint.bits() as f64 / LOG2_10) as u64;
    // guess number of digits based on number of bits in UInt
    let mut num = ten_to_the_uint(digits);
    while *uint >= num {
        num *= 10u8;
        digits += 1;
    }
    digits
}



#[cfg(test)]
mod test {
    use super::*;
    include!("decimal.tests.rs");
}
