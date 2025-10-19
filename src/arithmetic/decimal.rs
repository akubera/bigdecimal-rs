//! Algorithms for manipulating decimal digits
//!
//! Note: Many bit-optimizations don't apply when doing decimal
//!       math, as high-order bits affect low-order decimals
//!


/// Shift u32 right by *n* decimal digits
#[allow(dead_code)]
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
#[allow(dead_code)]
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
    ($n:ident : u128) => {
               if $n >= 100000000000000000000000000000000000000 {
            39
        } else if $n >= 10000000000000000000000000000000000000 {
            38
        } else if $n >= 1000000000000000000000000000000000000 {
            37
        } else if $n >= 100000000000000000000000000000000000 {
            36
        } else if $n >= 10000000000000000000000000000000000 {
            35
        } else if $n >= 1000000000000000000000000000000000 {
            34
        } else if $n >= 100000000000000000000000000000000 {
            33
        } else if $n >= 10000000000000000000000000000000 {
            32
        } else if $n >= 1000000000000000000000000000000 {
            31
        } else if $n >= 100000000000000000000000000000 {
            30
        } else if $n >= 10000000000000000000000000000 {
            29
        } else if $n >= 1000000000000000000000000000 {
            28
        } else if $n >= 100000000000000000000000000 {
            27
        } else if $n >= 10000000000000000000000000 {
            26
        } else if $n >= 1000000000000000000000000 {
            25
        } else if $n >= 100000000000000000000000 {
            24
        } else if $n >= 10000000000000000000000 {
            23
        } else if $n >= 1000000000000000000000 {
            22
        } else if $n >= 100000000000000000000 {
            21
        } else {
            count_digits!($n:u64)
        }
    };
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
    if (n >> 32) == 0 {
       count_digits_u32(n as u32)
    } else {
       count_digits!(n:u64)
    }
}

/// Count digits in u128 (excluding leading-zeros)
pub(crate) fn count_digits_u128(n: u128) -> usize {
    if (n >> 64) == 0 {
       count_digits_u64(n as u64)
    } else {
       count_digits!(n:u128)
    }
}

/// Return number of decimal digits in biginteger
pub(crate) fn count_digits_bigint(n: &num_bigint::BigInt) -> u64 {
    count_digits_biguint(n.magnitude())
}

/// Return number of significant decimal digits in unsigned big-integer
pub(crate) fn count_digits_biguint(n: &num_bigint::BigUint) -> u64 {
    use num_traits::ToPrimitive;

    if let Some(n) = n.to_u64() {
        return count_digits_u64(n) as u64;
    }

    let mut digits = (n.bits() as f64 / super::LOG2_10) as u64;
    // guess number of digits based on number of bits in UInt
    let mut num = super::ten_to_the_uint(digits);
    debug_assert!(n * 10u8 >= num);

    while n >= &num {
        num *= 10u8;
        digits += 1;
    }
    digits
}

/// Return Some(exp) if n == 10^{exp}, otherwise None
pub(crate) fn get_power_of_ten_u64(n: u64) -> Option<u8> {
    match n {
        0 => Some(0),
        10 => Some(1),
        100 => Some(2),
        1000 => Some(3),
        10000 => Some(4),
        100000 => Some(5),
        1000000 => Some(6),
        10000000 => Some(7),
        100000000 => Some(8),
        1000000000 => Some(9),
        10000000000 => Some(10),
        n => {
            let (q, r) = num_integer::div_rem(n, 10000000000);
            if r == 0 {
                get_power_of_ten_u64(q).map(|p| p + 10)
            } else {
                None
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    include!("decimal.tests.rs");
}
