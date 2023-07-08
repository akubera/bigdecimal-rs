//! Algorithms for manipulating decimal digits
//!
//! Note: Many bit-optimizations don't apply when doing decimal
//!       math, as high-order bits affect low-order decimals
//!
#![allow(dead_code)]

/// Lookup table used to divide u32 by a power of ten, using
/// a multiply and a shift-right
///
/// Presumably faster than div?
///
static DEC_SHIFT_RIGHT_U32_MAGIC_NUMBERS: [(u64, usize); 10] = [
    (1, 0),
    (3435973837, 35),
    (1374389535, 37),
    (274877907, 38),
    (3518437209, 45),
    (5629499535, 49),
    (1125899907, 50),
    (1801439851, 54),
    (1441151881, 57),
    (4611686019, 62),
];

/// Shift u32 right by *n* decimal digits (panics if *n* is greater than 9)
///
///
/// ```
/// assert_eq!(dec_shift_right_u32(12345, 0), 12345);
/// assert_eq!(dec_shift_right_u32(12345, 2), 123);
/// assert_eq!(dec_shift_right_u32(12345, 6), 0);
/// ```
///
pub fn dec_shift_right_u32_unchecked(x: u32, n: usize) -> u32 {
    debug_assert!(n < DEC_SHIFT_RIGHT_U32_MAGIC_NUMBERS.len());

    let (a, b) = DEC_SHIFT_RIGHT_U32_MAGIC_NUMBERS[n];
    let y = x as u64 * a;
    let result = (y >> b) as u32;
    debug_assert_eq!(result, x / 10u32.pow(n as u32));
    result
}

/// Shift u32 right by n decimal digit
///
/// ```
/// assert_eq!(dec_shift_right_u32(12345, 0), 12345);
/// assert_eq!(dec_shift_right_u32(12345, 2), 123);
/// assert_eq!(dec_shift_right_u32(12345, 6), 0);
/// ```
///
pub fn dec_shift_right_u32(x: u32, n: usize) -> u32 {
    debug_assert!(n < DEC_SHIFT_RIGHT_U32_MAGIC_NUMBERS.len());

    let (a, b) = match DEC_SHIFT_RIGHT_U32_MAGIC_NUMBERS.get(n) {
        None => { return 0; }
        Some(pair) => pair,
    };
    let y = x as u64 * a;
    let result = (y >> b) as u32;
    debug_assert_eq!(result, x / 10u32.pow(n as u32));
    result
}

/// Lookup table used to divide u64 by a power of ten, using
/// a multiply and a shift-right
static DEC_SHIFT_RIGHT_U64_MAGIC_NUMBERS: [(u128, usize); 20] = [
    (1, 0),
    (14757395258967641293, 67),
    (23611832414348226069, 71),
    (18889465931478580855, 74),
    (3777893186295716171, 75),
    (24178516392292583495, 81),
    (4835703278458516699, 82),
    (15474250491067253437, 87),
    (12379400392853802749, 90),
    (19807040628566084399, 94),
    (15845632502852867519, 97),
    (12676506002282294015, 100),
    (2535301200456458803, 101),
    (4056481920730334085, 105),
    (811296384146066817, 106),
    (20769187434139310515, 114),
    (4153837486827862103, 115),
    (26584559915698317459, 121),
    (21267647932558653967, 124),
    (8507059173023461587, 126),
];

/// Shift u64 right by *n* decimal digits (panics if *n* is greater than 19)
pub fn dec_shift_right_u64_unchecked(x: u64, n: usize) -> u64 {
    debug_assert!(n < DEC_SHIFT_RIGHT_U64_MAGIC_NUMBERS.len());

    let (a, b) = DEC_SHIFT_RIGHT_U64_MAGIC_NUMBERS[n];
    let y = x as u128 * a;
    let result = (y >> b) as u64;
    debug_assert_eq!(result, x / 10u64.pow(n as u32));
    result
}

/// Shift u64 right by *n* decimal digits
pub fn dec_shift_right_u64(x: u64, n: usize) -> u64 {
    debug_assert!(n < DEC_SHIFT_RIGHT_U64_MAGIC_NUMBERS.len());

    let (a, b) = match DEC_SHIFT_RIGHT_U64_MAGIC_NUMBERS.get(n) {
        None => { return 0; }
        Some(pair) => pair,
    };
    let y = x as u128 * a;
    let result = (y >> b) as u64;
    debug_assert_eq!(result, x / 10u64.pow(n as u32));
    result
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
    if (n >> 32) == 0 {
       count_digits_u32(n as u32)
    } else {
       count_digits!(n:u64)
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
    debug_assert!(&(n * 10u8) >= &num);

    while n >= &num {
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
