//! Algorithms for manipulating decimal digits
//!

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
