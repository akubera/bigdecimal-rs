//! arithmetic routines

use crate::*;

pub(crate) mod addition;
pub(crate) mod sqrt;
pub(crate) mod cbrt;
pub(crate) mod inverse;

/// Return 10^pow
///
/// Try to calculate this with fewest number of allocations
///
pub(crate) fn ten_to_the(pow: u64) -> BigInt {
    ten_to_the_uint(pow).into()
}

/// Return 10^{pow} as u64
pub(crate) fn ten_to_the_u64(pow: u8) -> u64 {
    debug_assert!(pow < 20);
    10u64.pow(pow as u32)
}

/// Return 10^pow
pub(crate) fn ten_to_the_uint(pow: u64) -> BigUint {
    if pow < 20 {
        return BigUint::from(10u64.pow(pow as u32));
    }

    // linear case of 10^pow = 10^(19 * count + rem)
    if pow < 590 {
        let ten_to_nineteen = 10u64.pow(19);

        // count factors of 19
        let (count, rem) = pow.div_rem(&19);

        let mut res = BigUint::from(ten_to_nineteen);
        for _ in 1..count {
            res *= ten_to_nineteen;
        }
        if rem != 0 {
            res *= 10u64.pow(rem as u32);
        }

        return res;
    }

    // use recursive algorithm where linear case might be too slow
    let (quotient, rem) = pow.div_rem(&16);
    let x = ten_to_the_uint(quotient);

    let x2 = &x * &x;
    let x4 = &x2 * &x2;
    let x8 = &x4 * &x4;
    let res = &x8 * &x8;

    if rem == 0 {
        res
    } else {
        res * 10u64.pow(rem as u32)
    }
}


/// Return number of decimal digits in integer
pub(crate) fn count_decimal_digits(int: &BigInt) -> u64 {
    count_decimal_digits_uint(int.magnitude())
}

/// Return number of decimal digits in unsigned integer
pub(crate) fn count_decimal_digits_uint(uint: &BigUint) -> u64 {
    if uint.is_zero() {
        return 1;
    }
    let mut digits = (uint.bits() as f64 / LOG2_10) as u64;
    // guess number of digits based on number of bits in UInt
    let mut num = ten_to_the(digits).to_biguint().expect("Ten to power is negative");
    while *uint >= num {
        num *= 10u8;
        digits += 1;
    }
    digits
}


/// Return difference of two numbers, returning diff as u64
pub(crate) fn diff<T>(a: T, b: T) -> (Ordering, u64)
where
    T: ToPrimitive + stdlib::ops::Sub<Output=T> + stdlib::cmp::Ord
{
    use stdlib::cmp::Ordering::*;

    match a.cmp(&b) {
        Less => (Less, (b - a).to_u64().unwrap()),
        Greater => (Greater, (a - b).to_u64().unwrap()),
        Equal => (Equal, 0),
    }
}

/// Return difference of two numbers, returning diff as usize
#[allow(dead_code)]
pub(crate) fn diff_usize(a: usize, b: usize) -> (Ordering, usize) {
    use stdlib::cmp::Ordering::*;

    match a.cmp(&b) {
        Less => (Less, b - a),
        Greater => (Greater, a - b),
        Equal => (Equal, 0),
    }
}
