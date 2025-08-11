//! Algorithms for manipulating decimal digits
//!

/// Return number of decimal digits in biginteger
pub(crate) fn count_digits_bigint(n: &num_bigint::BigInt) -> u64 {
    count_digits_biguint(n.magnitude())
}

/// Return number of significant decimal digits in unsigned big-integer
pub(crate) fn count_digits_biguint(n: &num_bigint::BigUint) -> u64 {
    let mut digits = (n.bits() as f64 / super::LOG2_10) as u64;
    // guess number of digits based on number of bits in UInt
    let mut num = super::ten_to_the_uint(digits);
    while n >= &num {
        num *= 10u8;
        digits += 1;
    }
    digits
}
