//!
//! Addition algorithms BigDigit
//!

use crate::bigdigit::{BigDigit, BigDigitVec};

/// Add two (aligned) slices of BigDigits
#[inline]
pub(crate) fn add_digit_slices(a: &[BigDigit], b: &[BigDigit]) -> BigDigitVec {
    let mut result = BigDigitVec::with_capacity(a.len().max(b.len() + 1));
    add_digit_slices_into(a, b, &mut result);
    return result;
}

/// Add aligned digits into result vector
#[inline]
pub(crate) fn add_digit_slices_into(a: &[BigDigit], b: &[BigDigit], v: &mut BigDigitVec) {
    // a is longer of the vectors
    let (a, b) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    v.clear_and_reserve(a.len() + 1);

    let mut a_digits = a.iter();
    let mut carry = BigDigit::zero();
    for b_digit in b.iter() {
        let a_digit = a_digits.next().unwrap();
        let sum = a_digit.add_with_carry(b_digit, &mut carry);
        v.push(sum);
    }

    while !carry.is_zero() {
        match a_digits.next() {
            Some(digit) => {
                v.push(digit.add_carry(&mut carry));
            }
            None => {
                // carry is not zero and a_digits has ended
                // so we push final carry and stop addition
                v.push(carry);
                return;
            }
        }
    }

    // at this point carry is zero so we just copy remaining
    for &a_digit in a_digits {
        v.push(a_digit);
    }
}

#[cfg(test)]
#[allow(overflowing_literals)]
#[allow(unreachable_patterns)]
mod test_add_digit_slices {
    use super::*;
    use crate::bigdigit::BIG_DIGIT_RADIX;

    include!("../test_macros.rs");

    macro_rules! impl_test {
        () => {
            |a, b, expected: &[BigDigit]| {
                let sum = add_digit_slices(a, b);
                assert_eq!(sum.as_ref(), expected);

                let commutes = add_digit_slices(b, a);
                assert_eq!(commutes.as_ref(), expected);
            }
        };
        ([$($a:literal),*] [$($b:literal),*] == [$($c:literal),*]) => {
            let do_test = impl_test!();
            call_func!(do_test, [$($a),*] [$($b),*] [$($c),*]);
        };
    }

    #[test]
    fn test_0_0() {
        impl_test!([0] [0] == [0]);
    }

    #[test]
    fn test_10_1() {
        impl_test!([10] [1] == [11]);
    }

    #[test]
    fn test_1_999999998() {
        impl_test_for_radix! {
            _ => { unimplemented!() },
            100 => [1] [98, 99, 99, 99, 9] == [99, 99, 99, 99, 9],
            1000000000 => [1] [999999998] == [999999999],
        };
    }

    #[test]
    fn test_1_999999999() {
        impl_test_for_radix! {
            _ => { unimplemented!() },
            100 => [1] [99, 99, 99, 99, 9] == [0, 0, 0, 0, 10],
            1000000000 => [1] [999999999] == [0, 1],
        };
    }

    #[test]
    fn test_5001_999999999() {
        impl_test_for_radix! {
            _ => { unimplemented!() },
            1000000000 => [5001] [999999999] == [5000, 1],
        };
    }

    #[test]
    fn test_25010755222_639426798457883776() {
        impl_test_for_radix! {
            _ => { unimplemented!() },
            1000       => [222, 755, 10, 25] [776, 883, 457, 798, 426, 639] == [998, 638, 468, 823, 426, 639],
            10000      => [5222, 1075, 250]  [3776, 5788, 7984, 9426, 63] == [8998, 6863, 8234, 9426, 63],
            10000000   => [755222, 2501]     [7883776, 2679845, 6394] == [8638998, 2682346, 6394],
            1000000000 => [010755222, 25]    [457883776, 639426798] == [468638998, 639426823],
        };
    }
}
