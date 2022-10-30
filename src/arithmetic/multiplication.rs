//!
//! Multiplication algorithms for BigDigits
//!

use crate::bigdigit::{
    BigDigit, BigDigitOverflow, BigDigitVec, BigDigitBase, BigDigitBaseDouble, BIG_DIGIT_RADIX
};


impl std::ops::Mul<BigDigit> for &BigDigit {
    type Output = (BigDigit, BigDigitOverflow);
    // return overflow
    fn mul(self, rhs: BigDigit) -> (BigDigit, BigDigitOverflow)
    {
        (rhs, rhs)
    }
}


/// Create BigDigitVec from product of big digit slices
pub(crate) fn multiply_digit_slices(a: &[BigDigit], b: &[BigDigit]) -> BigDigitVec {
    let mut result = BigDigitVec::with_capacity(a.len() + b.len() + 1);
    multiply_digit_slices_into(a, b, &mut result);
    return result;
}

/// Multiply digits in a and b into result
#[inline]
pub(crate) fn multiply_digit_slices_into(a: &[BigDigit], b: &[BigDigit], result: &mut BigDigitVec) {
    result.clear();
    result.resize(a.len() + b.len() + 1, 0u8.into());
    for (ia, digit_a) in a.iter().enumerate() {
        if digit_a.is_zero() {
            continue;
        }

        for (ib, digit_b) in b.iter().enumerate() {
            if digit_b.is_zero() {
                continue;
            }

            let mut idx = ia + ib;

            // calculate p_(i+j) += a_i * b_j, returning carry
            let mut carry = digit_a.fused_multiply_add_into(digit_b, &mut result[idx]);

            // apply the carry
            while carry != 0 {
                idx += 1;
                result[idx].add_assign_carry(&mut carry);
            }
        }
    }

    // remove leading zeros
    result.truncate_zeros();
}



#[cfg(test)]
#[allow(overflowing_literals)]
#[allow(unreachable_patterns)]
mod test_multiply_digit_vecs {
    use super::*;

    include!("../test_macros.rs");

    macro_rules! impl_test {
        () => {
            |a, b, expected: &[BigDigit]| {
                let sum = multiply_digit_slices(a, b);
                assert_eq!(sum.as_ref(), expected);

                // let commutes = multiply_digit_slices(b, a);
                // assert_eq!(commutes.as_ref(), expected);
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
    fn test_0_1() {
        impl_test!([0] [1] == [0]);
    }

    #[test]
    fn test_5_3() {
        impl_test!([5] [3] == [15]);
    }

    #[test]
    fn test_5_5() {
        impl_test!([5] [5] == [25]);
    }

    #[test]
    fn test_7_22() {
        impl_test_for_radix! {
            100 => [7] [22] == [54, 1],
            _ => [7] [22] == [154]
        }
    }

    #[test]
    fn test_7_22_truncates() {
        impl_test_for_radix! {
            100 => [7, 0] [22, 0] == [54, 1],
            _ => [7, 0] [22, 0] == [154]
        }
    }

    #[test]
    fn test_254_791() {
        impl_test_for_radix! {
          100   => [54, 2] [91, 7] == [14, 9, 20],
          256   => [254] [23, 3] == [210, 16, 3],
          10000 => [254] [791] == [914, 20],
          65536 => [254] [791] == [4306, 3],
          _     => [254] [791] == [200914]
        }
    }

    #[test]
    fn test_209504545595_605739580991() {
        impl_test_for_radix! {
          _ => { unimplemented!() },
          100        => [95, 55, 54, 4, 95, 20] [91, 9, 58, 39, 57, 60] == [45, 46, 78, 54, 51, 42, 64, 56, 19, 5, 69, 12],
          256        => [59, 171, 113, 199, 48] [63, 126, 228, 8, 141] == [133, 45, 204, 95, 64, 140, 96, 139, 223, 26],
          10000      => [5595, 454, 2095] [991, 3958, 6057] == [4645, 5478, 4251, 5664, 519, 1269],
          65536      => [43835, 51057, 48] [32319, 2276, 141] == [11653, 24524, 35904, 35680, 6879],
          1000000000 => [504545595, 209] [739580991, 605] == [154784645, 195664425, 126905],
          4294967297 => [3346115387, 48] [149192255, 141] == [1607216517, 2338360384, 6879],
        }
    }

    #[test]
    fn test_88230592051047800480860_3048679567898514200436785806() {
        impl_test_for_radix! {
          _ => { unimplemented!() },
          1000000000 => [800480860, 592051047, 88230] [436785806, 898514200, 48679567, 3] == [622673160, 644889559, 100461313, 490137102, 803249618, 268986],
        }
    }

    #[test]
    fn test_19455391702599000000000096374177_89171318485483000000000() {
        impl_test_for_radix! {
          _ => { unimplemented!() },
          1000000000 => [096374177, 0, 391702599, 19455] [0, 318485483, 89171] == [0, 310572491, 812431043, 434878910, 772278785, 734862929, 1],
        }
    }
}
