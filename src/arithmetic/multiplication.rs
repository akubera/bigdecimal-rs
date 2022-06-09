use crate::bigdigit::{BigDigitBase, BigDigitBaseDouble, BIG_DIGIT_RADIX};

fn multiply_digits_by_ten(v: &mut Vec<BigDigitBaseDouble>) {
    multiply_digits_by_n(v, 10);
}

fn multiply_digits_by_n(v: &mut Vec<BigDigitBaseDouble>, n: BigDigitBase) {
    multiply_digits_by_n_with_skip(v, n, 0);
}

#[inline]
pub(crate) fn multiply_digit_vecs_into(a: &[BigDigitBase], b: &[BigDigitBase], result: &mut Vec<BigDigitBase>) {
    // let product = multiply_digit_vecs(a, b);
    result.clear();
    result.resize(a.len() + b.len() + 1, 0);
    for (ia, &digit_a) in a.iter().enumerate() {
        if digit_a == 0 {
            continue;
        }

        for (ib, &digit_b) in b.iter().enumerate() {
            if digit_b == 0 {
                continue;
            }
            let mut idx = ia + ib;

            let prod = digit_a as BigDigitBaseDouble * digit_b as BigDigitBaseDouble;

            let tmp = prod % BIG_DIGIT_RADIX + result[idx] as BigDigitBaseDouble;
            result[idx] = (tmp % BIG_DIGIT_RADIX) as BigDigitBase;

            let mut carry = prod / BIG_DIGIT_RADIX + tmp / BIG_DIGIT_RADIX;

            while carry != 0 {
                idx += 1;
                let tmp = carry + result[idx] as BigDigitBaseDouble;
                result[idx] = (tmp % BIG_DIGIT_RADIX) as BigDigitBase;
                carry = carry / BIG_DIGIT_RADIX + tmp / BIG_DIGIT_RADIX;
            }
        }
    }

    let nonzero_index = result.iter().rposition(|&d| d != 0).unwrap_or(0);
    result.truncate(nonzero_index + 1);
}

fn multiply_digits_by_n_with_skip(v: &mut Vec<BigDigitBaseDouble>, n: BigDigitBase, s: usize) {
    let mut carry = 0;
    for d in v.iter_mut().skip(s) {
        let tmp = *d * n as BigDigitBaseDouble + carry;
        *d = tmp % BIG_DIGIT_RADIX;
        carry = tmp / BIG_DIGIT_RADIX;
    }

    while carry != 0 {
        v.push(carry % BIG_DIGIT_RADIX);
        carry /= BIG_DIGIT_RADIX;
    }
}

pub(crate) fn multiply_digit_vecs(a: &[BigDigitBase], b: &[BigDigitBase]) -> Vec<BigDigitBase> {
    // let mut result = vec![0; a.len() + b.len() + 1];
    let mut result = Vec::with_capacity(a.len() + b.len() + 1);
    multiply_digit_vecs_into(a, b, &mut result);
    return result;
}

#[cfg(test)]
#[allow(overflowing_literals)]
#[allow(unreachable_patterns)]
mod test_multiply_digit_vecs {
    use super::*;

    macro_rules! impl_test_for_radix {
    ( $($rad:pat => [$($a:literal),*] [$($b:literal),*] == [$($c:literal),*]),* ) => {{
      let do_test = |a, b, expected: &[BigDigitBase]| {
        let v = multiply_digit_vecs(a, b);
        assert_eq!(&v, &expected);

        let commutes = multiply_digit_vecs(b, a);
        assert_eq!(&commutes, &expected);
      };

      match BIG_DIGIT_RADIX {
        $( $rad => do_test(&[$($a,)*], &[$($b,)*], &[$($c,)*]), )*
      };
    }};
    ( _ => $all:block, $($rad:pat => [$($a:literal),*] [$($b:literal),*] == [$($c:literal),*]),* ) => {{
      let do_test = |a, b, expected: &[BigDigitBase]| {
        let v = multiply_digit_vecs(a, b);
        assert_eq!(&v, &expected);

        let commutes = multiply_digit_vecs(b, a);
        assert_eq!(&commutes, &expected);
      };

      match BIG_DIGIT_RADIX {
        $( $rad => do_test(&[$($a,)*], &[$($b,)*], &[$($c,)*]), )*
        _ => $all
      };
    }}
    }

    #[test]
    fn test_0_0() {
        let v = multiply_digit_vecs(&[0], &[0]);
        assert_eq!(v, &[0]);
    }

    #[test]
    fn test_5_5() {
        let v = multiply_digit_vecs(&[5], &[5]);
        assert_eq!(v, &[25]);
    }

    #[test]
    fn test_7_22() {
        let v = multiply_digit_vecs(&[7], &[22]);
        match BIG_DIGIT_RADIX {
            100 => assert_eq!(v, &[54, 1]),
            _ => assert_eq!(v, &[154]),
        }
    }

    #[test]
    fn test_7_22_truncates() {
        let v = multiply_digit_vecs(&[7, 0], &[22, 0, 0]);
        match BIG_DIGIT_RADIX {
            100 => assert_eq!(v, &[54, 1]),
            _ => assert_eq!(v, &[154]),
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
          4294967296 => [3346115387, 48] [149192255, 141] == [1607216517, 2338360384, 6879]
        }
    }
}
