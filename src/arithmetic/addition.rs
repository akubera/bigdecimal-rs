use crate::bigdigit::{BigDigitBase, BigDigitBaseDouble, BIG_DIGIT_RADIX};

macro_rules! add_digit_vecs_impl {
    ($a:ident + $b:ident => $sum:ident ; $radix:expr, $digit_type:ty, $double_digit_type:ty ) => {{
        $sum.clear();
        if $sum.capacity() < $a.len() + 1 {
            $sum.reserve($a.len() + 1 - $sum.capacity());
        }
        let mut a_iter = $a.iter();

        let mut carry = 0;
        for b_digit in $b.iter() {
            let a_digit = a_iter.next().unwrap();
            let x = *a_digit as $double_digit_type;
            let y = *b_digit as $double_digit_type;

            let sum = x + y + carry;
            $sum.push((sum % $radix) as $digit_type);
            carry = sum / $radix;
        }

        for a_digit in a_iter {
            let sum = carry + *a_digit as $double_digit_type;
            $sum.push((sum % $radix) as $digit_type);
            carry = sum / $radix;
        }

        if carry != 0 {
            $sum.push(carry as $digit_type);
        }
    }};
}

#[inline]
pub(crate) fn add_digit_vecs(a: &[BigDigitBase], b: &[BigDigitBase]) -> Vec<BigDigitBase> {
    let mut result = Vec::with_capacity(a.len().max(b.len() + 1));
    add_digit_vecs_into(a, b, &mut result);
    return result;
}

#[inline]
pub(crate) fn add_digit_vecs_into(a: &[BigDigitBase], b: &[BigDigitBase], v: &mut Vec<BigDigitBase>) {
    // a is longer of the vectors
    let (a, b) = if a.len() >= b.len() { (a, b) } else { (b, a) };

    add_digit_vecs_impl!(a + b => v; BIG_DIGIT_RADIX, BigDigitBase, BigDigitBaseDouble)
}

#[cfg(test)]
#[allow(overflowing_literals)]
#[allow(unreachable_patterns)]
mod test_add_digit_vecs {
    use super::*;

    macro_rules! impl_test_for_radix {
        ( $($rad:pat => [$($a:literal),*] [$($b:literal),*] == [$($c:literal),*]),* $(,)?) => {{
            let do_test = |a, b, expected: &[BigDigitBase]| {
                let v = add_digit_vecs(a, b);
                assert_eq!(&v, &expected);

                let commutes = add_digit_vecs(b, a);
                assert_eq!(&commutes, &expected);
            };

            match BIG_DIGIT_RADIX {
                $( $rad => do_test(&[$($a,)*], &[$($b,)*], &[$($c,)*]), )*
            };
        }};
        ( _ => $all:block, $($rad:pat => [$($a:literal),*] [$($b:literal),*] == [$($c:literal),*]),* $(,)?) => {{
            let do_test = |a, b, expected: &[BigDigitBase]| {
                let v = add_digit_vecs(a, b);
                assert_eq!(&v, &expected);

                let commutes = add_digit_vecs(b, a);
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
        let v = add_digit_vecs(&[0], &[0]);
        assert_eq!(&v, &[0]);
    }

    #[test]
    fn test_10_1() {
        impl_test_for_radix!(
            _ => [10] [1] == [11],
        );
    }

    #[test]
    fn test_25010755222_639426798457883776() {
        impl_test_for_radix!(
            _ => { unimplemented!() },
            10000    => [5222, 1075, 250] [3776, 5788, 7984, 9426, 63] == [8998, 6863, 8234, 9426, 63],
            10000000 => [755222, 2501] [7883776, 2679845, 6394] == [8638998, 2682346, 6394],
            1000000000 => [10755222, 25] [457883776, 639426798] == [468638998, 639426823],
        );
    }
}
