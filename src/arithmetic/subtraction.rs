use num_bigint::Sign;
use num_integer::div_rem;
use std::ops::Neg;
use std::iter;

use crate::{
    MAX_BIG_DIGIT_BASE_DOUBLE,
    bigdigit::{
        BIG_DIGIT_RADIX, BigDigitBase, BigDigitBaseSignedDouble, BigDigitVec, MAX_DIGITS_PER_BIGDIGIT,
        BigDigitBaseDouble,
    },
};

pub(crate) struct DigitInfo {
    pub digits: BigDigitVec,
    pub sign: Sign,
    pub scale: i64,
}

#[inline]
pub(crate) fn sub_digit_vecs(a: &[BigDigitBase], b: &[BigDigitBase]) -> Vec<BigDigitBase> {
    let mut result = Vec::with_capacity(a.len().max(b.len() + 1));
    sub_digit_vecs_into(a, b, &mut result);
    return result;
}

#[inline]
pub(crate) fn sub_digit_vecs_into(a: &[BigDigitBase], b: &[BigDigitBase], v: &mut Vec<BigDigitBase>) {
    // a is longer of the vectors
    let (a, b) = if a.len() >= b.len() { (a, b) } else { (b, a) };

    if a.len() == 1 && b.len() == 1 {
        v[0] = a[0] - b[0];
        return;
    }

    // add_digit_vecs_impl!(a + b => v; BIG_DIGIT_RADIX, BigDigitBase, BigDigitBaseDouble)
}

#[cfg(test)]
#[allow(overflowing_literals)]
#[allow(unreachable_patterns)]
mod test_sub_digit_vecs {
    use super::*;

    #[test]
    fn test_0_0() {
        let v = sub_digit_vecs(&[0], &[0]);
        assert_eq!(&v, &[0]);
    }

    #[test]
    fn test_10_0() {
        let v = sub_digit_vecs(&[10], &[0]);
        assert_eq!(&v, &[0]);
    }

    #[test]
    fn test_10_3() {
        let v = sub_digit_vecs(&[10], &[3]);
        assert_eq!(&v, &[7]);
    }
}

pub(crate) fn sub_small_int_digit_vec_into(a: i64, b: &DigitInfo, result: &mut DigitInfo) {
    use std::cmp::Ordering::{Equal, Less, Greater};

    debug_assert!(a.abs() < BIG_DIGIT_RADIX as i64);
    debug_assert!(b.digits.len() > 0);

    let DigitInfo { digits, scale, sign } = b;
    let sign = *sign;

    result.digits.clear();

    if *scale == 0 && digits.len() == 1 && a == digits[0] as i64 {
        result.sign = Sign::Plus;
        result.digits.push(0);
        result.scale = 0;
        return;
    }

    dbg!(a.cmp(&0), sign, *scale);
    match (a.cmp(&0), sign, *scale) {
        (_, Sign::NoSign, _) => {
            debug_assert!(digits.iter().all(|&d| d == 0));
            result.scale = 0;
            if a < 0 {
                result.sign = Sign::Minus;
                result.digits.push((-a) as BigDigitBase);
            } else {
                result.sign = Sign::Plus;
                result.digits.push(a as BigDigitBase);
            }
        }
        (Equal, _, scale) => {
            result.digits.extend_from_slice(&digits);
            result.sign = sign.neg();
            result.scale = scale;
            return;
        }
        (Less, Sign::Plus, 0) | (Greater, Sign::Minus, 0) => {
            let (hi, lo) = div_rem(digits[0] as i64 + a.abs(), BIG_DIGIT_RADIX as i64);
            result.digits.push(lo as BigDigitBase);

            let mut carry = hi as BigDigitBase;
            let mut i = 1;
            while carry > 0 {
                if i == digits.len() {
                    result.digits.push(carry);
                    break;
                }
                let (hi, lo) = div_rem(digits[i] + carry, BIG_DIGIT_RADIX as BigDigitBase);
                result.digits.push(lo);
                carry = hi;
                i += 1;
            }
            if i < digits.len() {
                result.digits.extend_from_slice(&digits[i..]);
            }
            result.sign = sign.neg();
            result.scale = 0;
        }
        (Greater, Sign::Plus, 0) => {
            result.sign = Sign::Minus;
            result.scale = 0;

            let diff = a - digits[0] as BigDigitBaseSignedDouble;
            dbg!(a, digits[0], diff);
            if diff <= 0 {
                result.digits.push((-diff) as BigDigitBase);
                result.digits.extend_from_slice(&digits[1..]);
                dbg!(&result.digits);
            } else if digits.len() > 1 {
                result
                    .digits
                    .push((BIG_DIGIT_RADIX as BigDigitBaseSignedDouble - diff) as BigDigitBase);
                dbg!(&result.digits);
                let mut i = 1;
                while digits[i] == 0 {
                    result.digits.push((BIG_DIGIT_RADIX - 1) as BigDigitBase);
                    i += 1;
                }
                result.digits.push(digits[i] - 1);
                result.digits.extend_from_slice(&digits[i + 1..]);
            } else {
                result.sign = Sign::Plus;
                result.digits.push(diff as BigDigitBase);
            }
        }
        (Less, Sign::Minus, 0) => {
            let (hi, lo) = div_rem(digits[0] as i64 + a.abs(), BIG_DIGIT_RADIX as i64);
            result.sign = Sign::Minus;
            result.scale = 0;
            let diff = a + digits[0] as BigDigitBaseSignedDouble;
            dbg!(a, digits[0], diff);
            if diff <= 0 {
                result.digits.push((-diff) as BigDigitBase);
                result.digits.extend_from_slice(&digits[1..]);
                dbg!(&result.digits);
            } else if digits.len() > 1 {
                result
                    .digits
                    .push((BIG_DIGIT_RADIX as BigDigitBaseSignedDouble - diff) as BigDigitBase);
                dbg!(&result.digits);
                let mut i = 1;
                while digits[i] == 0 {
                    result.digits.push((BIG_DIGIT_RADIX - 1) as BigDigitBase);
                    i += 1;
                }
                result.digits.push(digits[i] - 1);
                result.digits.extend_from_slice(&digits[i + 1..]);
            } else {
                result.sign = Sign::Plus;
                result.digits.push(diff as BigDigitBase);
            }
        }
        (Less, Sign::Plus, 0) | (Greater, Sign::Minus, 0) => {
            crate::arithmetic::addition::add_digit_vecs_into(&[a as BigDigitBase], digits, &mut result.digits);
            result.sign = sign;
            result.scale = 0;
        }
        (Less, Sign::Plus, scale) | (Greater, Sign::Minus, scale) if scale < 0 => {
            let (count, offset) = div_rem(-scale as usize, MAX_DIGITS_PER_BIGDIGIT);
            dbg!(count, offset);

            let mut a_digits = vec![0; count];
            let shift = 10_u32.pow(offset as u32) as BigDigitBaseDouble;
            let (a_hi, a_lo) = div_rem(a.abs() as BigDigitBaseDouble * shift, BIG_DIGIT_RADIX);


            a_digits.push(a_lo as BigDigitBase);
            a_digits.push(a_hi as BigDigitBase);

            dbg!(a, &a_digits, &digits, scale);
            // 10.powi(offset);

            crate::arithmetic::addition::add_digit_vecs_into(&a_digits[..], digits, &mut result.digits);
            result.sign = sign.neg();
            result.scale = scale;
        }
        (Less, Sign::Plus, scale) | (Greater, Sign::Minus, scale) if scale > 0 => {
            let (count, offset) = div_rem(scale as usize, MAX_DIGITS_PER_BIGDIGIT);
            dbg!(count, offset);
        }
        (Greater, Sign::Minus, scale) => {
            crate::arithmetic::addition::add_digit_vecs_into(&[a as BigDigitBase], digits, &mut result.digits);
            result.sign = Sign::Plus;
            result.scale = scale;
        }
        (Less, Sign::Plus, scale) => {
        }
        (Greater, Sign::Plus, scale) => {
        }
        _ => unimplemented!()
    };
}

#[inline]
pub(crate) fn sub_int_digit_vec_into(a: i64, b: &DigitInfo, result: &mut DigitInfo) {
    debug_assert!(b.digits.len() > 0);
    debug_assert!(b.digits.iter().all(|&d| (d as BigDigitBaseDouble) < BIG_DIGIT_RADIX));

    let DigitInfo { digits, scale, sign } = b;

    result.digits.clear();

    if a == 0 {
        result.digits.extend_from_slice(&digits);
        result.sign = sign.neg();
        result.scale = *scale;
        return;
    }

    if a.abs() < BIG_DIGIT_RADIX as i64 {
        return sub_small_int_digit_vec_into(a, b, result);
    }

    let (a_sign, a_digits) = {
        let mut v = vec![];
        let mut carry = a.abs();
        while carry != 0 {
            let (hi, lo) = div_rem(carry, BIG_DIGIT_RADIX as i64);
            v.push(lo as BigDigitBase);
            carry = hi;
        }

        if a >= 0 {
            (Sign::Plus, v)
        } else {
            (Sign::Minus, v)
        }
    };

    if digits.iter().all(|&d| d == 0) {
        result.digits.extend_from_slice(&a_digits);
        result.sign = a_sign;
        result.scale = 0;
        return;
    }

    match (*scale, *sign, a_sign) {
        (0, Sign::Plus, Sign::Plus) => {
            dbg!(&a_digits);
            dbg!(&digits);

            let digit_count = std::cmp::max(a_digits.len(), digits.len());

            let mut o_v = Vec::with_capacity(digit_count);
            let mut all_negative = true;
            let mut all_positive = true;
            let mut negative_count = 0;
            let mut positive_count = 0;
            let mut zero_count = 0;
            let mut all_zero = true;
            let mut trailing_zeros = 0;

            /*
            let f = |d: &BigDigitBase| *d as BigDigitBaseSignedDouble;

            let ai = a_digits.iter().map(f).chain(iter::repeat(0));
            let bi = digits.iter().map(f).chain(iter::repeat(0));

            for (a_d, b_d) in ai.zip(bi).take(digit_count) {
                let diff = a_d - b_d;
                o_v.push(diff);
                all_negative = all_negative && diff < 0;
                all_zero = all_zero && diff == 0;
            }
            */

            for i in 0..digit_count {
                let a_d = if i < a_digits.len() { a_digits[i] } else { 0 };
                let b_d = if i < digits.len() { digits[i] } else { 0 };

                let diff = a_d as BigDigitBaseSignedDouble - b_d as BigDigitBaseSignedDouble;
                o_v.push(diff);
                all_negative = all_negative && diff <= 0;
                all_positive = all_positive && diff >= 0;
                if diff <= 0 {
                    negative_count += 1;
                }
                if diff >= 0 {
                    positive_count += 1;
                }
                if diff == 0 {
                    zero_count += 1;
                }
                all_zero = all_zero && diff == 0;
                if diff == 0 {
                    trailing_zeros += 1;
                } else {
                    trailing_zeros = 0;
                }
            }
            dbg!(&o_v, all_negative, all_positive, all_zero, positive_count, negative_count, zero_count);

            result.scale = 0;

            if all_zero {
                result.sign = Sign::Plus;
                result.digits.push(0);
                return;
            }

            let digit_count = o_v.len() - trailing_zeros;
            let o_v = &mut o_v[..digit_count];

            if all_negative {
                result.sign = sign.neg();
                result.digits.extend(o_v.iter().map(|&d| -d as BigDigitBase));
                return;
            }

            result.sign = *sign;
            if digit_count == 1 && o_v[0] < 0 {
                result.digits.extend(o_v.iter().map(|&d| -d as BigDigitBase));
                dbg!(&result.digits);
                return;
            }

            if !all_positive {
                if o_v[digit_count - 1] > 0 {
                    for i in 0..digit_count - 1 {
                        dbg!(i, o_v[i]);
                        while o_v[i] < 0 {
                            o_v[i] += BIG_DIGIT_RADIX as BigDigitBaseSignedDouble;
                            o_v[i + 1] -= 1;
                            dbg!(&o_v);
                        }
                    }
                } else {

                }
            }

            dbg!(&o_v);
            result.digits.extend(o_v.iter().map(|&d| {
                debug_assert!(d >= 0);
                debug_assert!(d < BIG_DIGIT_RADIX as i64);
                d as BigDigitBase
            }));

            // remove trailing zeros
            for i in result.digits.len() - 1..1 {
                if result.digits[i] == 0 {
                    result.digits.pop();
                } else {
                    break;
                }
            }

            return;

            /*
            dbg!(&result.digits);
            result.scale = 0;
            result.digits.extend_from_slice(&digits);

            let diff = a as BigDigitBaseSignedDouble - digits[0] as BigDigitBaseSignedDouble;
            if diff >= 0 {
                result.digits.push(diff as BigDigitBase);
                all_negative = false;
            } else {
                result.digits.push(diff as BigDigitBase);
            }

            if all_negative {
                result.sign = sign.neg();
            }

            // for d in digits.iter() {
            //     println!("{}", d);
            // }

            // println!("OK {:?}", result.digits);

            // output.sniper()
            return;
            */
        }
        _ => unimplemented!(), // if *scale == 0 && 0 < a && a < BIG_DIGIT_RADIX as i64 {
    }

    // let DigitInfo { digits: mut result_digits, scale: mut out_scale, sign: mut out_sign } = result;
    // let DigitInfo { digits: mut result_digits, scale: mut out_scale, sign: mut out_sign } = result;

    // result.digits.copy_from_slice(&digits);
    result.digits.clear();

    // if *scale == 0 && *sign == Sign::Plus {
    dbg!(*scale, *sign, 0 <= a, digits.len());
    match (*scale, *sign, 0 <= a, a.abs() >= BIG_DIGIT_RADIX as i64, digits.len()) {
        (0, Sign::Plus, true, true, 1) => {
            let (mut hi, lo) = div_rem(a.abs(), BIG_DIGIT_RADIX as i64);
            let diff = lo as BigDigitBaseSignedDouble - digits[0] as BigDigitBaseSignedDouble;
            if diff > 0 {
                result.digits.push(diff as BigDigitBase);
            } else if hi > 0 {
                hi -= 1;
                let newlo = BIG_DIGIT_RADIX as BigDigitBaseSignedDouble + diff;
                result.digits.push(newlo as BigDigitBase);
            } else {
                unimplemented!()
            }
            while hi != 0 {
                let (up, lo) = div_rem(hi, BIG_DIGIT_RADIX as i64);
                result.digits.push(lo as BigDigitBase);
                hi = up;
            }

            dbg!(diff);
            result.digits.push(diff.abs() as BigDigitBase);
            result.scale = 0;
            result.sign = if diff < 0 { Sign::Minus } else { Sign::Plus };
        }
        (0, Sign::Plus, true, _, 1) => {
            let diff = a as BigDigitBaseSignedDouble - digits[0] as BigDigitBaseSignedDouble;
            dbg!(diff);
            result.digits.push(diff.abs() as BigDigitBase);
            result.scale = 0;
            result.sign = if diff < 0 { Sign::Minus } else { Sign::Plus };
        }
        (0, Sign::Plus, false, _, 1) => {
            let diff = a - digits[0] as BigDigitBaseSignedDouble;
            if diff == 0 {
                result.digits.push(0);
                result.sign = Sign::Plus;
                result.scale = 0;
                return;
            } else {
                dbg!(diff);
                let mut high = diff.abs();
                while high > 0 {
                    dbg!(high);
                    let (d, r) = div_rem(high, BIG_DIGIT_RADIX as BigDigitBaseSignedDouble);
                    result.digits.push(r as BigDigitBase);
                    high = d;
                }
            }
            result.scale = 0;
            result.sign = Sign::Minus;
        }
        (0, Sign::Plus, true, _, _) => {
            let diff = a - digits[0] as BigDigitBaseSignedDouble;
            dbg!(diff);
            result.digits.resize(digits.len(), 0);
            result.digits.copy_from_slice(&digits);
            if 0 <= diff {
                // result.digits.push(diff.abs() as BigDigitBase);
                // println!(">> {}", diff);
                // let v = MAX_DIGITS_PER_BIGDIGIT as BigDigitBaseSignedDouble - diff as BigDigitBaseSignedDouble;
                let v = dbg!(a as BigDigitBaseSignedDouble)
                    - dbg!(MAX_DIGITS_PER_BIGDIGIT as BigDigitBaseSignedDouble + digits[0] as BigDigitBaseSignedDouble);
                println!(">> {}", v);

                result.digits[0] = v as BigDigitBase;
                result.digits[1] -= 1;
            } else {
                // result.digits.push(-diff as BigDigitBase);
                result.digits[0] = -diff as BigDigitBase;
            }
            dbg!(&result.digits);
            result.sign = Sign::Minus;

            // let (index, offset)  = div_rem(*scale, MAX_BIG_DIGIT_BASE_DOUBLE as i64);
            // dbg!(index, offset);
            // let diff = a - digits[0] as BigDigitBaseSignedDouble;
            // dbg!(diff);
            // result.digits.resize();
            // result.digits.push(diff.abs() as BigDigitBase);
            // result.digits[1..].copy_from_slice(&digits[1..]);
            // result.scale = 0;
            // result.sign =  Sign::Plus;
        }
        (0, Sign::Plus, false, _, _) => {
            let diff = a - digits[0] as BigDigitBaseSignedDouble;
        }
        _ => unimplemented!(),
    }

    // match (a < 0, b.len()) {
    //     (_, 1) => {
    //         v.push((a - b[0]) as u32);
    //         Sign::Minus
    //     },
    //     _ => unimplemented!()
    // }
}

#[cfg(test)]
#[allow(overflowing_literals)]
#[allow(unreachable_patterns)]
#[allow(non_snake_case)]
mod test_sub_int_digit_vec_into {
    use super::*;

    #[test]
    fn test_10_3() {
        let input = DigitInfo {
            digits: digit_vec![3],
            scale: 0,
            sign: Sign::Plus,
        };

        let mut output = DigitInfo {
            digits: digit_vec![],
            scale: 0,
            sign: Sign::NoSign,
        };

        sub_int_digit_vec_into(10, &input, &mut output);
        assert_eq!(&output.digits, &[7]);
        assert_eq!(output.sign, Sign::Plus);
    }

    #[test]
    fn test_3_10() {
        let input = DigitInfo {
            digits: digit_vec![10],
            scale: 0,
            sign: Sign::Plus,
        };

        let mut output = DigitInfo {
            digits: digit_vec![],
            scale: 0,
            sign: Sign::NoSign,
        };

        sub_int_digit_vec_into(3, &input, &mut output);
        assert_eq!(&output.digits, &[7]);
        assert_eq!(output.sign, Sign::Minus);
    }

    #[test]
    fn test_20_3() {
        let input = DigitInfo {
            digits: digit_vec![2],
            scale: 100,
            sign: Sign::Plus,
        };

        let mut output = DigitInfo {
            digits: digit_vec![],
            scale: 0,
            sign: Sign::NoSign,
        };

        sub_int_digit_vec_into(3, &input, &mut output);
        assert_eq!(&output.digits, &[17]);
        assert_eq!(output.sign, Sign::Plus);
    }

    #[test]
    fn test_3_20202020202() {
        let input = DigitInfo {
            digits: digit_vec![202020202, 20],
            scale: 0,
            sign: Sign::Plus,
        };

        let mut output = DigitInfo {
            digits: digit_vec![],
            scale: 0,
            sign: Sign::NoSign,
        };

        sub_int_digit_vec_into(3, &input, &mut output);
        assert_eq!(&output.digits, &[202020199, 20]);
        assert_eq!(output.sign, Sign::Minus);
    }

    macro_rules! impl_test {
        (- $a:literal $($rest:tt)*) => {
            // impl_test!(ARGS -$a ; NAME ᄆｰ $a; $($rest)*);
            impl_test!(ARGS -$a ; NAME case_neg $a; $($rest)*);
        };
        ($a:literal $($rest:tt)*) => {
            // impl_test!(ARGS $a ; NAME  ᄆ  $a ; $($rest)*);
            impl_test!(ARGS $a ; NAME  case_ $a ; $($rest)*);
        };
        ( ARGS $a:expr; NAME $($name:expr)*; - [$($b:literal),+] $($rest:tt)*) => {
            impl_test!( ARGS $a; $($b),*; NAME $($name)* => ( $($b)* ) (); $($rest)*);
        };
        ( ARGS $a:expr; $($b:literal),+; NAME $($name:expr)* => ($nextb:literal $($forb:literal)*) ($($revb:literal)*); $($rest:tt)*) => {
            impl_test!( ARGS $a; $($b),*; NAME $($name)* => ( $($forb)* ) ( $nextb $($revb)* ); $($rest)*);
        };
        ( ARGS $a:expr; $($b:literal),+; NAME $($name:expr)* => () ( $($revb:literal)* ); $($rest:tt)*) => {
            // impl_test!( ARGS $a; $($b),*; NAME $($name)* ｰ $($revb)* => ; $($rest)*);
            impl_test!( ARGS $a; $($b),*; NAME $($name)* __ $($revb)* => ; $($rest)*);
        };
        ( ARGS $a:expr; $($b:literal),+; NAME $($name:expr)* => ; E - $scale:literal $($rest:tt)*) => {
            impl_test!( ARGS $a; $($b),*; -$scale; NAME $($name)* e_neg $scale; $($rest)*);
        };
        ( ARGS $a:expr; $($b:literal),+; NAME $($name:expr)* => ; E $scale:literal $($rest:tt)*) => {
            impl_test!( ARGS $a; $($b),*; $scale; NAME $($name)* e_ $scale; $($rest)* );
        };
        ( ARGS $a:expr; $($b:literal),+; NAME $($name:expr)* => ; $($rest:tt)*) => {
            impl_test!( ARGS $a; $($b),*; 0; NAME $($name)* ; $($rest)* );
        };
        ( ARGS $a:expr; $($b:literal),+; $scale:literal;  NAME $($name:expr)* ; = - [$($diff:literal),+] $($rest:tt)*) => {
            impl_test!( ARGS $a; $($b),*; $scale; Sign::Minus; $($diff),* ; NAME $($name)*; $($rest)* );
        };
        ( ARGS $a:expr; $($b:literal),+; $scale:literal;  NAME $($name:expr)* ; = [$($diff:literal),+] $($rest:tt)*) => {
            impl_test!( ARGS $a; $($b),*; $scale; Sign::Plus; $($diff),* ; NAME $($name)*; $($rest)* );
        };
        ( ARGS $a:expr; $($b:literal),*; $scale:literal; $sign:expr; $($r:literal),*; NAME $($name:expr)*; E $rscale:literal) => {
            impl_test!( ARGS $a; $($b),*; $scale; $sign; $($r),*; $rscale; NAME $($name)*; );
        };
        ( ARGS $a:expr; $($b:literal),*; $scale:literal; $sign:expr; $($r:literal),*; NAME $($name:expr)*;) => {
            impl_test!( ARGS $a; $($b),*; $scale; $sign; $($r),*; 0; NAME $($name)*; );
        };
        ( ARGS $a:expr; $($b:literal),*; $scale:literal; $sign:expr; $($r:literal),*; NAME $($name:expr)*;) => {
            impl_test!( ARGS $a; $($b),*; $scale; Sign::Plus; $($r),*; 0; NAME $($name)*; );
        };
        ( ARGS $a:expr; $($b:literal),*; $scale:literal; $sign:expr; $($r:literal),*; $rscale:literal; NAME $($name:expr)*;) => {
            paste! {
                #[test]
                fn [< $($name)* >]() {
                    impl_test!(IMPL $a; $($b),*; $scale; $sign; $($r),*; $rscale)
                }
            }
        };
        (IMPL $minuend:expr; $($subtrahend:literal),*; $scale:literal; $sign:expr; $($r:literal),*; $rscale:literal) => {{
            let input = DigitInfo {
                digits: digit_vec![$($subtrahend),*],
                scale: $scale,
                sign: Sign::Plus,
            };

            let mut output = DigitInfo {
                digits: digit_vec![],
                scale: 0,
                sign: Sign::NoSign,
            };

            sub_int_digit_vec_into($minuend, &input, &mut output);
            dbg!(&output.sign, &output.digits);
            assert_eq!(&output.digits, &[$($r),*]);
            assert_eq!(output.sign, $sign);
            assert_eq!(output.scale, $rscale);
        }};
    }

    impl_test!(123 - [030023874, 47234] = -[30023751, 47234]);
    impl_test!(-123 - [030023874, 47234] = -[30023997, 47234]);

    // impl_test!(-123 - [030023874, 47234] = -[30023997, 47234]);

    // impl_test!(123 - [0] = [123]);

    impl_test!(15 - [7] = [8]);
    impl_test!(7 - [15] = -[8]);
    impl_test!(898497495 - [898497496] = -[1]);
    // impl_test!(942445061 - [942445061] E 1 = -[482005549, 8]);

    impl_test!(1898497000 - [898497496, 1] = -[496]);
    impl_test!(1898497496 - [898497000, 1] = [496]);
    impl_test!(898497000 - [898497000, 1] = -[0, 1]);

    impl_test!(308558008 - [308558009, 1] = -[1, 1]);

    impl_test!(1522311586 - [936540162, 644790012, 745991119, 93] = -[414228576, 644790011, 745991119, 93]);

    impl_test!(-13 - [13] = -[26]);

    impl_test!(-958253824 - [958253824] = -[916507648, 1]);

    // impl_test!(11633491985251901031 - [1032340950] = -[219560081, 633491984, 11]);

    impl_test!(132340950 - [132340950] = [0]);

    // i64::MAX
    impl_test!(9223372036854775807 - [032340950, 1] = [822434857, 223372035, 9]);
    impl_test!(9223372036854775807 - [933375281] = [921400526, 223372035, 9]);
    impl_test!(
        9223372036854775807 - [945672187, 270605744, 453822838, 776256045, 8260] =
            -[90896380, 47233708, 453822829, 776256045, 8260]
    );
    impl_test!(
        9223372036854775807 - [3594813, 537760215, 712063757, 40691711, 5178] =
            -[148819006, 314388178, 712063748, 40691711, 5178]
    );

    // impl_test!(-16495329599712012293 - [958253824] = -[670266117, 495329600, 16]);
    // impl_test!(16495329599712012293 - [958253824] = -[753758469, 495329598, 16]);
    // impl_test!(9223372036854775808 - [958253824] = -[753758469, 495329598, 16]);

    impl_test!(2147483648 - [944215022, 2] = -[796731374]);
    impl_test!(-2147483648 - [944215022, 2] = -[91698670, 5]);

    impl_test!(-308558008 - [308558009, 1] = -[1, 1]);

    // impl_test!(
    //      - [999999999, 1] = -[1, 1]
    // );

    impl_test!(396984238 - [752594762, 901176759, 857429] = -[355610524, 901176759, 857429]);

    impl_test!(770949474 - [239227606, 633] = -[468278132, 632]);

    impl_test!(-845976267 - [624860973] E -6 = -[891860973, 845976] E -6);
    impl_test!(-475148789 - [398317042, 433486196] E -20 = -[398317042, 433486196, 514878900, 47] E -20);

    // #[test]
    // fn test_396984238_857429901176759752594762() {

    //     let input = DigitInfo {
    //         digits: digit_vec![752594762, 901176759, 857429],
    //         scale: 0,
    //         sign: Sign::Plus,
    //     };

    //     let mut output = DigitInfo {
    //         digits: digit_vec![],
    //         scale: 0,
    //         sign: Sign::NoSign,
    //     };

    //     sub_int_digit_vec_into(396984238, &input, &mut output);
    //     assert_eq!(&output.digits, &);
    //     assert_eq!(output.sign, Sign::Minus);
    // }
}

#[inline]
pub(crate) fn sub_digit_info_into(a: &DigitInfo, b: &DigitInfo, result: &mut DigitInfo) {
    let DigitInfo {
        digits: a_digits,
        scale: a_scale,
        sign: a_sign,
    } = a;
    let DigitInfo {
        digits: b_digits,
        scale: b_scale,
        sign: b_sign,
    } = b;

    // if
}

// fn add_digit_vecs(a_digits: &[BigDigitBase], a_scale: i64, b_digits
