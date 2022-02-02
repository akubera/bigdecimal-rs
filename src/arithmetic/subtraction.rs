use num_bigint::Sign;
use num_integer::div_rem;
use std::ops::Neg;
use std::cmp::Ordering;

use crate::bigdigit::{
    MAX_DIGITS_PER_BIGDIGIT,
    BIG_DIGIT_RADIX,
    BIG_DIGIT_RADIX_I64,
    BigDigitBase,
    BigDigitBaseSignedDouble,
    BigDigitVec,
    BigDigitBaseDouble,
    count_digits,
};

/// "lightweight" BigDecimal data
#[derive(Eq, PartialOrd)]
pub(crate) struct DigitInfo {
    pub digits: BigDigitVec,
    pub sign: Sign,
    pub scale: i64,
}

impl PartialEq for DigitInfo {
    fn eq(&self, other: &Self) -> bool {
        todo!()
    }
}

impl Ord for DigitInfo {
    fn cmp(&self, rhs: &DigitInfo) -> std::cmp::Ordering {
        let l_digit_count = count_digits(&self.digits);
        let r_digit_count = count_digits(&rhs.digits);

        let a_int_digits = l_digit_count as i64 + self.scale;
        let b_int_digits = r_digit_count as i64 + rhs.scale;

        Ordering::Less
    }
}


#[inline(always)]
fn negate_all_digits(mut v: Vec<i32>) -> Vec<u32> {
    for d in v.iter_mut() {
        debug_assert!(*d < 0);
        *d = d.abs();
    }

    convert_to_base_u32_vec(v)
}

fn convert_to_base_u32_vec(v: Vec<i32>) -> Vec<u32> {
    unsafe {
        debug_assert!(v.iter().all(|&d| d >= 0));
        std::mem::transmute::<Vec<i32>, Vec<u32>>(v)
    }
}

/// Subtract a:(digits, scale) - b:(digits, scale) with prec
/// precision and store in result
///
#[inline]
pub(crate) fn subtract_into(
    a_digits: &[BigDigitBase],
    a_scale: i64,
    b_digits: &[BigDigitBase],
    b_scale: i64,
    prec: std::num::NonZeroU32,
    result: &mut DigitInfo,
) {
    if a_scale == b_scale {
        _subtract_aligned_digits(a_digits, b_digits, prec, result);
        result.scale = a_scale;
        return;
    }

    let scale_diff = a_scale - b_scale;
    let delta_scale_abs = scale_diff.abs() as usize;

    dbg!(delta_scale_abs);
    dbg!(scale_diff);

    let (skip, offset) = num_integer::div_rem(delta_scale_abs, MAX_DIGITS_PER_BIGDIGIT);
    match std::num::NonZeroUsize::new(offset) {
        Some(offset) => _subtract_unaligned_digits(a_digits, b_digits, scale_diff, skip, offset, prec, result),
        None => unimplemented!("handle aligned digits?"),
    }

    dbg!(scale_diff, skip, offset);

    result.scale = a_scale.min(b_scale);
    result.sign = Sign::Plus;
    return;
    /*

        let a_int_digits = a_digit_count as i64 + a_scale;
        let b_int_digits = b_digit_count as i64 + b_scale;

        if a_int_digits < b_int_digits {
            subtract_into(b_digits, b_scale, a_digits, a_scale, prec, result);
            result.sign = result.sign.neg();
            result.scale = a_scale;
            return;
        }

        match (a_scale.cmp(&b_scale), a_digit_count.cmp(&b_digit_count)) {
            (Ordering::Less, Ordering::Less) => {}
            _ => unimplemented!(),
        }

        dbg!(a_int_digits, b_int_digits);

        let delta_scale = a_scale - b_scale;
        let delta_scale_abs = delta_scale.abs() as u32;
        let mask = to_power_of_ten(delta_scale_abs - 1);
        let shift = mask * 10;

        match delta_scale.cmp(&0) {
            Ordering::Equal => {
                unimplemented!();
            }
            Ordering::Greater => {
                // dbg!(diff);
                let mut carry = false;
                for i in 0..1 {
                    let a_shifted = a_digits[0] as BigDigitBaseDouble * shift as BigDigitBaseDouble;
                    let (a_hi, a_lo) = div_rem(a_shifted, BIG_DIGIT_RADIX);
                    dbg!(a_digits[0], a_hi, a_lo);
                    let diff = a_lo as BigDigitBaseSignedDouble - b_digits[0] as BigDigitBaseSignedDouble;
                    if diff < 0 {
                        result
                            .digits
                            .push(((BIG_DIGIT_RADIX as BigDigitBaseSignedDouble) + diff) as BigDigitBase);
                        carry = true;
                    } else if carry && diff == 0 {
                        result
                            .digits
                            .push(((BIG_DIGIT_RADIX as BigDigitBaseSignedDouble) - 1) as BigDigitBase);
                    } else if carry && diff != 0 {
                        result.digits.push((diff - 1) as BigDigitBase);
                        carry = false;
                    } else {
                        result.digits.push(diff as BigDigitBase);
                    }
                }

                // if a_hi != 0 {
                //     unimplemented!();
                // }
                // if diff > 0 {
                //     result.sign = Sign::Plus;
                //     return;
                // }
                // dbg!(a_hi);
            }
            Ordering::Less => {
                unimplemented!();
            }
        }

        // if a_digits.len() == 1 && b_digits.len() == 1 && delta_scale_abs < MAX_DIGITS_PER_BIGDIGIT as u32 {
        //     let (a_hi, a_lo) = div_rem(a_digits[0], shift);
        //     let a_lo_shift = a_lo * shift;
        //     dbg!(a_lo))
        //     // let (b_hi, b_lo) = div_rem(b_digits[0], shift);
        //     // unimplemented!();
        // }

        let i = 0;

        let (hi, lo) = div_rem(a_digits[i], shift);
        let x = lo * shift;
        dbg!(a_digits[i], x, hi);

        // MAX_DIGITS

        // let scale_a => {
        //     delta_scale
        // };
        // if del   ta_scale

        // let abc = a_int_digits - b_int_digits;
    */
}

#[cfg(test)]
#[allow(non_snake_case)]
mod test_subtract_into {
    use super::*;

    macro_rules! impl_test {
        ( [$($a:literal),+] $($rest:tt)* ) => {
            impl_test!( ARGS $($a),*; ($($a)*) -> (); NAME case__ ;; $($rest)* );
        };
        ( ARGS $($a:literal),*; ($a0:literal $($ar:literal)*) -> ($($an:literal)*); NAME $($names:expr)* ;; $($rest:tt)*) => {
            impl_test!( ARGS $($a),*; ($($ar)*) -> ($a0 $($an)*); NAME $($names)* ;; $($rest)* );
        };
        ( ARGS $($a:literal),*; () -> ($($an:literal)*); NAME $($names:expr)* ;; E -$a_scale:literal $($rest:tt)*) => {
            impl_test!( ARGS $($a),*; -$a_scale; NAME $($names)* $($an)* _e_neg $a_scale ;; $($rest)* );
        };
        ( ARGS $($a:literal),*; () -> ($($an:literal)*); NAME $($names:expr)* ;; E $a_scale:literal $($rest:tt)*) => {
            impl_test!( ARGS $($a),*; $a_scale; NAME $($names)* $($an)* _e $a_scale ;; $($rest)* );
        };
        ( ARGS $($a:literal),*; $a_scale:literal; NAME $($names:expr)* ;; - [$($b:literal),+] $($rest:tt)*) => {
            impl_test!( ARGS $($a),*; $a_scale; $($b),*; ($($b)*) -> (); NAME $($names)* ;; $($rest)* );
        };
        ( ARGS $($a:literal),*; $a_scale:literal; $($b:literal),*; ($b0:literal $($br:literal)*) -> ($($bn:literal)*); NAME $($names:expr)* ;; $($rest:tt)*) => {
            impl_test!( ARGS $($a),*; $a_scale; $($b),*; ($($br)*) -> ($b0 $($bn)*); NAME $($names)* ;; $($rest)* );
        };
        ( ARGS $($a:literal),*; $a_scale:literal; $($b:literal),*; () -> ($($bn:literal)*); NAME $($names:expr)* ;; E -$b_scale:literal $($rest:tt)*) => {
            impl_test!( ARGS $($a),*; $a_scale; $($b),*; -$b_scale; NAME $($names)* __ $($bn)* _e_neg $b_scale ;; $($rest)* );
        };
        ( ARGS $($a:literal),*; $a_scale:literal; $($b:literal),*; () -> ($($bn:literal)*); NAME $($names:expr)* ;; E $b_scale:literal $($rest:tt)*) => {
            impl_test!( ARGS $($a),*; $a_scale; $($b),*; $b_scale; NAME $($names)* __ $($bn)* _e $b_scale ;; $($rest)* );
        };
        ( ARGS $($a:literal),*; $a_scale:literal; $($b:literal),*; $b_scale:literal; NAME $($names:expr)* ;; = - [$($d:literal),*] E $d_scale:literal $($rest:tt)*) => {
            impl_test!( ARGS $($a),*; $a_scale; $($b),*; $b_scale; Sign::Minus; $($d),*; $d_scale; NAME $($names)* ;; $($rest)* );
        };
        ( ARGS $($a:literal),*; $a_scale:literal; $($b:literal),*; $b_scale:literal; NAME $($names:expr)* ;; = [$($d:literal),*] E $d_scale:literal $($rest:tt)*) => {
            impl_test!( ARGS $($a),*; $a_scale; $($b),*; $b_scale; Sign::Plus; $($d),*; $d_scale; NAME $($names)* ;; $($rest)* );
        };
        ( ARGS $($a:literal),+; $a_scale:literal; $($b:literal),+; $b_scale:literal; $sign:expr; $($r:literal),+; $r_scale:literal; NAME $($name:expr)* ;; ) => {
            paste! {
                #[test]
                fn [< $($name)* >]() {
                    impl_test!( IMPL $($a)*; $a_scale; $($b)*; $b_scale; $sign; $($r)*; $r_scale; 19; )
                }
            }
        };
        (IMPL $($a:literal)*; $a_scale:literal; $($b:literal)*; $b_scale:literal; $sign:expr; $($r:literal)*; $rscale:literal; $prec:literal; ) => {{
            let a_digits = [$($a),*];
            let b_digits = [$($b),*];

            let mut output = DigitInfo {
                digits: digit_vec![],
                scale: 0,
                sign: Sign::NoSign,
            };

            $( assert!(($a as i128) < (BIG_DIGIT_RADIX as i128)); )*
            $( assert!(($b as i128) < (BIG_DIGIT_RADIX as i128)); )*
            $( assert!(($r as i128) < (BIG_DIGIT_RADIX as i128)); )*

            subtract_into(&a_digits, $a_scale, &b_digits, $b_scale, std::num::NonZeroU32::new($prec).unwrap(), &mut output);

            dbg!(&output.sign, &output.digits);
            assert_eq!(&output.digits, &[$($r),*]);
            assert_eq!(output.sign, $sign);
            assert_eq!(output.scale, $rscale);
        }};
    }

    impl_test!([123]E 2 - [938]E 0 = -[93677]E 0);
    impl_test!([287]E 0 - [554]E 12 = -[999999713, 553999]E 0);
    impl_test!([719479559]E 2 - [947]E 6 = [710009559]E 2);
    impl_test!([7305274]E 2 - [633870639]E 21 = -[699084726, 6338]E 2);
    impl_test!([7305274]E 2 - [633870639]E 6 = -[699084726, 6338]E 2);
    impl_test!([401110279]E 0 - [271733004]E 0 = [129377275]E 0);
    impl_test!([2413893]E -7 - [907304782, 7137056]E -7 = - [904890889, 7137056]E -7);
    impl_test!([279982322, 3142305]E 20 - [8456861]E 20 = [271525461, 3142305]E 20 );
    impl_test!([712499514, 215065916, 733712324, 292]E -8 - [207657154, 921507228, 49]E -4 = [140959514, 142783840, 733213109, 292]E -8);
    // impl_test!([712499514, 215065916, 733712324, 292]E -8 - [207657154, 921507228, 49]E -4 = [140959514, 142783840, 733213109, 292]E -8);
    // impl_test!([712499514, 215065916, 733712324, 292]E -8 - [207657154, 921507228, 49]E -4 = [401409595, 91427838, 927332131, 2]E -8);

    impl_test!([62702530, 608163963, 110352346]E -6 - [627989360, 234532112, 586856646]E -14 = [392493193, 494782984, 103523465, 1]E -5);

    impl_test!([61954945]E 0 - [82116691]E -4 = [467333309, 619]E -4);
    // impl_test!([42026610]E 4 - [3187757]E -4 = [996812243, 4202660]E -4);

    impl_test!([90501172]E 2 - [5039448]E -8 = [994960552, 905011719]E -8);

    impl_test!([26632001]E 0 - [0, 109]E -11 = [0, 663199991, 2]E -11);
    impl_test!([89003121]E 0 - [0, 201]E -30 = [0, 663199991, 2]E -11);
}

#[inline]
pub(crate) fn sub_digit_vecs(a: &[BigDigitBase], b: &[BigDigitBase]) -> Vec<BigDigitBase> {
    let mut result = Vec::with_capacity(a.len().max(b.len()));
    sub_digit_vecs_into(a, b, &mut result);
    return result;
}

#[inline]
pub(crate) fn sub_digit_vecs_into(a: &[BigDigitBase], b: &[BigDigitBase], v: &mut Vec<BigDigitBase>) {
    if a.len() == 1 && b.len() == 1 {
        debug_assert!(a[0] >= b[0]);
        let diff = a[0] - b[0];
        v.push(diff);
        return;
    }

    // a is longer of the vectors
    let (a, b) = if a.len() >= b.len() { (a, b) } else { (b, a) };

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
        assert_eq!(&v, &[10]);
    }

    #[test]
    fn test_10_3() {
        let v = sub_digit_vecs(&[10], &[3]);
        assert_eq!(&v, &[7]);
    }
}

pub(crate) fn sub_small_int_digit_vec_into(a: i64, b: &DigitInfo, result: &mut DigitInfo) {
    debug_assert!(a.abs() < BIG_DIGIT_RADIX as i64);
    debug_assert!(b.digits.len() > 0);

    let DigitInfo {
        digits: b_digits,
        scale,
        sign,
    } = b;
    let sign = *sign;

    result.digits.clear();

    if *scale == 0 && b_digits.len() == 1 && a == b_digits[0] as i64 {
        result.sign = Sign::Plus;
        result.digits.push(0);
        result.scale = 0;
        return;
    }

    dbg!(a.cmp(&0), sign, *scale);
    match (a.cmp(&0), sign, *scale) {
        (_, Sign::NoSign, _) => {
            debug_assert!(b_digits.iter().all(|&d| d == 0));
            result.scale = 0;
            if a < 0 {
                result.sign = Sign::Minus;
                result.digits.push((-a) as BigDigitBase);
            } else {
                result.sign = Sign::Plus;
                result.digits.push(a as BigDigitBase);
            }
        }
        (Ordering::Equal, _, scale) => {
            result.digits.extend_from_slice(&b_digits);
            result.sign = sign.neg();
            result.scale = scale;
            return;
        }
        (Ordering::Less, Sign::Plus, 0) | (Ordering::Greater, Sign::Minus, 0) => {
            let (hi, lo) = div_rem(b_digits[0] as i64 + a.abs(), BIG_DIGIT_RADIX as i64);
            dbg!((hi, lo));
            result.digits.push(lo as BigDigitBase);

            let mut carry = hi as BigDigitBase;
            let mut i = 1;
            while carry > 0 {
                if i == b_digits.len() {
                    result.digits.push(carry);
                    break;
                }
                let (hi, lo) = div_rem(b_digits[i] + carry, BIG_DIGIT_RADIX as BigDigitBase);
                result.digits.push(lo);
                carry = hi;
                i += 1;
            }
            if i < b_digits.len() {
                result.digits.extend_from_slice(&b_digits[i..]);
            }
            dbg!(&result.digits);
            result.sign = sign.neg();
            result.scale = 0;
        }
        (Ordering::Greater, Sign::Plus, 0) => {
            result.sign = Sign::Minus;
            result.scale = 0;

            let diff = a - b_digits[0] as BigDigitBaseSignedDouble;
            dbg!(a, b_digits[0], diff);
            if diff <= 0 {
                result.digits.push((-diff) as BigDigitBase);
                result.digits.extend_from_slice(&b_digits[1..]);
                dbg!(&result.digits);
            } else if b_digits.len() > 1 {
                result
                    .digits
                    .push((BIG_DIGIT_RADIX as BigDigitBaseSignedDouble - diff) as BigDigitBase);
                dbg!(&result.digits);
                let mut i = 1;
                while b_digits[i] == 0 {
                    result.digits.push((BIG_DIGIT_RADIX - 1) as BigDigitBase);
                    i += 1;
                }
                let is_last_digit_trailing_zero = b_digits[i] > 1 || i + 1 != b_digits.len();
                if is_last_digit_trailing_zero {
                    result.digits.push(b_digits[i] - 1);
                    result.digits.extend_from_slice(&b_digits[i + 1..]);
                }
                dbg!(&result.digits);
            } else {
                result.sign = Sign::Plus;
                result.digits.push(diff as BigDigitBase);
            }
        }
        (Ordering::Less, Sign::Minus, 0) => {
            // let (hi, lo) = div_rem(digits[0] as i64 + a.abs(), BIG_DIGIT_RADIX as i64);
            result.sign = Sign::Minus;
            result.scale = 0;
            let diff = a + b_digits[0] as BigDigitBaseSignedDouble;
            dbg!(a, b_digits[0], diff);
            if diff <= 0 {
                result.digits.push((-diff) as BigDigitBase);
                result.digits.extend_from_slice(&b_digits[1..]);
                dbg!(&result.digits);
            } else if b_digits.len() > 1 {
                result
                    .digits
                    .push((BIG_DIGIT_RADIX as BigDigitBaseSignedDouble - diff) as BigDigitBase);
                dbg!(&result.digits);
                let mut i = 1;
                while b_digits[i] == 0 {
                    result.digits.push((BIG_DIGIT_RADIX - 1) as BigDigitBase);
                    i += 1;
                }
                result.digits.push(b_digits[i] - 1);
                result.digits.extend_from_slice(&b_digits[i + 1..]);
            } else {
                result.sign = Sign::Plus;
                result.digits.push(diff as BigDigitBase);
            }
        }
        (Ordering::Less, Sign::Plus, scale) | (Ordering::Greater, Sign::Minus, scale) if scale < 0 => {
            let (count, offset) = div_rem(-scale as usize, MAX_DIGITS_PER_BIGDIGIT);
            dbg!(count, offset);

            let mut a_digits = vec![0; count];
            let shift = 10_u32.pow(offset as u32) as BigDigitBaseDouble;
            let (a_hi, a_lo) = div_rem(a.abs() as BigDigitBaseDouble * shift, BIG_DIGIT_RADIX);

            a_digits.push(a_lo as BigDigitBase);
            a_digits.push(a_hi as BigDigitBase);

            dbg!(a, &a_digits, &b_digits, scale);
            // 10.powi(offset);

            crate::arithmetic::addition::add_digit_vecs_into(&a_digits[..], b_digits, &mut result.digits);
            result.sign = sign.neg();
            result.scale = scale;
        }
        (Ordering::Less, Sign::Plus, scale) | (Ordering::Greater, Sign::Minus, scale) if scale > 0 => {
            let (count, offset) = div_rem(scale as usize, MAX_DIGITS_PER_BIGDIGIT);
            dbg!(count, offset);
        }
        (Ordering::Greater, Sign::Minus, scale) => {
            crate::arithmetic::addition::add_digit_vecs_into(&[a as BigDigitBase], b_digits, &mut result.digits);
            result.sign = Sign::Plus;
            result.scale = scale;
        }
        (Ordering::Less, Sign::Plus, _scale) => {}
        (Ordering::Greater, Sign::Plus, _scale) => {}
        _ => unimplemented!(),
    };
}

/// Special case of subtracting vectors of digits
///
/// Note: result.digits is NOT cleared, so zeros or other values may
/// be prefixed before
#[inline]
fn _subtract_aligned_digits(
    a_digits: &[BigDigitBase],
    b_digits: &[BigDigitBase],
    prec: std::num::NonZeroU32,
    result: &mut DigitInfo,
) {
    dbg!(&prec);
    debug_assert!(a_digits[a_digits.len() - 1] != 0);
    debug_assert!(b_digits[b_digits.len() - 1] != 0);

    let a_len = a_digits.len();
    let b_len = b_digits.len();

    let digit_count = std::cmp::max(a_len, b_len);
    result.digits.reserve(result.digits.len() + digit_count);

    // handle case of subtracting a single big-digit
    if a_len > 1 && b_digits.len() == 1 {
        result.sign = Sign::Plus;

        let diff = a_digits[0] as i64 - b_digits[0] as i64;

        dbg!(dbg!(diff) >= 0, diff < BIG_DIGIT_RADIX_I64);

        match (diff >= 0, diff < BIG_DIGIT_RADIX_I64) {
            (true, true) => {
                result.digits.push(diff as BigDigitBase);
                result.digits.extend_from_slice(&a_digits[1..]);
            }
            (true, false) => {
                result.digits.push((diff - BIG_DIGIT_RADIX as i64) as BigDigitBase);

                let mut i = 1;
                while i < a_len && a_digits[i] == (BIG_DIGIT_RADIX as u32 - 1) {
                    result.digits.push(0);
                    i += 1;
                }
                if i == a_len {
                    // all a_digits were MAX, just carry the 1
                    result.digits.push(1);
                } else if i + 1 == a_len {
                    // increment last digit
                    result.digits.push(a_digits[i] + 1);
                } else {
                    // increment next digit and copy the rest
                    result.digits.push(a_digits[i] + 1);
                    result.digits.extend_from_slice(&a_digits[i + 1..]);
                }
            }
            (false, _) => {
                result.digits.push((BIG_DIGIT_RADIX as i64 + diff) as BigDigitBase);
                let mut i = 1;
                while a_digits[i] == 0 {
                    result.digits.push(BIG_DIGIT_RADIX as BigDigitBase - 1);
                    i += 1;
                }
                // skip trailing zero
                if !(i == a_digits.len() - 1 && a_digits[i] == 1) {
                    result.digits.push(a_digits[i] - 1);
                    result.digits.extend_from_slice(&a_digits[i + 1..]);
                }
            }
        }
        return;
    }

    let a_b_cmp = if a_len < b_len {
        Ordering::Less
    } else if b_len < a_len {
        Ordering::Greater
    } else {
        let mut i = a_len - 1;
        while i > 0 && a_digits[i] == b_digits[i] {
            i -= 1;
        }
        a_digits[i].cmp(&b_digits[i])
    };

    let (sign, g_digits, l_digits) = match a_b_cmp {
        Ordering::Equal => {
            result.digits.push(0);
            result.sign = Sign::NoSign;
            result.scale = 0;
            return;
        }
        Ordering::Greater => (Sign::Plus, a_digits, b_digits),
        Ordering::Less => (Sign::Minus, b_digits, a_digits),
    };

    result.sign = sign;
    dbg!(result.sign);

    let mut trailing_zero_count = 0;

    let mut carry = 0;
    for i in 0..l_digits.len() {
        let diff = g_digits[i] as i32 - l_digits[i] as i32 + carry;
        if diff == 0 {
            trailing_zero_count += 1;
        } else {
            trailing_zero_count = 0;
        }
        dbg!((i, diff));
        if diff < 0 {
            let d = (BIG_DIGIT_RADIX as i32 + diff) as BigDigitBase;
            dbg!(d);
            result.digits.push(d);
            carry = -1;
        } else {
            result.digits.push(diff as BigDigitBase);
            carry = 0;
        }
    }

    if g_digits.len() == l_digits.len() {
        assert_eq!(carry, 0);
    } else if carry == 0 {
        result.digits.extend_from_slice(&g_digits[l_digits.len()..]);
        trailing_zero_count = 0;
    } else if g_digits.len() == l_digits.len() + 1 && g_digits[l_digits.len()] == 1 {
        // do-nothing if carry is -1 and last digit is 1 (no trailing zero)
    } else {
        let mut i = l_digits.len();
        while g_digits[i] == 0 {
            i += 1;
            result.digits.push(BIG_DIGIT_RADIX as BigDigitBase - 1);
        }

        result.digits.push(g_digits[i] - 1);
        if i < g_digits.len() {
            result.digits.extend_from_slice(&g_digits[i + 1..]);
        }

        trailing_zero_count = 0;
    }

    if trailing_zero_count != 0 {
        result.digits.truncate(result.digits.len() - trailing_zero_count);
    }
    dbg!(l_digits);
    dbg!(g_digits);

    return;
    /*

    dbg!(&a_digits);
    dbg!(&b_digits);

    let mut diff_vec = Vec::with_capacity(digit_count);

    let mut all_negative = true;
    let mut all_positive = true;
    let mut negative_count = 0;
    let mut positive_count = 0;
    let mut zero_count = 0;
    let mut all_zero = true;
    let mut trailing_zeros = 0;

    let f = |d: &BigDigitBase| *d as i32;

    let ai = a_digits.iter().map(f).chain(iter::repeat(0));
    let bi = b_digits.iter().map(f).chain(iter::repeat(0));

    let mut carry = 0;
    for (a_d, b_d) in ai.zip(bi).take(digit_count) {
        let diff = a_d - b_d;
        // if diff < 0 {
        // }
        // diff_vec.push(diff);
        // all_negative = all_negative && diff < 0;
        // all_zero = all_zero && diff == 0;
    }

    for i in 0..digit_count {
        let a_d = if i < a_digits.len() { a_digits[i] } else { 0 };
        let b_d = if i < b_digits.len() { b_digits[i] } else { 0 };

        let diff = a_d as i32 - b_d as i32;
        diff_vec.push(diff);

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
    dbg!(&diff_vec, all_negative, all_positive, all_zero, positive_count, negative_count, zero_count);

    result.scale = 0;

    if all_zero {
        debug_assert!(zero_count == diff_vec.len());
        result.sign = Sign::Plus;
        result.digits.push(0);
        return;
    }

    // ignore trailing zeros
    let digit_count = diff_vec.len() - trailing_zeros;
    if trailing_zeros > 0 {
        diff_vec.truncate(digit_count);
    }
    let last_index = digit_count - 1;

    // the difference is negative if the highest order byte is negative
    if diff_vec[last_index] < 0 {
        result.sign = Sign::Minus;
    } else {
        result.sign = Sign::Plus;
    }
    */
}

/// Subtract slices of bigdigits with different digit boundaries
///
///
#[inline]
fn _subtract_unaligned_digits(
    a_digits: &[BigDigitBase],
    b_digits: &[BigDigitBase],
    scale_diff: i64,
    skip: usize,
    offset: std::num::NonZeroUsize,
    prec: std::num::NonZeroU32,
    result: &mut DigitInfo,
) {
    debug_assert!(scale_diff != 0);

    // they should not be aligned
    let offset = offset.get();
    dbg!(prec);

    dbg!(scale_diff < 0);

    let shift = ten_to_pow!(offset);
    let mask = ten_to_pow!(MAX_DIGITS_PER_BIGDIGIT as u32 - offset as u32);
    assert_eq!(shift * mask, BIG_DIGIT_RADIX as u32);

    // 'a' has more digits after decimal place
    if scale_diff < 0 {
        // let shift = ten_to_pow!(offset);
        // let mask = shift * 10;
        // assert_eq!(shift * mask, BIG_DIGIT_RADIX as u32);

        if skip > 0 {
            result.digits.extend_from_slice(&a_digits[..skip]);
        }

        let mut i = 0;
        // debug_assert!(b_digits.len() <= a_digits[skip..].len());

        let mut carry = 0;
        let mut sub_carry = 0;
        while i < b_digits.len() {
            let (b_hi, b_lo) = num_integer::div_rem(b_digits[i], mask);

            let next_a = a_digits[skip + i];
            let shifted_b = carry + b_lo * shift;

            let d = next_a as i32 - shifted_b as i32;
            dbg!(next_a, shifted_b, d);
            if d < 0 && sub_carry == 0 {
                sub_carry = -1;
                result.digits.push((BIG_DIGIT_RADIX as i32 + d) as BigDigitBase);
            } else if d < 0 {
                unimplemented!();
                // result.digits.push(BIG_DIGIT_RADIX + d);
            } else if d > 0 {
                result.digits.push((d + sub_carry) as BigDigitBase);
            } else {
                unimplemented!();
            }

            carry = b_hi;
            i += 1;
        }

        if i < a_digits.len() {
            let next_a = a_digits[skip + i];
            if sub_carry != 0 {
                unimplemented!();
            }
            debug_assert!((next_a - carry) > 0);
            result.digits.push((next_a - carry) as BigDigitBase);
            result.digits.extend_from_slice(&a_digits[skip + i + 1..]);
        }
    } else {
        dbg!(skip, shift, mask);

        // 'b' has more digits after decimal place
        let mut sub_carry = 0;
        // if skip == 1 {
        //     if b_digits[0] == 0 {
        //         result.digits.push(0);
        //     } else {
        //         let diff = BIG_DIGIT_RADIX as i32 - b_digits[0] as i32;
        //         result.digits.push(diff as BigDigitBase);
        //         sub_carry = 1;
        //     }
        // } else if skip > 0 {
            for i in 0..skip {
                match (b_digits[i], sub_carry) {
                    (0, 0) => {
                        result.digits.push(0);
                    }
                    (0, _) => {
                        let diff = BIG_DIGIT_RADIX - 1 as BigDigitBaseDouble;
                        result.digits.push(diff as BigDigitBase);
                        sub_carry = 0;
                    }
                    (d, 0) => {
                        let diff = BIG_DIGIT_RADIX - d as BigDigitBaseDouble;
                        result.digits.push(diff as BigDigitBase);
                        sub_carry = 1;
                    }
                    (d, _) if d == (BIG_DIGIT_RADIX - 1) as u32 => {
                        let diff = BIG_DIGIT_RADIX - d as BigDigitBaseDouble;
                        result.digits.push(diff as BigDigitBase);
                        sub_carry = 0;
                    }
                    (d, _) => {
                        let diff = BIG_DIGIT_RADIX - d as BigDigitBaseDouble;
                        result.digits.push(diff as BigDigitBase);
                        sub_carry = 0;
                    }
                }
            }

        if a_digits.len() <= b_digits[skip..].len() {
        }
            // result.digits.extend_from_slice(&b_digits[..skip]);
        // }

        dbg!(a_digits.len(), b_digits[skip..].len());
        debug_assert!(a_digits.len() <= b_digits[skip..].len());

        let mut i = 0;
        let mut carry = 0;
        while i < a_digits.len() {
            let (hi_a, lo_a) = div_rem(a_digits[i], mask);
            dbg!(hi_a, lo_a);

            let shifted_a = lo_a * shift + carry;
            dbg!(shifted_a);
            let diff = shifted_a as i32 - b_digits[i + skip] as i32;
            dbg!(diff);
            if diff >= 0 {
                result.digits.push(diff as u32);
            } else {
                result.digits.push((BIG_DIGIT_RADIX as i64 + diff as i64) as u32);
            }

            // dbg!(b_hi, b_lo, a_digits);

            // let next_a = a_digits[skip + i];
            // dbg!(next_a, carry, b_lo, shift);
            // let shifted_b = carry + b_lo * shift;

            // let d = next_a as i32 - shifted_b as i32;
            // dbg!(next_a, shifted_b, d);
            // if d < 0 && sub_carry == 0 {
            //     sub_carry = -1;
            //     result.digits.push((BIG_DIGIT_RADIX as i32 + d) as BigDigitBase);
            // } else if d < 0 {
            //     unimplemented!();
            //     // result.digits.push(BIG_DIGIT_RADIX + d);
            // } else if d > 0 {
            //     result.digits.push((d + sub_carry) as BigDigitBase);
            // } else {
            //     unimplemented!();
            // }

            carry = hi_a;
            i += 1;
        }

        if carry != 0 {
            result.digits.push(carry as BigDigitBase);
        }

        // if i < a_digits.len() {
        //     let next_a = a_digits[skip + i];
        //     if sub_carry != 0 {
        //         unimplemented!();
        //     }
        //     debug_assert!((next_a - carry) > 0);
        //     result.digits.push((next_a - carry) as BigDigitBase);
        //     result.digits.extend_from_slice(&a_digits[skip + i + 1..]);
        // }
    }

    // unimplemented!()
    // let mask = to_power_of_ten(lo) as i64;

    // dbg!(dbg!(scale_diff) % dbg!(MAX_DIGITS_PER_BIGDIGIT as i64));
}

#[inline]
pub(crate) fn sub_int_digit_vec_into(a: i64, b: &DigitInfo, prec: std::num::NonZeroU32, result: &mut DigitInfo) {
    debug_assert!(b.digits.len() > 0);
    debug_assert!(b.digits.iter().all(|&d| (d as BigDigitBaseDouble) < BIG_DIGIT_RADIX));

    let DigitInfo {
        digits: b_digits,
        scale,
        sign,
    } = b;
    let b_scale = *scale;
    let b_sign = *sign;

    result.digits.clear();

    // handle case (0 - b) = -b
    if a == 0 {
        result.digits.extend_from_slice(&b_digits);
        result.sign = sign.neg();
        result.scale = b_scale;
        return;
    }

    if a.abs() < BIG_DIGIT_RADIX as i64 {
        return sub_small_int_digit_vec_into(a, b, result);
    }

    let mut digit_buff = [0u32; 3];
    let (a_sign, a_digits) = {
        let mut carry = a.abs();
        let mut i = 0;
        while carry != 0 {
            let (hi, lo) = div_rem(carry, BIG_DIGIT_RADIX as i64);
            dbg!(carry, hi, lo);
            digit_buff[i] = lo as BigDigitBase;
            carry = hi;
            i += 1;
        }

        if a >= 0 {
            (Sign::Plus, &digit_buff[..i])
        } else {
            (Sign::Minus, &digit_buff[..i])
        }
    };

    // handle case (a - 0) = a
    if b_sign == Sign::NoSign || b_digits.iter().rev().all(|&d| d == 0) {
        result.digits.extend_from_slice(a_digits);
        result.sign = a_sign;
        result.scale = 0;
        return;
    }

    debug_assert!(a_digits.len() <= 3);
    debug_assert!(a_digits[a_digits.len() - 1] > 0);
    dbg!(&a_digits);
    dbg!(&b_digits);

    if b_scale == 0 {
        if a_sign == b_sign {
            _subtract_aligned_digits(a_digits, b_digits, prec, result);
            result.scale = 0;
            if a_sign == Sign::Minus {
                result.sign = result.sign.neg();
            }
        } else {
            crate::arithmetic::addition::add_digit_vecs_into(a_digits, b_digits, &mut result.digits);
            result.scale = 0;
            result.sign = a_sign;
        }
        return;
    }

    let (count, offset) = div_rem(b_scale, MAX_DIGITS_PER_BIGDIGIT as i64);
    dbg!((count, offset));
    match (count, offset) {
        (-1, 0) => {
            // dbg!(b_scale % (MAX_DIGITS_PER_BIGDIGIT as i64));
            result.digits.push(count as u32);
            result.digits.push(offset as u32);
        }
        _ => unimplemented!(),
    }

    if b_scale < 0 {
        dbg!(b_scale % (MAX_DIGITS_PER_BIGDIGIT as i64));
    }

    // foo bar
    if b_scale > 0 {
        dbg!(a_digits.len());
        match b_scale as usize % MAX_DIGITS_PER_BIGDIGIT {
            0 => {
                let digit_count = std::cmp::max(a_digits.len(), b_digits.len());
                dbg!(digit_count);
            }
            _ => unimplemented!(),
        }
    }

    subtract_into(a_digits, 0, b_digits, b_scale, prec, result);

    unimplemented!();
}

#[cfg(test)]
#[allow(overflowing_literals)]
#[allow(unreachable_patterns)]
#[allow(non_snake_case)]
mod test_sub_int_digit_vec_into {
    use super::*;

    const DEFAULT_PREC: std::num::NonZeroU32 = unsafe { std::num::NonZeroU32::new_unchecked(19) };

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

        sub_int_digit_vec_into(10, &input, DEFAULT_PREC, &mut output);
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

        sub_int_digit_vec_into(3, &input, DEFAULT_PREC, &mut output);
        assert_eq!(&output.digits, &[7]);
        assert_eq!(output.sign, Sign::Minus);
    }

    #[test]
    fn test_20_3() {
        let input = DigitInfo {
            digits: digit_vec![2],
            scale: 1,
            sign: Sign::Plus,
        };

        let mut output = DigitInfo {
            digits: digit_vec![],
            scale: 0,
            sign: Sign::NoSign,
        };

        sub_int_digit_vec_into(3, &input, DEFAULT_PREC, &mut output);
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

        sub_int_digit_vec_into(3, &input, DEFAULT_PREC, &mut output);
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

            assert!(($minuend as i128) <= (i64::MAX as i128));

            sub_int_digit_vec_into($minuend, &input, DEFAULT_PREC, &mut output);
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
    impl_test!(308558008 - [308558007, 1] = -[999999999]);
    impl_test!(-308558008 - [308558009, 1] = -[617116017, 1]);

    impl_test!(1522311586 - [936540162, 644790012, 745991119, 93] = -[414228576, 644790011, 745991119, 93]);

    impl_test!(-13 - [13] = -[26]);

    impl_test!(-958253824 - [958253824] = -[916507648, 1]);

    // impl_test!(11633491985251901031 - [1032340950] = -[219560081, 633491984, 11]);

    impl_test!(132340950 - [132340950] = [0]);

    impl_test!(-38114338160860411 - [35540405] = -[196400816, 38114338]);
    impl_test!(601033208449587446 - [449587446] = [0, 601033208]);

    impl_test!(999999999999999999 - [380292085] = [619707914, 999999999]);
    impl_test!(1000000000444635166 - [973719306] = [470915860, 999999999]);
    impl_test!(1000000003767677855 - [984077921] = [783599934, 000000002, 1]);
    // i64::MAX
    impl_test!(9223372036854775807 - [032340950, 1] = [822434857, 223372035, 9]);
    impl_test!(9223372036854775807 - [933375281] = [921400526, 223372035, 9]);
    impl_test!(
        9223372036854775807 - [945672187, 270605744, 453822838, 776256045, 8260] =
            -[90896380, 47233708, 453822829, 776256045, 8260]
    );
    impl_test!(
        9223372036854775807 - [003594813, 537760215, 712063757, 040691711, 5178] =
            -[148819006, 314388178, 712063748, 40691711, 5178]
    );

    // impl_test!(-16495329599712012293 - [958253824] = -[670266117, 495329600, 16]);
    // impl_test!(16495329599712012293 - [958253824] = -[753758469, 495329598, 16]);
    // impl_test!(9223372036854775808 - [958253824] = -[753758469, 495329598, 16]);

    impl_test!(2147483648 - [944215022, 2] = -[796731374]);
    impl_test!(-2147483648 - [944215022, 2] = -[91698670, 5]);

    // impl_test!(
    //      - [999999999, 1] = -[1, 1]
    // );

    impl_test!(396984238 - [752594762, 901176759, 857429] = -[355610524, 901176759, 857429]);

    impl_test!(770949474 - [239227606, 633] = -[468278132, 632]);

    impl_test!(-845976267 - [624860973] E -6 = -[891860973, 845976] E -6);
    impl_test!(-475148789 - [398317042, 433486196] E -20 = -[398317042, 433486196, 514878900, 47] E -20);

    impl_test!(109530412037944878 - [604710212, 882598735, 7184598] E -9 = [395289788, 155346142, 102345813] E -9);

    // impl_test!(-475148789 - [398317042, 433486196] E -20 = -[398317042, 433486196, 514878900, 47] E -20);
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
