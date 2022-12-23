//!
//! Addition algorithms BigDigit
//!

use std::num::NonZeroUsize;
use std::ops::Not;

use crate::bigdigit::{
    self,
    BigDigit,
    BigDigitVec,
    BigDigitSplitterIter,
    BigDigitSliceSplitterIter,
    DigitInfo,
    DigitInfoRef,
    BigDigitLoc,
    align_with_insignificance,
    align_with_shift
};
use crate::arithmetic::subtraction;

use crate::context::{Context, RoundingMode};
use crate::Sign;

use num_integer::div_rem;


/// Add two (aligned) slices of BigDigits
#[inline]
pub(crate) fn add_digit_slices(a: &[BigDigit], b: &[BigDigit]) -> BigDigitVec {
    let mut result = BigDigitVec::with_capacity(a.len().max(b.len() + 1));
    add_digit_slices_into(a, b, &mut result);
    return result;
}

/// Fill DigitVec with sum of digits
#[inline]
pub(crate) fn add_digit_slices_into(a: &[BigDigit], b: &[BigDigit], v: &mut BigDigitVec) {
    // a is longer of the vectors
    let (a, b) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    v.clear_and_reserve(a.len() + 1);
    extend_digit_slice_sum_into(a, b, v);
}

/// Extend DigitVec with sum of digits, digits are aligned
#[inline]
pub(crate) fn extend_digit_slice_sum_into(a: &[BigDigit], b: &[BigDigit], v: &mut BigDigitVec) {
    let (a, b) = if a.len() >= b.len() { (a, b) } else { (b, a) };
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

/// Fill BigDigitVec with (potentially unaligned) digits
///
/// digit_shift is the difference between the digit exponents
///
/// a*10^A + b^B == add_digit_slices_with_offset_into(a, b, A - B, v)
///
///
#[inline]
pub(crate) fn add_digit_slices_with_offset_into(
    a: &[BigDigit],
    b: &[BigDigit],
    digit_shift: i64,
    result: &mut BigDigitVec,
) {
    if digit_shift == 0 {
        return add_digit_slices_into(a, b, result);
    }

    // swap a and b such that digit_shift is positive
    if digit_shift < 0 {
        return add_digit_slices_with_offset_into(b, a, -digit_shift, result);
    }

    let (skip, a_offset) = div_rem(
        digit_shift as usize, bigdigit::MAX_DIGITS_PER_BIGDIGIT
    );

    result.extend_from_slice(&b[..skip]);

    if a_offset == 0 {
        return extend_digit_slice_sum_into(a, &b[skip..], result);
    }

    let mut aligned_a_digits = BigDigitSplitterIter::from_slice_shifting_left(
        &a, a_offset
    );
    let b_digits = b[skip..].iter();

    let mut carry = BigDigit::zero();
    for b_digit in b_digits {
        let sum = if let Some(shifted_digit) = aligned_a_digits.next() {
            b_digit.add_with_carry(&shifted_digit, &mut carry)
        } else {
            b_digit.add_carry(&mut carry)
        };
        result.push(sum);
    }

    result.extend_with_carried_sum(aligned_a_digits, carry);
}

#[cfg(test)]
#[allow(overflowing_literals)]
#[allow(unreachable_patterns)]
mod test_add_digit_slices_with_offset_into {
    use super::*;
    use crate::bigdigit::BIG_DIGIT_RADIX;

    include!("../test_macros.rs");

    macro_rules! impl_test {
        () => {
            |a, a_shift, b, b_shift, expected: &[BigDigit]| {
                let mut sum = BigDigitVec::new();
                add_digit_slices_with_offset_into(a, b, a_shift as i64 - b_shift, &mut sum);
                assert_eq!(sum.as_ref(), expected);

                let mut commutes = BigDigitVec::new();
                add_digit_slices_with_offset_into(b, a, b_shift - a_shift, &mut commutes);
                assert_eq!(commutes.as_ref(), expected);
            }
        };
        ([$($a:literal),*]/$a_scale:literal [$($b:literal),*]/$b_scale:literal == [$($c:literal),*]) => {
            let do_test = impl_test!();
            call_func!(do_test, [$($a),*]/$a_scale [$($b),*]/$b_scale [$($c),*]);
        };
    }

    #[test]
    fn test_0_0() {
        impl_test!([0]/0 [0]/0 == [0]);
    }

    /// 6277.82148603152
    ///    4.72957163297543182607
    //         |       |        |
    ///
    #[test]
    fn test_627782148603152e11_472957163297543182607e20() {
        impl_test!(
            [148603152, 627782]/-11
            [543182607, 957163297, 472]/-20
         == [543182607, 105766449, 628255]
        );
    }


    //   234666915454145414.8760506308
    // +                123.2629070859583263547519927
    //         |        |         |        |        |
    #[test]
    fn test_2346669154541454148760506308e0_1232629070859583263547519927e15() {
        impl_test!(
            [760506308, 541454148, 346669154, 2]/-10
            [547519927, 859583263, 232629070, 1]/-25
         == [547519927, 167583263, 381389577, 154541455, 2346669]
        );
    }

    //               59503150.88766999999994303187
    // + 16907800067882600606.59028336
    //      |        |         |        |        |
    #[test]
    fn test_5950315088766999999994303187e20_1690780006788260060659028336e8() {
        impl_test!(
            [994303187, 766999999, 950315088, 5]/-20
            [659028336, 788260060, 690780006, 1]/-8
         == [994303187, 795335999, 210375747, 780006794, 1690]
        );
    }

    //                 3150.9975698
    // + 22540435457
    //         |        |         |
    #[test]
    fn test_31509975698eneg7_22540435457e7() {
        impl_test!(
            [509975698, 31]/-7
            [540435457, 22]/7
         == [509975698, 545700031, 2254043]
        );
    }

    #[test]
    fn test_2134139897064eneg7_1018939eneg6() {
        impl_test!(
            [139897064, 2134]/-10
            [1018939]/-6
         == [329287064, 2144]
        );
    }
}

/// Calculate a + b, to the requested precision
///
#[allow(unreachable_code)]
pub(crate) fn add_digits_into(
    a: &DigitInfo,
    b: &DigitInfo,
    precision: NonZeroUsize,
    rounding: RoundingMode,
    result: &mut DigitInfo
) {
    // route to some implemenation
    match (a.sign, b.sign, a.scale > b.scale) {
        (Sign::Plus, Sign::Minus, _) => {
            subtraction::_call_subtract_digits_into_impl(
                a.as_ref(), b.neg_ref(), precision, rounding, result
            )
        }
        (Sign::Minus, Sign::Plus, _) => {
            subtraction::_call_subtract_digits_into_impl(
                b.as_ref(), a.neg_ref(), precision, rounding, result
            )
        }
        (Sign::NoSign, _, _) => {
            result.copy_with_precision(b.as_ref(), precision, rounding)
        }
        (_, Sign::NoSign, _) => {
            result.copy_with_precision(a.as_ref(), precision, rounding)
        }
        (_, _, true) => {
            add_digits_into_impl(b.as_ref(), a.as_ref(), precision, rounding, result)
        }
        (_, _, false) => {
            add_digits_into_impl(a.as_ref(), b.as_ref(), precision, rounding, result)
        }
    }
}

/// Actual implementation of add_digits_into_impl
///
#[allow(unreachable_code)]
pub(crate) fn add_digits_into_impl<'a, 'b>(
    a: DigitInfoRef<'a>,
    b: DigitInfoRef<'b>,
    precision: NonZeroUsize,
    rounding: RoundingMode,
    result: &mut DigitInfo
) {
    use std::cmp::Ordering::*;

    debug_assert_eq!(a.sign, b.sign);
    debug_assert!(a.scale <= b.scale);

    if a.digits.is_zero() {
        result.copy_with_precision(b, precision, rounding);
        return;
    }
    if b.digits.is_zero() {
        result.copy_with_precision(a, precision, rounding);
        return;
    }

    result.sign = a.sign;

    // digit positions relative to end of 'a'
    //
    //       aaa.aaaa
    //      │       └─> a-end-pos=0 (always)
    //      └────────> a-start-pos=7
    //   bbbbbbbb.b
    //  │         └─> b-end-pos=3
    //  └──────────> b-start-pos=12
    //
    let b_end_pos = (b.scale - a.scale) as usize;
    let b_start_pos = b.digits.count_digits() + b_end_pos;
    let a_start_pos = a.digits.count_digits();

    let max_start_pos = usize::max(a_start_pos, b_start_pos);

    // precision is greater than total number of digits (including potential rounding/overflow)
    // so we can do 'simple' addition
    if max_start_pos < precision.get() {
        result.scale = a.scale;
        let (a_skip, b_shift) = BigDigitVec::digit_position_to_bigdigit_index_offset(b_end_pos);
        let b_digits = BigDigitSplitterIter::from_slice_shifting_left(&b.digits, b_shift);
        if a_skip < a.digits.len() {
            let (only_a, a_digits) = a.digits.split_at(a_skip);
            result.digits.extend_from_slice(&only_a);
            let a_digits = BigDigitSplitterIter::from_slice_shifting_left(&a_digits, 0);
            // 'output' of carry is ignored, we are sure there's no overflow
            let mut carry = BigDigit::zero();
            _impl_add_digits(a_digits, b_digits, &mut result.digits, &mut carry);
        } else {
            // a & b are "disjoint" - we just copy the values
            result.digits.extend_from_slice(&a.digits);
            result.digits.resize(a_skip, BigDigit::zero());
            b_digits.extend_vector(&mut result.digits);
        }

        debug_assert!(result.digits.count_digits() <= precision.get());
        return;
    }

    // position relative to end of 'a' between insiginificatnt and
    // significant digits, aka the "rounding point"
    let significant_pos = max_start_pos - precision.get();

    // removing 'n' digits from a has the effect of decreasing scale by 'n'
    result.scale = a.scale + significant_pos as i64;

    let (
        mut a_digits,
        a_insignificant_count,
        skipped_a_digits,
    ) = align_with_insignificance(
        a.digits.as_slice(), significant_pos, significant_pos.min(b_end_pos)
    );

    let (
        mut b_digits,
        b_loc,
    ) = align_with_shift(b.digits.as_slice(), significant_pos, b_end_pos);

    let (
        pos_idx, pos_offset
    ) = BigDigitVec::digit_position_to_bigdigit_index_offset(significant_pos);
    let (
        a_start_idx, a_start_offset
    ) = BigDigitVec::digit_position_to_bigdigit_index_offset(a_start_pos - 1);

    let _a_bigdigit_count = a_start_idx + (a_start_offset > 0) as usize;

    let trailing_zeros;
    let rounding_digit0;
    let rounding_digit1;
    let rounding_digit2;

    let d0;

    let mut carry = BigDigit::zero();
    let mut rounding_carry = BigDigit::zero();

    // let all_a_digits_skipped = a_digit_slice.len() == 0;
    let all_a_digits_skipped = skipped_a_digits.len() == a.digits.len();

    match b_loc {
        // all 'b' digits significant no 'a' digits significant
        BigDigitLoc::Significant(trailing_zero_count) if all_a_digits_skipped => {
            // handle unlikely case of insignificant 'a' digit providing the
            // last insignificant digit:
            //        xaaaaaaa
            //  bbbbbxx
            //        ^
            if pos_offset == 0 && a_start_idx == pos_idx - 1 {
                let (hi_digit, trailing_digits) = a.digits.as_slice().split_last().unwrap();
                let (hi, remainder) = hi_digit.split_highest_digit();
                trailing_zeros = remainder == 0 && trailing_digits.iter().all(BigDigit::is_zero);
                rounding_digit0 = hi;
            } else {
                trailing_zeros = false;
                rounding_digit0 = 0;
            };
            let b0 = if trailing_zero_count == 0 {
                b_digits.next().unwrap()
            } else {
                BigDigit::zero()
            };
            d0 = b0.as_digit_base();

            (
                rounding_digit2,
                rounding_digit1
            ) = rounding_digits(b0);

            let rounded_b0 = make_rounded_value(
                b0,
                rounding,
                result.sign,
                (rounding_digit1, rounding_digit0),
                trailing_zeros,
                &mut rounding_carry,
                &mut carry,
            );
            result.digits.push(rounded_b0);
            if trailing_zero_count > 0 {
                result.digits.resize(trailing_zero_count, BigDigit::zero());
            }
            b_digits.extend_vector(&mut result.digits);
        }
        // Some 'b' digits insignificant & all 'a' digits (very) insignificant
        BigDigitLoc::Insignificant(idx) if all_a_digits_skipped => {
            for _ in 1..idx.get() {
                b_digits.next().unwrap();
            }
            let b_insig = b_digits.next().unwrap();
            (rounding_digit0, _) = b_insig.split_highest_digit();
            trailing_zeros = false;
            let b0 = b_digits.next().unwrap();
            d0 = b0.as_digit_base();
            (
                rounding_digit2,
                rounding_digit1
            ) = rounding_digits(d0);

            let rounded_b0 = make_rounded_value(
                b0,
                rounding,
                result.sign,
                (rounding_digit1, rounding_digit0),
                trailing_zeros,
                &mut rounding_carry,
                &mut carry,
            );
            result.digits.push(rounded_b0);
            b_digits.extend_vector_adding_carry(carry, &mut result.digits);
        }
        // All 'b' digits are significant & 'a' has some significant digits
        BigDigitLoc::Significant(trailing_b_zero_count) => {
            if a_insignificant_count == 0 {
                // hande case where highest insignificant digits is skipped
                match skipped_a_digits.split_last() {
                    Some((insig_a, rest)) => {
                        let (hi, remainder) = insig_a.split_highest_digit();
                        trailing_zeros = remainder == 0 && rest.iter().all(BigDigit::is_zero);
                        rounding_digit0 = hi;
                    }
                    None => {
                        rounding_digit0 = 0;
                        trailing_zeros = true;
                    }
                }
            } else {
                let a_insig = a_digits.next().unwrap();
                let (hi, remainder) = a_insig.split_highest_digit();
                trailing_zeros = remainder == 0 && skipped_a_digits.iter().all(BigDigit::is_zero);
                rounding_digit0 = hi;
            }

            let a0 = a_digits.next().unwrap_or(BigDigit::zero());
            let b0 = if trailing_b_zero_count == 0 {
                b_digits.next().unwrap()
            } else {
                BigDigit::zero()
            };
            let sum0 = BigDigit::add_with_carry(&a0, &b0, &mut carry);
            d0 = sum0.as_digit_base();

            (
                rounding_digit2,
                rounding_digit1
            ) = rounding_digits(d0);

            let rounded_d0 = make_rounded_value(
                sum0,
                rounding,
                result.sign,
                (rounding_digit1, rounding_digit0),
                trailing_zeros,
                &mut rounding_carry,
                &mut carry,
            );
            result.digits.push(rounded_d0);

            // handle case of zeros between a & b digits
            for _ in 1..trailing_b_zero_count {
                match a_digits.next() {
                    None => {
                        result.digits.push(carry);
                        carry = BigDigit::zero();
                        result.digits.resize(trailing_b_zero_count, BigDigit::zero());
                        break;
                    },
                    Some(mut digit) => {
                        digit.add_assign_carry(&mut carry);
                        result.digits.push(digit);
                    },
                }
            }
            _impl_add_digits(a_digits, b_digits, &mut result.digits, &mut carry);
        }
        // 'b' has insignificant digits and a has significance
        BigDigitLoc::Insignificant(b_idx) => {
            let b_insignificant_count = b_idx.get();

            // insignificant (summed) values are zero
            let mut summed_trailing_zeros = true;

            // 'a' may have one more insignificant digit than 'b'
            // (if there were more than one we would have included
            // that digit in the skipped_digits slice)
            if a_insignificant_count > b_insignificant_count {
                debug_assert_eq!(b_insignificant_count + 1, a_insignificant_count);
                let skipped_a_digit = a_digits.next().unwrap();
                summed_trailing_zeros &= skipped_a_digit.is_zero();
            }

            // sum insignificant digits, tracking carry & trailing zeros
            for _ in 1..b_insignificant_count {
                match (a_digits.next(), b_digits.next()) {
                    (Some(a_digit), Some(b_digit)) => {
                        let sum_digit = a_digit.add_with_carry(&b_digit, &mut carry);
                        summed_trailing_zeros &= sum_digit.is_zero();
                    }
                    (Some(digit), None) | (None, Some(digit)) => {
                        let next_digit = digit.add_carry(&mut carry);
                        summed_trailing_zeros &= next_digit.is_zero();
                    }
                    (None, None) => { unreachable!() }
                }
            }

            // get final insignificant sum for digit right of rounding point
            let insig_a = a_digits.next().unwrap_or(BigDigit::zero());
            let insig_b = b_digits.next().unwrap_or(BigDigit::zero());
            let insig_s = BigDigit::add_with_carry(&insig_a, &insig_b, &mut carry);

            let (high_digit, remainder) = insig_s.split_highest_digit();
            rounding_digit0 = high_digit;

            // first significant digit gets rounded
            let a0 = a_digits.next().unwrap_or(BigDigit::zero());
            let b0 = b_digits.next().unwrap_or(BigDigit::zero());
            let sum0 = BigDigit::add_with_carry(&a0, &b0, &mut carry);
            d0 = sum0.as_digit_base();

            trailing_zeros = remainder == 0 && summed_trailing_zeros && skipped_a_digits.iter().all(BigDigit::is_zero);
            (
                rounding_digit2,
                rounding_digit1
            ) = rounding_digits(d0);

            let rounded_d0 = make_rounded_value(
                sum0,
                rounding,
                result.sign,
                (rounding_digit1, rounding_digit0),
                trailing_zeros,
                &mut rounding_carry,
                &mut carry,
            );
            result.digits.push(rounded_d0);
            _impl_add_digits(a_digits, b_digits, &mut result.digits, &mut carry);
        }
    }

    let overflowed = carry.is_one() || result.digits.count_digits() > precision.get();
    if overflowed {
        let rounding_pair = (rounding_digit2, rounding_digit1);
        handle_overflow(
            d0,
            rounding,
            rounding_pair,
            trailing_zeros && rounding_digit0 == 0,
            rounding_carry,
            result
        );
    }

    debug_assert_eq!(result.count_digits(), precision.get() as usize);
}


/// Adds the digit iterators together into sum
///
/// Non-standard behavior: the carry is not cleared after being added to the sum.
///     This is for the optimization that if a carry is one, we have certainly overflowed
///     and do not need to count digits.
///
fn _impl_add_digits<'a>(
    mut a_digits: BigDigitSplitterIter<'a, std::slice::Iter<'a, BigDigit>>,
    mut b_digits: BigDigitSplitterIter<'a, std::slice::Iter<'a, BigDigit>>,
    sum: &mut BigDigitVec,
    carry: &mut BigDigit,
)
{
    loop {
        match (a_digits.next(), b_digits.next()) {
            (Some(a_digit), Some(b_digit)) => {
                sum.push(
                    BigDigit::add_with_carry(&a_digit, &b_digit, carry)
                );
            }
            (Some(a_digit), None) => {
                sum.push(a_digit.add_carry(carry));
                a_digits.extend_vector_adding_carry(*carry, sum);
                return;
            }
            (None, Some(b_digit)) => {
                sum.push(b_digit.add_carry(carry));
                b_digits.extend_vector_adding_carry(*carry, sum);
                return;
            }
            (None, None) => {
                if !carry.is_zero() {
                    sum.push(*carry);
                }
                return;
            }
        }
    }
}


#[cfg(test)]
#[allow(non_snake_case)]
mod test_add_digits_into {
    use super::*;
    use crate::bigdigit::DigitInfo;
    use crate::bigdigit::BigDigitVec;
    use crate::bigdigit::BIG_DIGIT_RADIX;

    include!("../test_macros.rs");

    macro_rules! impl_case {
        ( $prec:literal :: $mode:ident => $($s:literal)+ E $s_exp:literal ) => {
            paste! {
                #[test]
                fn [< prec_ $prec _round_ $mode >]() {
                    let (a, b) = build_case_input();
                    let mut result = DigitInfo::default();
                    let mode = RoundingMode::$mode;
                    let precision = std::num::NonZeroUsize::new($prec).unwrap();
                    add_digits_into(&a, &b, precision, mode, &mut result);
                    let expected = digit_info!($($s)* E $s_exp);
                    assert_eq!(result, expected);
                }
            }
        };
        ( $prec:literal :: $mode:ident $(, $modes:ident)+ => $($s:literal)+ E $s_exp:literal ) => {
            impl_case!($prec :: $mode => $($s)* E $s_exp );
            impl_case!($prec :: $($modes),* => $($s)* E $s_exp );
        };
        ( $prec:literal ::
            $($amodes:ident),+ => $($as:literal)+ E $as_exp:literal ;
            $($bmodes:ident),+ => $($bs:literal)+ E $bs_exp:literal
        ) => {
            impl_case!($prec :: $($amodes),* => $($as)* E $as_exp );
            impl_case!($prec :: $($bmodes),* => $($bs)* E $bs_exp );
        };
        ( $prec:literal :: $($amodes:ident),+ => $($as:literal)+ E $as_exp:literal
                         : $($bmodes:ident),+ => $($bs:literal)+ E $bs_exp:literal
        ) => {
            impl_case!($prec :: $($amodes),* => $($as)* E $as_exp );
            impl_case!($prec :: $($bmodes),* => $($bs)* E $bs_exp );
        };
    }

    macro_rules! case_input {
        ( $($a:literal)+ E $a_exp:literal + $($b:literal)+ E $b_exp:literal ) => {
            fn build_case_input() -> (DigitInfo, DigitInfo) {
                let a = digit_info!($($a)* E $a_exp);
                let b = digit_info!($($b)* E $b_exp);
                (a, b)
            }
        };
    }

    mod case_32368_E_neg1_73708_E_0 {
        use super::*;

        case_input! {
               32368 E -1
            + 73708 E 0
        }

        impl_case!(5 :: Up, Ceiling => 76945 E 0; Down => 76944 E 0);
        impl_case!(6 :: Up, Ceiling => 769448 E -1; Down => 769448 E -1);
        impl_case!(7 :: Up, Ceiling, Down  => 769448 E -1);
        impl_case!(8 :: Up, Ceiling, Down  => 769448 E -1);
    }

    mod case_11332585891914_E_neg100_98868715_E_neg4 {
        use super::*;

        case_input! { 11332 585891914 E -100 + 98868715 E -4 }

        impl_case!(8 :: Up => 98868716 E -4;
                        Down => 98868715 E -4 );
        impl_case!(9 :: Up => 988687151 E -5;
                        Down => 988687150 E -5 );
        impl_case!(10 :: Up => 9 886871501 E -6;
                        Down => 9 886871500 E -6 );
        impl_case!(50 :: Up => 98868 715000000 000000000 000000000 000000000 000000001 E -46);

        impl_case!(91 :: Up => 9 886871500 000000000 000000000 000000000 000000000 000000000 000000000 000000000 000000000 000000002 E -87);
        impl_case!(92 :: Up => 98 868715000 000000000 000000000 000000000 000000000 000000000 000000000 000000000 000000000 000000012 E -88);

        impl_case!(97 :: Up =>  9886871 500000000 000000000 000000000 000000000 000000000 000000000 000000000 000000000 000000000 001133259 E -93;
                        Down => 9886871 500000000 000000000 000000000 000000000 000000000 000000000 000000000 000000000 000000000 001133258 E -93 );
        impl_case!(99 :: Up => 988687150 000000000 000000000 000000000 000000000 000000000 000000000 000000000 000000000 00000000 113325859 E -95;
                        Down => 988687150 000000000 000000000 000000000 000000000 000000000 000000000 000000000 000000000 00000000 113325858 E -95 );
        impl_case!(100 :: Up => 9 886871500 000000000 000000000 000000000 000000000 000000000 000000000 000000000 000000000 000000001 133258590 E -96;
                        Down => 9 886871500 000000000 000000000 000000000 000000000 000000000 000000000 000000000 000000000 000000001 133258589 E -96 );
    }

    mod case_42267449_E_neg1_82651114_E_0 {
        use super::*;

        //  422.67449
        // 8265.1114x
        // 8765 43210

        //    4.2267449
        // 8265.1114xxx
        // 0987 6543210
        case_input! { 42267449 E -5 + 82651114 E -4 }

        impl_case!(8 :: Up => 86877859 E -4;
                        Down => 86877858 E -4);
    }


    mod case_780728539486935E_neg6_195622692238e_neg4  {
        use super::*;

        case_input! { 780728 539486935 E -6 + 195 622692238 E -4 }

        // [ a₁   ][    a₀    ]
        // [780728][539.486935]
        //  [195][62269.2238]
        //  [ b₁][     b₀   ]
        //
        // a: (0, 14) max_start_pos = 14
        // b: (2, 13)
        //

        // prec=11   -> prec_pos = 14 - 11 = 3
        // [78][0728539.48][6935xxxxx]
        //  [1][9562269.22][38xxxxxxx]
        // |-------11-----|

        // prec=10   -> prec_pos = 14 - 10 = 4
        // [7][80728539.4][86935xxxx]
        //    [19562269.2][238xxxxxx]
        // |-------10----|
        //
        //              [1][107350000]
        //   [7][807285394]
        //      [195622692]
        //
        //   [1][002908087][107350000]
        //   [7]
        //

        // prec=9   -> prec_pos = 14 - 9 + 1 = 6 -> (0,6)
        //
        // [780728539.][486935xxx]
        //  [19562269.][2238xxxxx]
        //  |---9---|
        impl_case!(11 :: Down => 80 029080871 E -2);
        impl_case!(10 :: Up => 8 002908088 E -1;
                        Down => 8 002908087 E -1);

        impl_case!(9 :: Up => 800290809 E 0;
                        Down => 800290808 E 0);
    }

    mod case_21182876230333040678_E_neg7_41979135927194856497_E_neg17 {
        use super::*;

        //           419.79135927194856497
        // 2118287623033.3040678     |
        // ↑29      ↑20        ↑10   |   ↑0
        // prec: |7    |13      |21  |26

        //             [a₂][    a₁    ][    a₀   ]
        //             [41][9.79135927][194856497]
        // [21][182876230][33.3040678]
        // [b₂][   b₁    ][     b₀   ]

        // prec=20
        //             [4][19.7913592]~[719485649][7...]
        // [21][182876230][33.3040678]~[xxxxxxxxx]
        // |-----------------20------|

        // prec=19
        //               [419.791359]~[271948564][97...]
        // [2][118287623][033.304067]~[8xxxxxxxx]
        // |-----------------19-----|

        // prec=18
        //            [ 419.79135]~[927194856]497
        // [211828762][3033.30406]~[78xxxxxxx]
        // |--------------18-----|

        // prec=17
        //             [419.7913]~[592719485][6497..]
        // [21182876][23033.3040]~[678xxxxxx]
        // |--------------17----|

        // prec=11
        //             [4][19.7913592][719485649][7]
        // [21][182876230][33.3040678]
        // |----11-------|

        // 21182876, 234530954, 270719486

        case_input! {
                21 182876230 333040678 E -7
              +            41 979135927 194856497 E -17
        }

        // prec=26, pos=4
        //           [  419.7913][592719485][6497]
        // [21182876][23033.3040][678______]
        // |---------------------26--------|
        impl_case!(26 :: Up => 21182876 234530954 270719486 E -13;
                         Down => 21182876 234530954 270719485 E -13);

        // prec=23, pos=7
        //        [     419.7][913592719][4856497__]
        // [21182][87623033.3][040678___]
        // |------------------23--------|
        impl_case!(23 :: Up => 21182 876234530 954270720 E -10;
                         Down => 21182 876234530 954270719 E -10);
        impl_case!(22 :: Up => 2118 287623453 095427072 E -9;
                         Down => 2118 287623453 095427071 E -9);
        impl_case!(21 :: Up => 211 828762345 309542708 E -8;
                         Down => 211 828762345 309542707 E -8);
        impl_case!(20 :: Up => 21 182876234 530954271 E -7;
                         Down => 21 182876234 530954270 E -7);

        // prec=19
        //               [419.791359]~27194856497
        // [2][118287623][033.304067]~8
        // |-----------------19-----|
        //                   ^17      ^10       ^0
        //
        //               [419.791359]~[271948564][97_______]
        // [2][118287623][033.304067]~[8________]
        // |-----------------19-----|
        //                             ^17                ^0
        //
        //                              [194856497]
        //               [419.791359]~[27_______]
        // [2][118287623][033.304067]~[8________]
        // |-----------------19-----|
        //               ^17           ^8      ^0
        //

        impl_case!(19 :: Up => 2 118287623 453095428 E -6;
                         Down => 2 118287623 453095427 E -6);

        // prec=18
        //               [419.79135]~[927194856][497______]
        // [2][11828762][3033.30406]~[78_______]
        // |----------------18-----|
        //                            ^17               ^0
        //
        //                              [194856497]
        //               [419.79135]~[927______]
        // [2][118287623][033.30406]~[78_______]
        // |----------------18-----|
        //                            ^8
        //

        impl_case!(18 :: Up => 211828762 345309543 E -5;
                         Down => 211828762 345309542 E -5);
        impl_case!(17 :: Up => 21182876 234530955 E -4;
                         Down => 21182876 234530954 E -4);
        impl_case!(16 :: Up => 2118287 623453096 E -3;
                         Down => 2118287 623453095 E -3);
        impl_case!(15 :: Up => 211828 762345310 E -2;
                         Down => 211828 762345309 E -2);
        // impl_case!(12 :: Up => 21 182876235 E 2);

        // prec=11

        //           419.79135927194856497
        // 2118287623033.3040678
        // ↑29      ↑20        ↑10       ↑0
        //
        //             [41][9.79135927][194856497]
        // [21][182876230][33.3040678]
        //
        //             [4]~[19.7913592][719485649][7________]
        // [21][182876230]~[33.3040678]
        // |----11-------|
        //                              ^17                ^0
        //
        //                              [194856497]
        //             [4]~[19.7913592][7________]
        // [21][182876230]~[33.3040678]
        // |----11-------|
        //                  ^17                 ^0
        impl_case!(11 :: Up => 21 182876235 E 2);

        //               ~[419.791359][271948564][97________]
        // [2][118287623]~[033.304067][8________]
        // |----10------|
        //
        //                              [194856497]
        //               ~[419.791359][27_______]
        // [2][118287623]~[033.304067][8________]
        // |----10------|
        impl_case!(10 :: Up => 2 118287624 E 3);
    }

    mod case_65105089065643509134639_E_neg7_83049409402376021061_E_neg34 {
        use super::*;
        case_input! {
            65105 089065643 509134639 E -7
          + 83 049409402 376021061 E -27
        }

        impl_case!(15 :: Up => 651050 890656436 E 1 ;
                         Down => 651050 890656435 E 1);
        impl_case!(50 :: Up, Down => 6510508 906564350 913463983 049409402 376021061 E -27 );
    }

    mod case_178450147E_neg3_2392081E6 {
        use super::*;
        case_input! { 178450147 E -3 + 2392081 E 6 }

        impl_case!( 18 :: Up => 2392081 178450147 E -3 );
    }

    mod case_65684331366963425850801476994Eneg28_29702871998771040e16 {
        use super::*;

        // b_end = 12

        case_input! {
            65 684331366 963425850 801476994 E -28
          + 29702871 998771040 E -16
        }

        // sig-a-pos: 20
        // a-padding: 27 - 20 = 7
        //
        //   |         |         |         |
        //  656843313 669634258 508014769 94_______
        //  297028719 98771040_
        //          *        |
        //          |        b_end' = 12 + 7 = 19
        //          |
        //          | sig_pos = 20
        //          | sig_pos' = 20 + 7 = 27
        //
        //
        //                       {801476994}
        //   |         |         |
        //  656843313 669634258 50_______
        //  297028719 98771040_
        //          *        |
        //          |        |b_end=3, b_end'=3+7=10
        //          pos=11
        //          pos'=11+7=18
        //
        impl_case!(9 :: Up => 953872034 E -8 );

        // sig-a-pos: 29 - 11 = 18
        // a-padding: 18 - 18 = 0
        //
        //   |         |         |         |
        //  65 684331366 963425850 801476994
        //  29 702871998 771040___
        //             *      |
        //             |      b_end' = 12 + 0 = 12
        //             |
        //             | sig_pos = 18
        //             | sig_pos' = 18 + 0 = 18
        impl_case!(11 :: Up => 95 387203366 E -10 );

        // sig-a-pos: 14
        // a-padding: 18 - 14 = 4
        //
        //   |         |         |         |
        //  656843 313669634 258508014 76994____
        //  297028 719987710 40_______
        //
        //  656843 313669634 25850____
        //  297028 719987710 40_______
        //
        impl_case!(15 :: Up => 953872 033657345 E -14 );

        // sig-a-pos: 13
        // a-padding: 18 - 13 = 5
        //
        //   |         |         |         |
        //  6568433 136696342 585080147 6994_____
        //  2970287 199877104 0________
        //          |       * |
        //                  | b_end' = 12 + 5 = 17
        //                  |
        //                  sig_pos = 13
        //                  sig_pos' = 13 + 5 = 18
        //
        // a removing insignificant digits
        //
        //   |         |         |
        //  6568433 136696342 5850_____
        //  2970287 199877104 0________
        //          |       * |
        //                  | b_end' = 12 + 5 = 17
        //                  |
        //                  sig_pos = 13
        //                  sig_pos' = 13 + 5 = 18
        //
        impl_case!(16 :: Up => 9538720 336573447 E -15 );


        // sig-a-pos: 29 - 17 = 12
        // a-padding: 18 - 12 = 6
        //
        //   |         |         |         |
        //  65684331 366963425 850801476 994______
        //  29702871 998771040
        //          |        *
        //                   | b_end' = 12 + 6 = 18
        //                   |
        //                   sig_pos = 12
        //                   sig_pos' = 12 + 6 = 18
        //
        //   |         |         |
        //  65684331 366963425 850______
        //  29702871 998771040
        //
        // [6.5][684331366][963425850][801476994]
        // [2.9702871][998771040]
        // |------------17-----|
        //
        //
        //  12 /% 9 -> (1, 3) <- starting bottom 3
        //
        //  [6.5684331][366963425][850801476][994______]
        //  [2.9702871][998771040]
        //
        //  b_end starts at (1,3) <- we can skip 1 a digit
        //                           {801476994}
        //  [6.5684331][366963425][850______]
        //  [2.9702871][998771040]
        //

        impl_case!(17 :: Up => 95387203 365734466 E -16 );
    }


    mod case_137681612112971086Eneg9_1e20 {
        use super::*;

        case_input! { 137681612 112971086 E -9 + 1 E 20 }

        impl_case!(31 :: Up => 100 000000000 137681612 112971086 E -9 );
        impl_case!(30 :: Up => 100 000000000 137681612 112971086 E -9 );
        impl_case!(29 :: Up => 10 000000000 013768161 211297109 E -8 );
        impl_case!(20 :: Up => 10 000000000 013768162 E 1 );
    }

    mod case_220131999_439298761Eneg9 {
        use super::*;

        case_input! {
            220131999 E 0
          +  439298761 E -9
        }

        impl_case!(5 :: Up => 22014 E 4);
        impl_case!(8 :: Up => 22013200 E 1);
        impl_case!(9 :: Up => 220132000 E 0);
        impl_case!(10 :: Up => 2 201319995 E -1
                       : Down => 2 201319994 E -1);
        impl_case!(17 :: Up => 22013199 943929877 E -8
                       : Down => 22013199 943929876 E -8);
        impl_case!(18 :: Up, Down => 220131999 439298761 E -9);
        impl_case!(20 :: Up, Down => 220131999 439298761 E -9);
        impl_case!(1000 :: Up, Down => 220131999 439298761 E -9);
    }

    mod case_43397981256Eneg2_70216732530Eneg18 {
        use super::*;

        case_input! {
            43 397981256 E -2
          +  70 216732530 E -18
        }

        impl_case!(19 :: Up => 4 339798125 600000703 E -10);
        impl_case!(25 :: Up => 4339798 125600000 702167326 E -16);
    }

    mod case_46321925_3004847Eneg45 {
        use super::*;

        case_input! {
            46321925 E 0
          +  3004847 377142081 418295693 E -45
        }

        impl_case!(19 :: Up => 4 632192500 000000001 E -11);
        impl_case!(25 :: Up => 4632192 500000000 000000001 E -17);

        impl_case!(34 :: Up => 4632192 500000000 000000000 000300485 E -26);
        impl_case!(35 :: Up => 46321925 000000000 000000000 003004848 E -27);
        impl_case!(36 :: Up => 463219250 000000000 000000000 030048474 E -28);
        impl_case!(37 :: Up => 4 632192500 000000000 000000000 300484738 E -29);
    }

    mod case_137708802_439298761Eneg9 {
        use super::*;

        case_input! {
            137708802 E 0
          +  250057873 E -10
        }

        //  137708802
        // +         0250057873
        //  ^        ^        ^
        //  ^        9        0

        impl_case!(5 :: Up => 13771 E 4);
        impl_case!(9 :: Up => 137708803 E 0);
        impl_case!(10 :: Up => 1 377088021 E -1);

        //  137708802
        // +         0250057873
        //  ^18      ^9       ^0
        //
        // shift right 8
        //
        //  137708802
        // +         02
        //   ^      ^ ^
        //   9      2 0
        //
        impl_case!(11 :: Up => 13 770880203 E -2);
        impl_case!(12 :: Up => 137 708802026 E -3);
        impl_case!(13 :: Up => 1377 088020251 E -4);
    }

    mod case_221456999999Eneg3_ {
        use super::*;

        case_input! {
            221 456999999 E -3
          +  90 208634338 467704452 E -22
        }

        //  221456999.999
        //           .__90208634338467704452
        //
        //              [90][208634338][467704452]
        // [221][456999999]
        //
        //              [90][208634338][467704452]
        // [221][456999999]
        //
        //
        //  |-5-|
        //              [90][208634338][467704452]
        // [221][456999999]
        //                {208634338,467704452}
        //               [9__]
        // [22145]~[6999999__]

        impl_case!(5 :: Up => 22146 E 4);
        impl_case!(9 :: Up => 221457001 E 0);
    }

    mod case_7252497018938231971071980694278391312Eneg81_582401198862283838Eneg53 {
        use super::*;

        case_input! {
           7 252497018 938231971 071980694 278391312 332025784 984799912 889878916 571079890 868310108 E -81
          +  582401198 862283838 803655671 145175731 609057795 489189459 E -53
        }

        //           |         |         |         |         |         |         |         |         |
        // 72524 970189382 319710719 806942783 913123320 257849847 999128898 789165710 798908683 10108____
        // 58240 119886228 383880365 567114517 573160905 779548918 9459_____
        //     ^
        impl_case!(5 :: Up => 13077 E -3);

        //           8         7         6         5         4         3         2         1         0
        //           |         |         |         |         |         |         |         |         |
        // 725249701 893823197 107198069 427839131 233202578 498479991 288987891 657107989 086831010 8________
        // 582401198 862283838 803655671 145175731 609057795 489189459
        //         ^
        //
        //           5         4         3         2         1         0
        //           |         |         |         |         |         |
        // 725249701 893823197 107198069 427839131 233202578 498479991 2________
        // 582401198 862283838 803655671 145175731 609057795 489189459
        //         ^
        impl_case!(9 :: Up => 130765091 E -7);

        //           8         7         6         5         4         3         2         1         0
        //           |         |         |         |         |         |         |         |         |
        // 7 252497018 938231971 071980694 278391312 332025784 984799912 889878916 571079890 868310108
        // 5 824011988 622838388 036556711 451757316 090577954 89189459_
        //           ^
        //
        //
        //           5         4         3         2         1         0
        //           |         |         |         |         |         |
        // 7 252497018 938231971 071980694 278391312 332025784 984799912
        // 5 824011988 622838388 036556711 451757316 090577954 89189459_
        //           ^
        impl_case!(10 :: Up => 1 307650901 E -8);

        //           8         7         6         5         4         3         2         1         0
        //           |         |         |         |         |         |         |         |         |
        // 72 524970189 382319710 719806942 783913123 320257849 847999128 898789165 710798908 68310108_
        // 58 240119886 228383880 365567114 517573160 905779548 9189459__
        //           ^
        //
        //           5         4         3         2         1         0
        //           |         |         |         |         |         |
        // 72 524970189 382319710 719806942 783913123 320257849 84799912_
        // 58 240119886 228383880 365567114 517573160 905779548 9189459__
        //           ^
        impl_case!(11 :: Up => 13 076509008 E -9);

        //           8         7         6         5         4         3         2         1         0
        //           |         |         |         |         |         |         |         |         |
        // 725 249701893 823197107 198069427 839131233 202578498 479991288 987891657 107989086 8310108__
        // 582 401198862 283838803 655671145 175731609 057795489 189459___
        //           ^
        //
        //           5         4         3         2         1         0
        //           |         |         |         |         |         |
        // 725 249701894 823197107 198069427 839131233 202578498 4799912__
        // 582 401198862 283838803 655671145 175731609 057795489 189459___
        //           ^
        impl_case!(12 :: Up => 130 765090076 E -10);

        //           8         7         6         5         4         3         2         1         0
        //           |         |         |         |         |         |         |         |         |
        // 7252 497018938 231971071 980694278 391312332 025784984 799912889 878916571 079890868 310108___
        // 5824 011988622 838388036 556711451 757316090 577954891 89459___
        //           ^
        //
        //           5         4         3         2         1         0
        //           |         |         |         |         |         |
        // 7252 497018938 231971071 980694278 391312332 025784984 799912___
        // 5824 011988622 838388036 556711451 757316090 577954891 89459____
        //           ^
        impl_case!(13 :: Up => 1307 650900757 E -11);

        //           8         7         6         5         4         3         2         1         0
        //           |         |         |         |         |         |         |         |         |
        // 7 252497018 938231971 071980694 278391312 332025784 984799912 889878916 571079890 868310108
        // 5 824011988 622838388 036556711 451757316 090577954 89189459_
        //                     ^
        //
        //           5         4         3         2         1         0
        //           |         |         |         |         |         |
        // 7 252497018 938231971 071980694 278391312 332025784 984799912
        // 5 824011988 622838388 036556711 451757316 090577954 89189459_
        //                     ^
        impl_case!(19 :: Up => 1 307650900 756107036 E -17);

        //           |         |         |         |         |         |         |         |         |
        // 72 524970189 382319710 719806942 783913123 320257849 847999128 898789165 710798908 68310108_
        // 58 240119886 228383880 365567114 517573160 905779548 9189459__
        //            ^
        impl_case!(20 :: Up => 13 076509007 561070360 E -18);
    }

    mod case_1940445822027805476857100732Eneg27_6979656906052501169943119Eneg24 {
        use super::*;

        case_input! {
            1 940445822 027805476 857100732 E -27
         +  6979656 906052501 169943119 E -24
        }

        //           2         1         0
        //           |         |         |
        // 19404 458220278 054768571 007320000
        // 69796 569060525 011699431 190000000
        //     ^
        impl_case!(5 :: Up => 89202 E -4);

        impl_case!(6 :: Up => 892011 E -5);

        // 1940445 822027805 476857100 732000000
        // 6979656 906052501 169943119
        impl_case!(7 :: Up => 8920103 E -6);
        impl_case!(8 :: Up => 89201028 E -7);
        impl_case!(9 :: Up => 892010273 E -8);
        impl_case!(10 :: Up => 8 920102729 E -9);
        impl_case!(13 :: Up => 8920 102728081 E -12);

        //           2         1         0
        //           |         |         |
        // 194044 582202780 547685710 073200000
        // 697965 690605250 116994311 900000000
        //                ^
        impl_case!(15 :: Up => 892010 272808031 E -14);
    }


    mod case_1_2966825458Eneg10 {
        use super::*;

        case_input! {
            1 E 0
         +  2 966825458 E -10
        }

        impl_case!(10 :: Up => 1 296682546 E -9);
    }

    mod case_22493_2966825458Eneg10 {
        use super::*;

        case_input! {
            22493 E 0
         +  6116004 159574192 551232564 E -24
        }

        impl_case!(4 :: Up => 2250 E 1);
        impl_case!(5 :: Up => 22500 E 0);
        impl_case!(10 :: Up => 2 249911601 E -5);
    }

    mod case_5Eneg1_9999332354Eneg10 {
        use super::*;

        case_input! {
            5 E -1
         +  9 999332354 E -10
        }

        impl_case!(10 :: Up => 1 499933236 E -9);
    }

    mod case_1000_999999900Eneg16 {
        use super::*;

        case_input! {
            1000 E 0
         +  999999900 E -16
        }

        //    1000
        //  +    0.0000000999999900
        //    |---11-----|

        //    1000
        //  +    0.0000000999999900
        //    |---10----|
        //    [1]
        //    [0000000][999999900]

        impl_case!(10 :: Up => 1 000000001 E -6
                       : Down, HalfUp => 1 000000000 E -6);
        impl_case!(11 :: Up, HalfUp, HalfDown, HalfEven => 10 000000001 E -7
                       : Down => 10 000000000 E -7);

        impl_case!(12 :: Up, HalfUp => 100 000000010 E -8
                       : Down => 100 000000009 E -8);

        impl_case!(15 :: Up, HalfUp => 100000 000010000 E -11
                       : Down => 100000 000009999 E -11);
    }

    mod case_1000_5Eneg8 {
        use super::*;

        case_input! {
            1000 E 0
         +  5 E -8
        }

        impl_case!(10 :: Up => 1 000000001 E -6
                       : Down, HalfUp => 1 000000000 E -6);
        impl_case!(11 :: Up, HalfUp => 10 000000001 E -7
                       : Down, HalfEven, HalfDown => 10 000000000 E -7);
        impl_case!(12 :: Up, Down, HalfEven, HalfDown, HalfUp => 100 000000005 E -8);
    }

    mod case_12624669663Eneg5_99999900Eneg14 {
        use super::*;

        case_input! {
            12 624669663 E -5
         +  99999900 E -14
        }

        impl_case!(10 :: Up => 1 262466967 E -4
                       : Down => 1 262466966 E -4);
    }

    mod case_500020139947889411758Eneg21_5Eneg1 {
        use super::*;

        case_input! {
            500 020139947 889411758 E -21
         +  5 E -1
        }

        impl_case!(10 :: Up => 1 000020140 E -9
                       : Down => 1 000020139 E -9);
    }

    mod case_92415491245Eneg11_5E_neg1 {
        use super::*;

        case_input! {
            92 415491245 E -11
         +  5 E -1
        }

        // .92415491245
        // .5
        // [92][415491245]
        // [5]

        // [92][415491245]
        // [5]
        //  |----10----|
        //
        // [9][241549124][5________]
        // [5]
        //  |----10----|

        impl_case!(10 :: Up => 1 424154913 E -9
                       : Down => 1 424154912 E -9);
    }

    mod case_4999999999742996055106Eneg22_5Eneg1 {
        use super::*;

        case_input! {
            4999 999999742 996055106 E -22
         +  5 E -1
        }

        // .4999 999999742 996055106
        // .5

        // [4999][999999742][996055106]
        // [5]
        // b_end_pos=21

        // prec=9  pos=13
        // [499999999]~[974299605][5106_____]
        // [5________]
        //
        //                 {996055106}
        // [499999999]~[9742_____]
        // [5________]


        impl_case!(9 :: Up => 100000000 E -8
                      : Down => 999999999 E -9);
        impl_case!(10 :: Up => 1 000000000 E -9
                       : Down => 9 999999999 E -10);
        impl_case!(11 :: Up => 99 999999998 E -11
                       : Down => 99 999999997 E -11);
    }

    mod case_10629710115Eneg20_999999999846851456665Eneg21 {
        use super::*;

        case_input! {
            10 629710115 E -20
         +  999 999999846 851456665 E -21
        }

        // 0.999999999846851456665
        // 0.00000000010629710115
        //

        //  0.999999999846851456665
        //  0.00000000010629710115
        //    |----20------------|
        // 0.[99][999999984][685145666][5________]
        //              [10][629710115]
        impl_case!(20 :: Up => 99 999999995 314855782 E -20);

        //  0.999999999846851456665
        //  0.00000000010629710115
        //    |-----19----------|
        //                      ^2
        // 0.[9][999999998][468514566]~[65_______]
        //              [1][062971011]~[5________]
        impl_case!(19 :: Up => 9 999999999 531485579 E -19);

        //  0.999999999846851456665
        //  0.00000000010629710115
        //    |-----18---------|
        //                     ^3
        // 0.[9][99999999][846851456]~[665______]
        //                [106297101]~[15_______]
        impl_case!(18 :: Up => 999999999 953148558 E -18);

        //  0.999999999846851456665
        //  0.00000000010629710115
        //    |-----15------|
        //                  ^6
        // 0.[999999][999846851]~[456665___]
        //              [106297]~[10115____]
        impl_case!(15 :: Up => 999999 999953149 E -15);

        //  0.999999999846851456665
        //  0.00000000010629710115
        //    |---12-----|
        //               ^9
        // 0.[999][999999846]~[851456665]
        //              [106]~[29710115_]
        impl_case!(12 :: Up => 999 999999954 E -12);


        // 0.999999999846851456665
        // 0.00000000010629710115
        //   |--11-----|
        //             ^10
        //
        // [99][999999984]~[685145666][5_______]
        //            [10]~[629710115]
        impl_case!(11 :: Up => 99 999999996 E -11
                       : Down => 99 999999995 E -11);

        // 0.999999999846851456665
        // 0.00000000010629710115
        //   |--10----|
        //            ^11
        //
        // [9][999999998]~[468514566][65_______]
        //            [1]~[062971011][5________]
        //
        impl_case!(10 :: Up => 1 000000000 E -9
                       : Down => 9 999999999 E -10);

        //  0.999999999846851456665
        //  0.00000000010629710115
        //    |--9----|
        //            ^12
        // 0.[999999999]~[846851456][665______]
        //              ~[106297101][15_______]
        impl_case!(9 :: Up => 100000000 E -8
                      : Down => 999999999 E -9);
    }


    mod case_3153658933995718176610972527Eneg27 {
        use super::*;

        case_input! {
            3 153658933 995718176 610972527 E -27
         +  1 235890621 129256389 E 20
        }

        // |----17---------|------------------------------------------------|
        // 1235890621129256389xxxxxxxxxxxxxxxxxxx3153658933995718176610972527
        impl_case!(17 :: Up => 12358906 211292564 E 22);
        // |----18----------|-----------------------------------------------|
        // 1235890621129256389xxxxxxxxxxxxxxxxxxx3153658933995718176610972527
        impl_case!(18 :: Up => 123589062 112925639 E 21);
        impl_case!(20 :: Up => 12 358906211 292563891 E 19);
        impl_case!(27 :: Up => 123589062 112925638 900000001 E 12);

        // |----30----------------------|-----------------------------------|
        // 1235890621129256389xxxxxxxxxxxxxxxxxxx3153658933995718176610972527
        impl_case!(28 :: Up => 1 235890621 129256389 000000001 E 11);

        // |----30----------------------|-----------------------------------|
        // 1235890621129256389xxxxxxxxxxxxxxxxxxx3153658933995718176610972527
        impl_case!(30 :: Up => 123 589062112 925638900 000000001 E 9);

        // |---57--------------------------------------------------|--------|
        // 1235890621129256389xxxxxxxxxxxxxxxxxxx3153658933995718176610972527
        impl_case!(57 :: Up => 123 589062112 925638900 000000000 000000003 153658933 995718177 E -18);
        // |---65----------------------------------------------------------|
        // 1235890621129256389xxxxxxxxxxxxxxxxxxx3153658933995718176610972527
        impl_case!(65 :: Up => 12 358906211 292563890 000000000 000000000 315365893 399571817 661097253 E -26);
        impl_case!(66 :: Up => 123 589062112 925638900 000000000 000000003 153658933 995718176 610972527 E -27);
        impl_case!(68 :: Up => 123 589062112 925638900 000000000 000000003 153658933 995718176 610972527 E -27);
    }

    mod case_999999e10_2 {
        use super::*;

        case_input! {
            2 E 0
         +  999999 E 10
        }

        // |-5-|
        // 999999xxxxxxxxx2
        impl_case!(5 :: Up => 10000 E 12);

        // |--8---|
        // 999999xxxxxxxxx2
        impl_case!(8 :: Up => 99999901 E 8);
    }

    mod case_999999e10_500000000 {
        use super::*;

        case_input! {
            500000000 E 0
         +  999999 E 10
        }

        // 999999xxxxxxxxxx

        // |-5-|
        // 999999x500000000
        impl_case!(5 :: Up => 10000 E 12);
        // |--6-|
        // 999999x500000000
        impl_case!(6 :: Up => 100000 E 11);

        // |---7-|
        // 999999x500000000
        impl_case!(7 :: Up, HalfUp => 9999991 E 9
                      : Down, HalfDown, HalfEven => 9999990 E 9);

        // |----8-|
        // 999999x500000000
        impl_case!(8 :: Up, Down => 99999905 E 8);

        impl_case!(9 :: Up, Down => 999999050 E 7);
        impl_case!(10 :: Up, Down => 9 999990500 E 6);

        impl_case!(16 :: Up, Down => 9999990 500000000 E 0);
    }

    mod case_999999999999_999999999999 {
        use super::*;

        case_input! {
            999 999999999 E 0
         +  999 999999999 E 0
        }

        impl_case!(12 :: Up => 200 000000000 E 1);

        impl_case!(13 :: Up, HalfUp => 1999 999999998 E 0
                       : Down, HalfDown, HalfEven => 1999 999999998 E 0);
    }

    mod case_999999999999_999999000000 {
        use super::*;

        case_input! {
            999 999999999 E 0
         +  999 999000000 E 0
        }

        impl_case!(13 :: Up, Down, HalfDown, HalfEven, HalfUp => 1999 998999999 E 0);

        impl_case!(12 :: Up, HalfUp => 199 999900000 E 1
                       : Down => 199 999899999 E 1);

        impl_case!(7 :: Up, HalfUp => 1999999 E 6
                      : Down => 1999998 E 6);
    }

    mod case_50000000006239812165Eneg74_99999Eneg74 {
        use super::*;

        case_input! {
            50 000000006 239812165 713997130 356572547 321118899 035201144 467289510 531789638 E -74
         +                                          99 999999999 999176722 499389900 889909530 E -74
        }

        impl_case!(1 :: Up, Ceiling => 6 E -1
                      : Down, HalfDown, HalfEven, HalfUp => 5 E -1);

        impl_case!(2 :: Up => 51 E -2
                      : Down => 50 E -2);

        impl_case!(20 :: Up => 50 000000006 239812166 E -20);
        impl_case!(29 :: Up => 50 000000006 239812165 713997131 E -29);
        impl_case!(39 :: Up => 500 000000062 398121657 139971303 565726474 E -39);
        impl_case!(45 :: Up => 500000000 062398121 657139971 303565726 473211189 E -45);
        impl_case!(55 :: Up => 5 000000000 623981216 571399713 035657264 732111889 903437787 E -55);
        impl_case!(56 :: Up => 50 000000006 239812165 713997130 356572647 321118899 034377867 E -56);
    }

    mod case_5E5_99999E6 {
        use super::*;

        case_input! {
                  5 E 5
        +   999994  E 6
        }

        impl_case!(5 :: Up => 10000 E 8
                      : Down, HalfUp, HalfDown, HalfEven => 99999 E 7);
        impl_case!(6 :: Up, HalfUp => 999995 E 6
                      : Down, HalfDown, HalfEven => 999994 E 6);
        impl_case!(7 :: Up, Down => 9999945 E 5);
    }

    mod case_51107686028821487501515062485847334785980064596338468467Eneg56_ {
        use super::*;

        case_input! {
            51 107686028 821487501 515062485 847334785 980064596 338468467 E -56
        +   98 892313971 178512498 484937514 152665214 019935403 661531533 E -56
        }

        impl_case!(1 :: Up, HalfUp, HalfEven => 2 E 0
                      : Down, HalfDown => 1 E 0);
        impl_case!(2 :: Up, Down, HalfUp, HalfDown, HalfEven => 15 E -1);
        impl_case!(3 :: Up, Down, HalfUp, HalfDown, HalfEven => 150 E -2);
        impl_case!(10 :: Up, Down => 1 500000000 E -9);
        impl_case!(47 :: Up, Down => 15 000000000 000000000 000000000 000000000 000000000 E -46);
    }

}


fn rounding_digits<N: Into<bigdigit::BigDigitBase>>(n: N) -> (u8, u8)
{
    let x = n.into() % 100;
    div_rem(x as u8, 10)
}

// Round the digit by subtracting the lowest digit and adding the result of rounding
// the pair of digits
//
// If an overflow occurs after rounding, both the rounding_carry and carry will be
// set to 1. It is asserted that if carry is already 1, then rounding cannot
// overflow
//
//
fn make_rounded_value(
    digit: BigDigit,
    rounding: RoundingMode,
    sign: Sign,
    pair: (u8, u8),
    trailing_zeros: bool,
    rounding_carry: &mut BigDigit,
    carry: &mut BigDigit,
) -> BigDigit
{
    debug_assert_eq!(*rounding_carry, BigDigit::zero());
    let rounded_digit = rounding.round(sign, pair, trailing_zeros);
    let d = digit.as_digit_base();
    let reduced_d = BigDigit::from_raw_integer(d - (d % 10));
    let rounded_value = reduced_d.add_with_carry(rounded_digit, rounding_carry);

    debug_assert!(!(carry.is_one() && rounding_carry.is_one()));
    carry.add_assign(*rounding_carry);
    return rounded_value;
}

/// Called when sum of digits exceeds requested digit length
///
/// We need to re-round the low digit one decimal point left, and shift the
/// remaining values right by one digit.
///
/// Params
/// ------
/// d0: The original decimal (before any rounding)
/// rounding: rounding mode
/// pair: digits to round
/// trailing_zeros: true if all digits after pair are zero, used for rounding
/// rounding_carry: BigDigit storing the 'carry' value of the last rounding operation
///     If it is the same as this second rounding, no change needs to happen with the other
///     values.
///     If original was zero and this was one, it's a new carry that must be propagated.
///     If original was one and this was zero... that probably can't happen
///
/// result: original values of the sum, which is one too many digits long
///
fn handle_overflow(
    d0: bigdigit::BigDigitBase,
    rounding: RoundingMode,
    pair: (u8, u8),
    trailing_zeros: bool,
    rounding_carry: BigDigit,
    result: &mut DigitInfo,
) {
    // shifted_radix is the 'radix' for the BigDigit divided by ten (i.e. shifted one digit right)
    let shifted_radix = BigDigit::max_power_of_ten().as_digit_base();

    // calculate new (shifted) rounded value of d0
    let rounded_value = rounding.round(result.sign, pair, trailing_zeros);
    let shifted_d0 = d0 / 10;
    let mut rounded_d0 = shifted_d0 - (shifted_d0 % 10) + rounded_value as bigdigit::BigDigitBase;

    // If the original rounding already carried the one into the
    // rest of the sum, we must remove it from replacement value.
    if rounding_carry.is_one() {
        if rounded_d0 >= shifted_radix {
            rounded_d0 -= shifted_radix;
        } else {
            // The original value rounded into overflow, but this
            // one did not. This should not happen?
            // To fix, we'd have to subtract one (with borrow) from
            // the rest of the digits.
            unreachable!();
        }
    }

    result.scale += 1;
    result.digits.shift_right_1_and_replace_bigdigit(
        BigDigit::from_raw_integer(rounded_d0)
    );
}
