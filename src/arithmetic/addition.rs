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
    DigitInfo,
    BigDigitLoc,
    align_with_insignificance,
    align_with_shift
};

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
    // route to something
    match (a.sign, b.sign, a.scale > b.scale) {
        (Sign::Plus, Sign::Minus, true) => { unimplemented!(); }
        (Sign::Plus, Sign::Minus, false) => { unimplemented!(); }
        (Sign::Minus, Sign::Plus, true) => { unimplemented!(); }
        (Sign::Minus, Sign::Plus, false) => { unimplemented!(); }
        (Sign::NoSign, _, _) => {
            result.copy_with_precision(b, precision, rounding)
        }
        (_, Sign::NoSign, _) => {
            result.copy_with_precision(a, precision, rounding)
        }
        (_, _, true) => {
            add_digits_into_impl(b, a, precision, rounding, result)
        }
        (_, _, false) => {
            add_digits_into_impl(a, b, precision, rounding, result)
        }
    }
}

/// Actual implementation of add_digits_into_impl
///
#[allow(unreachable_code)]
pub(crate) fn add_digits_into_impl(
    a: &DigitInfo,
    b: &DigitInfo,
    precision: NonZeroUsize,
    rounding: RoundingMode,
    result: &mut DigitInfo
) {
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
    //       │      └─> a-end-pos=0 (always)
    //       └────────> a-start-pos=6
    //  bbbbbbbb.b
    //  │        └─> b-end-pos=3
    //  └──────────> b-start-pos=11
    //
    let b_end_pos = (b.scale - a.scale) as usize;
    let b_start_pos = b.count_digits() + b_end_pos - 1;
    let a_start_pos = a.count_digits() - 1;

    let max_start_pos = usize::max(a_start_pos, b_start_pos);

    // Compare maximum digit position to requested precision
    // * If max-digits is less than the precision, we can safely add the two numbers
    //   and not worry about overflow. This is the case where checked_sub returns None
    // * If the last-digit of b ends before the start of a, we do not have to handle
    //   any addition, and can just copy the shifted bigdigits from each array
    // * Otherwise we have to add all overlapping digits to see how rounding needs
    //   to be applied
    match max_start_pos.checked_sub(precision.get()) {
        // not enough digits to worry about precision/rounding
        None => {
            result.scale = a.scale;
            let (a_skip, b_shift) = BigDigitVec::digit_position_to_bigdigit_index_offset(b_end_pos);
            let b_digits = BigDigitSplitterIter::from_slice_shifting_left(&b.digits, b_shift);
            let mut carry = BigDigit::zero();
            if a_skip < a.digits.len() {
                // a & b are "disjoint" - we just copy the values
                let (only_a, a_digits) = a.digits.split_at(a_skip);
                result.digits.extend_from_slice(&only_a);
                let a_digits = BigDigitSplitterIter::from_slice_shifting_left(&a_digits, 0);
                _impl_add_digits(a_digits, b_digits, &mut result.digits, &mut carry);
                if !carry.is_zero() {
                    result.digits.push(carry);
                }
            } else {
                // a & b are "disjoint" - we just copy the values
                result.digits.extend_from_slice(&a.digits);
                result.digits.resize(a_skip, BigDigit::zero());
                b_digits.extend_vector(&mut result.digits);
            }

            // check for overflow
            let overflow = max_start_pos + 1 == precision.get() &&
                (!carry.is_zero() || result.digits.count_digits() > precision.get());
            if overflow {
                result.scale += 1;
                let rounding_value = result.digits[0].as_digit_base() % 100;
                let rounding_pair = div_rem(rounding_value as u8, 10);
                let rounded_digit = rounding.round(result.sign, rounding_pair, true);
                result.digits.shift_right_and_replace_digit(1, rounded_digit.into());
            }
            return;
        }
        // Digits in 'a' & 'b' are disjoint - no need to actually sum
        // Note: we need the +1 for the case where we round inside 'a' and
        //       it overflows into the 'b' digits
        Some(insig_pos) if b_end_pos > a_start_pos + 1 => {
            let significant_pos = insig_pos + 1;
            result.scale = a.scale + significant_pos as i64;

            let (
                a_skip, a_offset
            ) = BigDigitVec::digit_position_to_bigdigit_index_offset(significant_pos);

            let mut trailing_zeros = false;
            let rounding_digit0;
            let rounding_digit1;

            if b_end_pos == significant_pos {
                rounding_digit0 = 1;
                rounding_digit1 = (b.digits[0].as_digit_base() % 10) as u8;
            } else if significant_pos > b_end_pos {
                let sig_pos_relative_to_b_end = significant_pos - b_end_pos;
                ((rounding_digit1, rounding_digit0), _) = b.digits.get_rounding_info(sig_pos_relative_to_b_end);
            } else if significant_pos == a_start_pos + 1 {
                // highest a digit is insignificant rounding digit
                let (last_bigdigit, rest) = a.digits.split_last().unwrap();
                let (highest_digit, lower_digits) = last_bigdigit.split_highest_non_zero_digit();
                trailing_zeros = lower_digits == 0 && rest.iter().all(BigDigit::is_zero);
                rounding_digit0 = highest_digit;
                rounding_digit1 = 0;  // always zero, since we enforce a space between 'a' and 'b'
            } else if significant_pos > a_start_pos + 1 {
                // a is insignificant but nonzero, so rounding_digit0 is 1
                rounding_digit0 = 1;
                rounding_digit1 = 0;
            } else {
                // we can use the standard rounding-info for 'a'
                (
                    (rounding_digit1, rounding_digit0),
                    trailing_zeros
                ) = a.digits.get_rounding_info(significant_pos);
            }

            let rounded_value = rounding.round(result.sign, (rounding_digit1, rounding_digit0), trailing_zeros);
            // dbg!(rounding_digit1, rounding_digit0, trailing_zeros, rounded_value);

            let (
                b_shift,
                b_offset,
                mut b_digits
            );

            if b_end_pos >= significant_pos {
                let b_end_relative_to_sig_point = b_end_pos - significant_pos;
                let (b_end_idx, b_end_offset) = BigDigitVec::digit_position_to_bigdigit_index_offset(b_end_relative_to_sig_point);
                b_shift = Some(b_end_idx);
                b_offset = b_end_offset;
                b_digits = BigDigitSplitterIter::from_slice_shifting_left(&b.digits, b_offset);
            } else {
                let sig_point_relative_to_b_end = significant_pos - b_end_pos;
                let (b_end_idx, b_end_offset) = BigDigitVec::digit_position_to_bigdigit_index_offset(sig_point_relative_to_b_end);
                b_shift = None;
                b_offset = b_end_offset;
                b_digits = BigDigitSplitterIter::from_slice_shifting_right(&b.digits[b_end_idx..], b_offset);
            }

            // handle case of totally insignificant 'a'
            if significant_pos >= a_start_pos + 1 {
                result.digits.push(rounded_value.into());

                let mut zero = BigDigit::zero();
                if b_end_pos == significant_pos {
                    let replacement_digit: BigDigit = rounding_digit1.into();
                    let reduced_b0 = b_digits.next().unwrap().sub_with_carry(replacement_digit, &mut zero);
                    result.digits[0].add_assign(reduced_b0);
                } else {
                    match b_shift {
                        Some(0) => {
                            result.digits[0].add_assign(b_digits.next().unwrap());
                        }
                        Some(bigdigit_count) => {
                            result.digits.resize(bigdigit_count, BigDigit::zero());
                        }
                        None => {
                            let b0 = b_digits.next().unwrap().as_digit_base();
                            let reduced_b0 = BigDigit::from_raw_integer(b0 - (b0 % 10));
                            result.digits[0].add_assign_with_carry(reduced_b0, &mut zero);
                            b_digits.extend_vector_adding_carry(zero, &mut result.digits);
                            return;
                        }
                    }
                }
                assert!(zero.is_zero());
            } else {
                let mut a_digits = BigDigitSplitterIter::from_slice_shifting_right(
                    &a.digits[a_skip..], a_offset
                );
                let a0 = a_digits.next().unwrap();

                let mut carry = BigDigit::from_raw_integer(rounded_value);
                let rounded_a0 = a0.sub_with_carry(a0.lowest_digit(), &mut carry);
                result.digits.push(rounded_a0);
                a_digits.extend_vector_adding_carry(carry, &mut result.digits);

                match b_shift {
                    Some(bigdigit_count) if bigdigit_count + 1 == result.digits.len() => {
                        debug_assert!(b_offset > 0);
                        let b0 = b_digits.next().unwrap();
                        let prev_digit = result.digits.last_mut().unwrap();
                        prev_digit.add_assign(b0);
                    }
                    Some(bigdigit_count) => {
                        // 'b' and 'a' are present in the same bigdigit
                        debug_assert!(bigdigit_count >= result.digits.len());
                        result.digits.resize(bigdigit_count, BigDigit::zero());
                    }
                    None => {}
                }
            }

            b_digits.extend_vector(&mut result.digits);
        }
        // All of 'b' is significant and there's digit overlap
        Some(insignificant_pos) if b_end_pos >= insignificant_pos + 1 => {
            let significant_pos = insignificant_pos + 1;
            result.scale = a.scale + significant_pos as i64;

            let (
                pos_idx,
                pos_offset,
            ) = BigDigitVec::digit_position_to_bigdigit_index_offset(significant_pos);
            let (insig_a_digits, sig_a_digits) = a.digits.split_at(pos_idx);

            // aligned a & b digits
            let mut a_digits = BigDigitSplitterIter::from_slice_starting_bottom(
                sig_a_digits, pos_offset
            );

            let shifted_b_end = b_end_pos - significant_pos;
            let (
                shifted_b_idx,
                shifted_b_offset,
            ) = BigDigitVec::digit_position_to_bigdigit_index_offset(shifted_b_end);
            let mut b_digits = BigDigitSplitterIter::from_slice_shifting_left(
                &b.digits, shifted_b_offset
            );

            let trailing_zeros;
            let rounding_digit0;
            let rounding_digit1;
            let rounding_digit2;

            match (pos_idx, pos_offset) {
                (0, 0) => {
                    trailing_zeros = true;
                    rounding_digit0 = 0;
                }
                (_, 0) => {
                    // all a_digits are significant, get rounding_digit0 from insig_a_digits
                    let (last_bigdigit, rest) = insig_a_digits.split_last().unwrap();
                    let (highest_digit, lower_digits) = last_bigdigit.split_highest_digit();
                    trailing_zeros = lower_digits == 0 && rest.iter().all(BigDigit::is_zero);
                    rounding_digit0 = highest_digit;
                }
                _ => {
                    // Get rounding_digit0 from first a_digits
                    let last_bigdigit = a_digits.next().unwrap();
                    let (highest_digit, lower_digits) = last_bigdigit.split_highest_digit();
                    // dbg!(last_bigdigit, highest_digit, lower_digits);
                    trailing_zeros = lower_digits == 0 && insig_a_digits.iter().all(BigDigit::is_zero);
                    rounding_digit0 = highest_digit;
                }
            }

            let mut carry = BigDigit::zero();
            let overflow_digit0;
            if shifted_b_idx == 0 {
                // b digits overlap first significant a digits - need to sum
                let a0 = a_digits.next().unwrap_or(BigDigit::zero());
                let b0 = b_digits.next().unwrap_or(BigDigit::zero());
                let s0 = BigDigit::add_with_carry(&a0, &b0, &mut carry);

                let rounding_digit_value = s0.as_digit_base() % 100;
                (
                    rounding_digit2,
                    rounding_digit1,
                ) = div_rem(rounding_digit_value as u8, 10);

                let rounded = rounding.round(
                    result.sign,
                    (rounding_digit1, rounding_digit0),
                    trailing_zeros
                );

                let mut tmp = BigDigit::from_raw_integer(rounded);
                let rounded_s0 = s0.sub_with_carry(rounding_digit1, &mut tmp);
                carry.add_assign(tmp);
                result.digits.push(rounded_s0);

                let rounded = rounding.round(
                    result.sign,
                    (rounding_digit2, rounding_digit1),
                    trailing_zeros && rounding_digit0 == 0
                );

                let shifted_s0 = s0.as_digit_base() / 10;
                let rounded_s0 = shifted_s0 - (shifted_s0 % 10) + rounded as bigdigit::BigDigitBase;
                overflow_digit0 = match rounded_s0.cmp(&100000000) {
                    std::cmp::Ordering::Less => BigDigit::from_raw_integer(rounded_s0),
                    std::cmp::Ordering::Equal => BigDigit::zero(),
                    std::cmp::Ordering::Greater => unreachable!(),
                };
            } else {
                let a0 = a_digits.next().unwrap();
                let rounding_digit_value = a0.as_digit_base() % 100;
                (
                    rounding_digit2,
                    rounding_digit1,
                ) = div_rem(rounding_digit_value as u8, 10);

                let rounded = rounding.round(
                    result.sign,
                    (rounding_digit1, rounding_digit0),
                    trailing_zeros
                );
                carry = BigDigit::from_raw_integer(rounded);
                let rounded_a0 = a0.sub_with_carry(rounding_digit1, &mut carry);
                result.digits.push(rounded_a0);
                while !carry.is_zero() && result.digits.len() < shifted_b_idx {
                    let mut next_a_digit = a_digits.next().unwrap_or(BigDigit::zero());
                    next_a_digit.add_assign_carry(&mut carry);
                    result.digits.push(next_a_digit);
                }
                for _ in result.digits.len()..shifted_b_idx {
                    result.digits.push(a_digits.next().unwrap_or(BigDigit::zero()));
                }

                let rounded = rounding.round(
                    result.sign,
                    (rounding_digit2, rounding_digit1),
                    trailing_zeros && rounding_digit0 == 0
                );

                let shifted_a0 = a0.as_digit_base() / 10;
                let rounded_a0 = shifted_a0 - (shifted_a0 % 10) + rounded as bigdigit::BigDigitBase;
                overflow_digit0 = match rounded_a0.cmp(&100000000) {
                    std::cmp::Ordering::Less => BigDigit::from_raw_integer(rounded_a0),
                    std::cmp::Ordering::Equal => BigDigit::zero(),
                    std::cmp::Ordering::Greater => unreachable!(),
                };
            }
            _impl_add_digits(a_digits, b_digits, &mut result.digits, &mut carry);
            if !carry.is_zero() {
                result.digits.push(carry);
            }

            let overflowed = !carry.is_zero() || result.digits.count_digits() > precision.get();
            if overflowed {
                result.scale += 1;
                result.digits.shift_right_1_and_replace_bigdigit(overflow_digit0);
            }
        }
        Some(insignificant_pos) => {
            use std::cmp::Ordering::*;

            // position of first significant digit (as 'digit-index') in relation to
            // last (smallest) digit of 'a'
            let significant_pos = insignificant_pos + 1;

            let (
                pos_idx,
                pos_offset,
            ) = BigDigitVec::digit_position_to_bigdigit_index_offset(significant_pos);

            let mut trailing_zeros = true;

            let (
                skipable_a_bigdigits,
                _,
            ) = BigDigitVec::digit_position_to_bigdigit_index_offset(b_end_pos);

            let insig_digit_count_b = significant_pos - b_end_pos;
            let (
                b_idx,
                b_offset,
            ) = BigDigitVec::digit_position_to_bigdigit_index_offset(insig_digit_count_b);

            let insig_bigdigit_count_b = b_idx + (b_offset > 0) as usize;
            let insig_bigdigit_count_a = pos_idx + (pos_offset > 0) as usize - skipable_a_bigdigits;

            let (ignorable_a_digits, overlap_digits) = a.digits.split_at(skipable_a_bigdigits);
            trailing_zeros &= ignorable_a_digits.iter().all(BigDigit::is_zero);

            // aligned a & b digits
            let mut a_digits = BigDigitSplitterIter::from_slice_starting_bottom(
                overlap_digits, pos_offset
            );

            let mut b_digits = BigDigitSplitterIter::from_slice_starting_bottom(
                &b.digits, b_offset
            );

            // There are extra insignificant digits in 'a' that need evaluated
            // if b_offset == 0 && pos_offset != 0 {
            if insig_bigdigit_count_b != insig_bigdigit_count_a {
                let insig_a = a_digits.next().unwrap();
                trailing_zeros &= insig_a.is_zero();
            }

            let mut carry = BigDigit::zero();

            // insignificant sums
            for _ in 1..insig_bigdigit_count_b {
                let next_a = a_digits.next().unwrap_or(BigDigit::zero());
                let next_b = b_digits.next().unwrap_or(BigDigit::zero());
                let insig_sum = BigDigit::add_with_carry(&next_a, &next_b, &mut carry);
                trailing_zeros &= insig_sum.is_zero();
            }

            let insig_a0 = a_digits.next().unwrap_or(BigDigit::zero());
            let insig_b0 = b_digits.next().unwrap_or(BigDigit::zero());
            let insig_s0 = BigDigit::add_with_carry(&insig_a0, &insig_b0, &mut carry);

            let (rounding_digit0, remainder) = insig_s0.split_highest_digit();
            trailing_zeros &= remainder == 0;

            // the first significant addition
            let a0 = a_digits.next().unwrap_or(BigDigit::zero());
            let b0 = b_digits.next().unwrap_or(BigDigit::zero());
            let s0 = BigDigit::add_with_carry(&a0, &b0, &mut carry);

            let rounding_digit_value = s0.as_digit_base() % 100;
            let (
                rounding_digit2,
                rounding_digit1,
            ) = div_rem(rounding_digit_value as u8, 10);

            let rounded_digit = rounding.round(
                result.sign, (rounding_digit1, rounding_digit0), trailing_zeros
            );

            let mut tmp =  BigDigit::from_raw_integer(rounded_digit);
            let rounded_s0 = s0.sub_with_carry(rounding_digit1, &mut tmp);
            carry.add_assign(tmp);
            result.digits.push(rounded_s0);
            _impl_add_digits(a_digits, b_digits, &mut result.digits, &mut carry);
            if !carry.is_zero() {
                result.digits.push(carry);
            }
            result.scale = a.scale + significant_pos as i64;

            let overflowed = !carry.is_zero() || result.digits.count_digits() > precision.get();
            if overflowed {
                result.scale += 1;
                let replacement_digit = rounding.round(
                    result.sign,
                    (rounding_digit2, rounding_digit1),
                    trailing_zeros && (rounding_digit0 == 0)
                );
                let shifted_s0 = s0.as_digit_base() / 10;
                let rounded_s0 = shifted_s0 - (shifted_s0 % 10) + replacement_digit as bigdigit::BigDigitBase;
                let replacement_bigdigit = match rounded_s0.cmp(&100000000) {
                    std::cmp::Ordering::Less => BigDigit::from_raw_integer(rounded_s0),
                    std::cmp::Ordering::Equal => BigDigit::zero(),
                    std::cmp::Ordering::Greater => unreachable!(),
                };
                result.digits.shift_right_1_and_replace_bigdigit(replacement_bigdigit);
            }
        }
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
        match dbg!(a_digits.next(), b_digits.next()) {
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

        case_input! { 21 182876230 333040678 E -7 + 41 979135927 194856497 E -17 }

        impl_case!(26 :: Up => 21182876 234530954 270719486 E -13;
                         Down => 21182876 234530954 270719485 E -13);

        impl_case!(23 :: Up => 21182 876234530 954270720 E -10;
                         Down => 21182 876234530 954270719 E -10);
        impl_case!(21 :: Up => 211 828762345 309542708 E -8;
                         Down => 211 828762345 309542707 E -8);
        impl_case!(20 :: Up => 21 182876234 530954271 E -7;
                         Down => 21 182876234 530954270 E -7);
        impl_case!(19 :: Up => 2 118287623 453095428 E -6;
                         Down => 2 118287623 453095427 E -6);
        impl_case!(18 :: Up => 211828762 345309543 E -5;
                         Down => 211828762 345309542 E -5);
        impl_case!(17 :: Up => 21182876 234530955 E -4;
                         Down => 21182876 234530954 E -4);
        impl_case!(16 :: Up => 2118287 623453096 E -3;
                         Down => 2118287 623453095 E -3);
        impl_case!(15 :: Up => 211828 762345310 E -2;
                         Down => 211828 762345309 E -2);
        impl_case!(11 :: Up => 21 182876235 E 2);
    }

    mod case_65105089065643509134639_E_neg7_83049409402376021061_E_neg34 {
        use super::*;
        case_input! { 65105 089065643 509134639 E -7 + 83 049409402 376021061 E -27 }
        impl_case!(15 :: Up => 651050 890656436 E 1;
                         Down => 651050 890656435 E 1);
        impl_case!(50 :: Up, Down => 6510508 906564350 913463983 049409402 376021061 E -27 );
    }

    mod case_178450147E_neg3_2392081E6 {
        use super::*;
        case_input! { 178450147 E -3 + 2392081 E 6 }

        impl_case!( 18 :: Up => 2392081 178450147 E -3 );
    }

    mod case_137681612112971086Eneg9_1e20 {
        use super::*;

        case_input! { 137681612 112971086 E -9 + 1 E 20 }

        impl_case!(31 :: Up => 100 000000000 137681612 112971086 E -9 );
        impl_case!(30 :: Up => 100 000000000 137681612 112971086 E -9 );
        impl_case!(29 :: Up => 10 000000000 013768161 211297109 E -8 );
        impl_case!(20 :: Up => 10 000000000 013768162 E 1 );
    }
}


/// Add an insignificant number to n, respecting rounding and precision rules
///
/// This is to be used by functions which detect that one of the operands in
/// an addition operation is too small to have an effect on the other, but
/// rounding may be required.
///
pub(crate) fn add_jot_into(
    n: &DigitInfo,
    precision: NonZeroUsize,
    rounding: RoundingMode,
    result: &mut DigitInfo
) {
    use std::cmp::Ordering::*;

    let digit_count = n.count_digits();
    result.sign = n.sign;
    result.scale = n.scale;
    result.digits.reserve_precision(precision);

    // fnz === first non-zero digit
    let (fnz_idx, fnz_bigdigit) = n.digits.argwhere(|d| d.is_zero().not()).unwrap();

    match digit_count.cmp(&precision.get()) {
        // special case where precision matches digit-count and first digit in stream is zero
        Equal if fnz_idx != 0 => {
            // simulate adding jot, the origin pair of digits to round is (0,0),
            // meaning we will be borrow for negative 99 and adding 1 to positive 01
            let digit_pair = if n.sign == Sign::Minus { (9, 9) } else { (0, 1) };
            let rounded = rounding.round_digits(n.sign == Sign::Minus, digit_pair);
            if rounded == 9 {
                result.digits.resize(fnz_idx, BigDigit::max());
                result.digits.push(fnz_bigdigit.unchecked_sub(1u32));
                result.digits.extend_from_slice(&n.digits[fnz_idx+1..]);
            } else {
                debug_assert!(rounded == 0 || rounded == 10);
                result.digits.extend_from_slice(&n.digits);
            }
        }
        // special case where precision matches digit-count and first digit is not zero
        Equal => {
            let d0 = n.digits[0];
            let high = (d0.as_digit_base() % 10) as u8;

            // round with second digit "1" because we're adding the jot
            // let digit_pair = if n.sign == Sign::Minus { (high - 1, 9) } else { (high, 1) };
            let digit_pair = match (high, n.sign) {
                (0, Sign::Minus) => {
                    (9, 9)
                }
                (h, Sign::Minus) => {
                    (h - 1, 9)
                }
                (h, _) => {
                    (h, 1)
                }
            };

            let rounded = rounding.round_digits(n.sign == Sign::Minus, digit_pair);

            // no change - just copy digits and return
            if rounded == high {
                result.digits.extend_from_slice(&n.digits);
                return;
            }

            // subtract away original first digit add rounded (carry)
            let mut carry = BigDigit::from_raw_integer(rounded);
            let rounded_d0 = d0.sub_with_carry(high, &mut carry);

            // check for "trim" digits only if we're rounding up 9 -> 10
            let wont_need_trimmed = (rounded != 10) || (carry.is_zero() && n.digits.len() > 1);
            if wont_need_trimmed {
                result.digits.push(rounded_d0);
                result.digits.extend_from_slice(&n.digits[1..]);
            }
            // handle pushing single digit, trimming overflow if necessary
            else if n.digits.len() == 1 {
                if d0.is_max() {
                    result.scale += 1;
                    result.digits.push(BigDigit::max_power_of_ten());
                } else {
                    let incremented_bigdigit = d0.incremented();
                    if incremented_bigdigit.is_power_of_ten() {
                        result.scale += 1;
                        let scaled_bigdigit = incremented_bigdigit / 10u8;
                        result.digits.push(scaled_bigdigit);
                    } else {
                        result.digits.push(rounded_d0);
                    }
                }
            }
            // case where we rounded up and have to carry values
            else {
                debug_assert_eq!(rounded, 10);
                debug_assert_eq!(d0, BigDigit::max());
                debug_assert_eq!(rounded_d0, 0);
                debug_assert_eq!(carry, BigDigit::one());

                match n.digits.argwhere(|&d| d != BigDigit::max()) {
                    // first-non-max index and bigdigit
                    Some((fnm_idx, fnm_bigdigit)) if fnm_idx + 1 < n.digits.len() => {
                        result.digits.resize(fnm_idx, BigDigit::zero());
                        result.digits.push(fnm_bigdigit.add_unchecked(1u8));
                        result.digits.extend_from_slice(&n.digits[fnm_idx+1..]);
                    },
                    // handle case where first-non-max bigdigit is the last digit
                    Some((fnm_idx, fnm_bigdigit)) => {
                        result.digits.resize(fnm_idx, BigDigit::zero());
                        let added_number = fnm_bigdigit.add_unchecked(1u8);
                        if !added_number.is_power_of_ten() {
                            result.digits.push(added_number);
                        } else {
                            // 9999 999999999
                            result.scale += 1;
                            result.digits.push(added_number / 10u32);
                        }
                    },
                    // very special case of nines going up to big digit boundary [999999999, 999999999]
                    // we "round back"
                    None => {
                        result.scale += 1;
                        result.digits.resize(n.digits.len() - 1, BigDigit::zero());
                        result.digits.push(BigDigit::max_power_of_ten());
                    }
                }
            }
        }
        // digit count is less than requested precision:
        // here we handle rounding (0, 0) to the right of our decimal
        Less => {
            let (fnz_digit, fnz_offset) = fnz_bigdigit.get_lowest_non_zero_digit();
            debug_assert_ne!(fnz_digit, 0);

            let new_prec_digit_count = precision.get() - digit_count;
            let (new_prec_bigdigit_count, new_prec_bigdigit_offset) = div_rem(
                new_prec_digit_count, bigdigit::MAX_DIGITS_PER_BIGDIGIT
            );

            result.scale -= new_prec_digit_count as i64;

            let rounded = if n.sign == Sign::Minus {
                rounding.round_digits(true, (9, 9))
            } else {
                rounding.round_digits(false, (0, 1))
            };

            // TODO: skip trailing zeros before making splitter
            let mut splitter = BigDigitSplitterIter::from_slice_shifting_left(&n.digits, new_prec_bigdigit_offset);

            match (n.sign, rounded) {
                // handle case where we rounded 'up' towards zero, and have to 'borrow'
                // from our first non zero bigdigit
                (Sign::Minus, 9) => {
                    result.digits.resize(new_prec_bigdigit_count, BigDigit::max());
                    while let Some(next_digit) = splitter.next() {
                        if next_digit.is_zero() {
                            result.digits.push(BigDigit::max());
                        } else {
                            let digit = next_digit.unchecked_sub(1u32);
                            match splitter.next() {
                                // special case where the last digit is 1
                                None if next_digit.is_one() => {
                                    result.scale -= 1;
                                    result.digits.push(BigDigit::from_raw_integer(9u32));
                                }
                                // we are subtracting from the the last digit which is a power of ten
                                // (e.g. 1000 -> 999), we are 'losing' a digit so must add an extra '9'
                                // and decrease the scale
                                None if next_digit.is_power_of_ten() => {
                                    result.scale -= 1;
                                    let bumped_digit = u32::from(digit) * 10 + 9;
                                    result.digits.push(BigDigit::from_raw_integer(bumped_digit));
                                }
                                None => {
                                    result.digits.push(digit);
                                }
                                Some(following_digit) => {
                                    result.digits.push(digit);
                                    result.digits.push(following_digit);
                                }
                            }
                            break;
                        }
                    }
                }
                (Sign::Minus, 10) | (_, 0) => {
                    result.digits.resize(new_prec_bigdigit_count, BigDigit::zero());
                }
                (_, 1) if new_prec_bigdigit_count == 0 => {
                    match splitter.next() {
                        Some(next_digit) => {
                            result.digits.push(next_digit.add_unchecked(1u32))
                        },
                        None => unreachable!()
                    }
                }
                (_, 1) if new_prec_bigdigit_count > 0 => {
                    result.digits.push(BigDigit::one());
                }
                _ => {
                    unreachable!();
                }
            };

            splitter.extend_vector(&mut result.digits);
        }
        Greater => {
            let idx = digit_count - precision.get();
            result.scale += idx as i64;

            let (index, offset) = div_rem(idx, bigdigit::MAX_DIGITS_PER_BIGDIGIT);

            let rounding_info = n.digits.get_rounding_info(idx);

            // simulate the addition of jot by changing the
            // digits used for rounding
            let rounding_pair = match (rounding_info.0, rounding_info.1, n.sign) {
                // -1.234000 + 1e-100 = -1.233999999....
                //       ^                    ^
                ((0, 0), true, Sign::Minus) => {
                    (9, 9)
                }
                // -1.234000 + 1e-100 = -1.233999999....
                //      ^                    ^
                ((l, 0), true, Sign::Minus) => {
                    (l - 1, 9)
                }
                //  1.234000 + 1e-100 =  1.234000..1
                // -1.234010 + 1e-100 = -1.2340099....
                //      ^                    ^
                ((l, 0), _, _) => {
                    (l, 1)
                }
                // 1.234500 + 1e-100 = 1.234500..1
                //     ^                   ^
                ((l, 5), true, Sign::Plus) => {
                    (l, 6)
                }
                // -1.234500 + 1e-100 = 1.234499..
                //      ^                   ^
                ((l, 5), true, Sign::Minus) => {
                    (l, 4)
                }
                // 1.234000 + 1e-100 = 1.234000..1
                //    ^                   ^
                ((l, r), _, _) => {
                    (l, r)
                }
            };
            let rounded = rounding.round_digits(n.sign == Sign::Minus, rounding_pair);

            let mut splitter = BigDigitSplitterIter::from_slice_shifting_right(
                &n.digits[index..], offset
            );

            // Push the rounded value into result
            match (rounding_info.0, rounding_info.1, n.sign, rounded) {
                // rounding had no effect - no special behavior
                ((x, _), _, _, y) if x == y => {
                }
                ((0, 0), true, Sign::Minus, 10) => { }
                // the case where we have to worry about rounding
                // while borrowing during 'subtraction'
                ((0, 0), true, Sign::Minus, 9) => {
                    while let Some(next_digit) = splitter.next() {
                        if next_digit.is_zero() {
                            result.digits.push(BigDigit::max());
                        } else {
                            result.digits.push(next_digit.unchecked_sub(1u8));
                            break;
                        }
                    }
                }
                // simply replace old digit in bigdecimal with the new (single) digit
                ((old_digit, _), _, _, new_digit) if new_digit < 10 => {
                    let next_bigdigit = splitter.next().unwrap();
                    let mut carry = BigDigit::from_raw_integer(new_digit);
                    // new_bigdigit = old_bigdigit - old_digit + new_digit
                    result.digits.push(next_bigdigit.sub_with_carry(old_digit, &mut carry));
                    debug_assert!(carry.is_zero());
                }
                // handle case of rounding-up to 10 and "carrying the one"
                ((old_digit, _), _, _, new_digit) => {
                    // new digit better be 10!
                    debug_assert_eq!(new_digit, 10);

                    let next_bigdigit = splitter.next().unwrap();
                    let mut carry = BigDigit::from_raw_integer(new_digit);
                    result.digits.push(next_bigdigit.sub_with_carry(old_digit, &mut carry));

                    let mut splitter_exhausted = false;
                    while !carry.is_zero() {
                        match splitter.next() {
                            Some(next_bigdigit) => {
                                result.digits.push(next_bigdigit.add_carry(&mut carry));
                            },
                            // we have overflowed, which is bad...
                            None => {
                                splitter_exhausted = true;
                                result.digits.push(carry);
                                break;
                            }
                        }
                    }

                    if !splitter_exhausted {
                        // we have to check if we happened to round on the last digit
                        match splitter.next() {
                            Some(next_bigdigit) => {
                                result.digits.push(next_bigdigit);
                            }
                            None => {
                                splitter_exhausted = true;
                            }
                        }
                    }

                    // if we exhausted the split digits while rounding, we have to scale back
                    if splitter_exhausted {
                        debug_assert_eq!(splitter.next(), None);
                        let last_idx = result.digits.len() - 1;
                        let last_digit = result.digits[last_idx];
                        if last_digit.is_one() {
                            result.scale += 1;
                            result.digits.truncate(last_idx);
                            debug_assert_eq!(result.digits[last_idx - 1], BigDigit::zero());
                            result.digits[last_idx - 1] = BigDigit::max_power_of_ten();
                        } else if last_digit.is_power_of_ten() {
                            result.scale += 1;
                            result.digits[last_idx] /= 10u8;
                            debug_assert_ne!(result.digits[last_idx], BigDigit::zero());
                        }
                    }
                }
            }
            result.digits.extend(splitter);
        }
    }

    // the result should have the precision number of digits requested
    debug_assert_eq!(result.count_digits(), precision.get() as usize);
}


#[cfg(test)]
#[allow(overflowing_literals)]
#[allow(unreachable_patterns)]
#[allow(non_snake_case)]
mod test_add_jot_into {
    use super::*;

    include!{ "../test_macros.rs" }

    macro_rules! impl_case {
        ($prec:literal, $rounding:ident => $($n:literal)* E $scale:literal) => {
            paste! {
                #[test]
                fn [< prec_ $prec _round_ $rounding >]() {
                    let data = case_input!();
                    let mut result = DigitInfo::default();
                    add_jot_into(&data, nonzero!($prec;usize), RoundingMode::$rounding, &mut result);
                    let expected = digit_info!($($n)* E $scale);
                    assert_eq!(result, expected);
                }
            }
        };
        ($prec:literal, $rounding:ident, $($multiple_rounding:ident),+ => - $($n:literal)* E $scale:literal) => {
            impl_case!($prec, $rounding => - $($n)* E $scale);
            impl_case!($prec, $($multiple_rounding),* => - $($n)* E $scale);
        };
        ($prec:literal, $rounding:ident, $($multiple_rounding:ident),+ => $($n:literal)* E $scale:literal) => {
            impl_case!($prec, $rounding => $($n)* E $scale);
            impl_case!($prec, $($multiple_rounding),* => $($n)* E $scale);
        };
    }

    mod case_84940950305270406218631_Eneg7 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!( 84940 950305270 406218631 E -7 ) }
        }

        impl_case!(13, Up => 8494 095030528 E 3);
        impl_case!(14, Up => 84940 950305271 E 2);
        impl_case!(15, Up => 849409 503052705 E 1);
        impl_case!(15, Down => 849409 503052704 E 1);
    }

    mod case_93881419894285022eneg14 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(93881419 894285022 E -14) }
        }

        impl_case!(8, Down => 93881419 E -5);
        impl_case!(8, Up => 93881420 E -5);

        impl_case!(14, Up, Ceiling => 93881 419894286 E -11);
        impl_case!(14, Down, HalfUp, HalfDown, HalfEven => 93881 419894285 E -11);

        impl_case!(17, Down => 93881419 894285022 E -14);
        impl_case!(17, Up => 93881419 894285023 E -14);

        impl_case!(19, Up => 9 388141989 428502201 E -16);
    }

    mod case_90000000000000000_e_neg14 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(90000000 000000000 E -14) }
        }

        impl_case!(19, Up => 9 000000000 000000001 E -16);
    }

    mod case_neg_87300000000000000000000000_e_2 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(-87300000 000000000 000000000 E 2) }
        }

        impl_case!(10, Up => -8 730000000 E 18);
        impl_case!(20, Up => -87 300000000 000000000 E 8);
        impl_case!(28, Up => -8 730000000 000000000 000000000 E 0);

        impl_case!(10, Down, Ceiling => -8 729999999 E 18);
        impl_case!(20, Down => -87 299999999 999999999 E 8);

        impl_case!(28, Down => -8 729999999 999999999 999999999 E 0);
    }


    mod case_99999995_e_0 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(99999995 E 0) }
        }

        impl_case!(5, Up => 10000 E 4);

        impl_case!(7, Up, Ceiling, HalfDown, HalfUp, HalfEven => 1000000 E 2);
        impl_case!(7, Down, Floor  => 9999999 E 1);
        impl_case!(8, Up, Ceiling => 99999996 E 0);
        impl_case!(8, Down, Floor, HalfDown, HalfUp, HalfEven  => 99999995 E 0);
    }

    mod case_999999995_e_0 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(999999995 E 0) }
        }

        impl_case!(5, Up => 10000 E 5);

        impl_case!(8, Up, Ceiling, HalfDown, HalfUp, HalfEven => 10000000 E 2);
        impl_case!(9, Up, Ceiling => 999999996 E 0);

        impl_case!(5, Down => 99999 E 4);

        impl_case!(8, Down, Floor => 99999999 E 1);
        impl_case!(9, Down, Floor, HalfDown, HalfUp, HalfEven => 999999995 E 0);
    }


    mod case_99999999_e_0 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(99999999 E 0) }
        }

        // impl_case!(5, Up => 10000 E 4);

        impl_case!(8, Up, Ceiling => 10000000 E 1);

        impl_case!(9, Up, Ceiling => 999999991 E -1);
        impl_case!(10, Up, Ceiling => 9 999999901 E -2);

        impl_case!(19, Up => 9 999999900 000000001 E -11);

        impl_case!(8, Down, Floor, HalfDown, HalfUp, HalfEven => 99999999 E 0);
        impl_case!(9, Down, Floor, HalfDown, HalfUp, HalfEven => 999999990 E -1);
        impl_case!(10, Down, Floor, HalfDown, HalfUp, HalfEven => 9 999999900 E -2);
        impl_case!(19, Down => 9 999999900 000000000 E -11);
    }

    mod case_999999999_e_0 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(999999999 E 0) }
        }

        impl_case!(5, Up => 10000 E 5);
        impl_case!(9, Up => 100000000 E 1);
        impl_case!(10, Up => 9 999999991 E -1);
        impl_case!(19, Up => 9 999999990 000000001 E -10);

        impl_case!(9, Down, Floor, HalfDown, HalfUp, HalfEven => 999999999 E 0);
        impl_case!(10, Down, Floor  => 9 999999990 E -1);
        impl_case!(19, Down => 9 999999990 000000000 E -10);
    }

    mod case_20999999999999999999_e_0 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(20 999999999 999999999 E 0) }
        }

        impl_case!(20, Up => 21 000000000 000000000 E 0);
        impl_case!(19, Up => 2 100000000 00000000 E 1);
        impl_case!(18, Up => 210000000 00000000 E 2);
    }

    mod case_29999999999999999999_e_0 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(29 999999999 999999999 E 0) }
        }

        impl_case!(20, Up => 30 000000000 000000000 E 0);
        impl_case!(19, Up => 3 000000000 00000000 E 1);
        impl_case!(18, Up => 300000000 00000000 E 2);
    }

    mod case_899999999999999999999999999_e_0 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(899999999 999999999 999999999 E 0) }
        }

        impl_case!(27, Up => 900000000 000000000 000000000 E 0);
        // impl_case!(19, Up => 3 000000000 00000000 E 1);
        // impl_case!(18, Up => 300000000 00000000 E 2);
    }


    mod case_999999999999999999999999_e_neg13 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(999999 999999999 999999999 E -13) }
        }

        impl_case!(12, Up, Ceiling, HalfDown, HalfEven, HalfUp => 100 000000000 E 0);
        impl_case!(24, Up => 100000 000000000 000000000 E -12);

        impl_case!(10, Down, Floor => 9 999999999 E 1);
        impl_case!(11, Down, Floor => 99 999999999 E 0);
        impl_case!(12, Down, Floor => 999 999999999 E -1);
        impl_case!(27, Down, Floor => 999999999 999999999 999999000 E -16);
        // impl_case!(19, Up => 3 000000000 00000000 E 1);
        // impl_case!(18, Up => 300000000 00000000 E 2);
    }

    mod case_999999999999999999999999999_e_neg7 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(999999999 999999999 999999999 E -7) }
        }

        impl_case!(27, Up => 100000000 000000000 000000000 E -6);
        impl_case!(27, Down => 999999999 999999999 999999999 E -7);
        // impl_case!(19, Up => 3 000000000 00000000 E 1);
        // impl_case!(18, Up => 300000000 00000000 E 2);
    }

    mod case_99999_e_10 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(99999 E 10) }
        }

        impl_case!(5, Up => 10000 E 11);
    }

    mod case_199999_e_0 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(199999 E 0) }
        }

        impl_case!(5, Up, Ceiling => 20000 E 1);

        impl_case!(6, Up, Ceiling => 200000 E 0);
        impl_case!(6, Down, Floor, HalfUp, HalfDown, HalfEven => 199999 E 0);

        impl_case!(16, HalfEven => 1999990 000000000 E -10);
    }

    mod case_neg_199999_e_0 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(-199999 E 0) }
        }

        impl_case!(6, Up => -199999 E 0);
        impl_case!(6, Down => -199998 E 0);
        impl_case!(6, Ceiling => -199998 E 0);
        impl_case!(6, Floor => -199999 E 0);
        impl_case!(6, HalfUp => -199999 E 0);
        impl_case!(6, HalfDown => -199999 E 0);
        impl_case!(6, HalfEven => -199999 E 0);
    }


    mod case_neg_14478775 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(-14478775 E 0) }
        }

        impl_case!(8, Up, Floor, HalfUp, HalfDown, HalfEven => -14478775 E 0);
        impl_case!(8, Down, Ceiling => -14478774 E 0);


        impl_case!(9, Up, Floor, HalfUp, HalfDown, HalfEven => -144787750 E -1);
        impl_case!(9, Down, Ceiling => -144787749 E -1);

        impl_case!(20, Up => -14 478775000 000000000 E -12);
        impl_case!(20, Down => -14 478774999 999999999 E -12);
    }

    mod case_neg_1000_e_neg3 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(-1000 E -3) }
        }

        // impl_case!(18, Up   => -100000000 000000000 E -17);

        impl_case!(19, Up   => -1 000000000 000000000 E -18);
        impl_case!(20, Up   => -10 000000000 000000000 E -19);

        impl_case!(16, Down => -9999999 999999999 E -16);
        impl_case!(17, Down => -99999999 999999999 E -17);
        impl_case!(18, Down => -999999999 999999999 E -18);
        impl_case!(19, Down => -9 999999999 999999999 E -19);
        impl_case!(20, Down => -99 999999999 999999999 E -20);

        impl_case!(24, Down => -999999 999999999 999999999 E -24);

        impl_case!(27, Down => -999999999 999999999 999999999 E -27);
    }

    mod case_neg_100000000_e_neg_60 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(-100000000 E -60) }
        }

        impl_case!(18, Up, Floor => -100000000 000000000 E -69);
        impl_case!(19, Up, Floor => -1 000000000 000000000 E -70);
        impl_case!(20, Up, Floor => -10 000000000 000000000 E -71);
        impl_case!(21, Up, Floor => -100 000000000 000000000 E -72);
        impl_case!(22, Up, Floor => -1000 000000000 000000000 E -73);
        impl_case!(23, Up, Floor => -10000 000000000 000000000 E -74);
        impl_case!(24, Up, Floor => -100000 000000000 000000000 E -75);
        impl_case!(25, Up, Floor => -1000000 000000000 000000000 E -76);

        impl_case!(18, Down, Ceiling => -999999999 999999999 E -70);
        impl_case!(19, Down, Ceiling => -9 999999999 999999999 E -71);
        impl_case!(20, Down, Ceiling => -99 999999999 999999999 E -72);
    }

    mod case_neg_1000000000_e_10 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(-1 000000000 E 10) }
        }

        // impl_case!(7, Down => -9999999 E 18);
        impl_case!(14, Down => -99999 999999999 E 5);
        impl_case!(15, Down => -999999 999999999 E 4);
        impl_case!(16, Down => -9999999 999999999 E 3);
        impl_case!(17, Down => -99999999 999999999 E 2);
        impl_case!(18, Down => -999999999 999999999 E 1);
        impl_case!(19, Down => -9 999999999 999999999 E 0);
        impl_case!(20, Down => -99 999999999 999999999 E -1);
        impl_case!(21, Down => -999 999999999 999999999 E -2);
        impl_case!(22, Down => -9999 999999999 999999999 E -3);
        impl_case!(27, Down => -999999999 999999999 999999999 E -8);
        impl_case!(28, Down => -9 999999999 999999999 999999999 E -9);

        impl_case!(18, Up => - 100000000 000000000 E 2);
        impl_case!(19, Up => -1 000000000 000000000 E 1);
        impl_case!(20, Up => -10 000000000 000000000 E 0);


        impl_case!(22, Up => -1000 000000000 000000000 E -2);

        impl_case!(27, Up => -100000000 000000000 000000000 E -7);
    }

    mod case_neg_10000000000_e_8 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(-10 000000000 E 8) }
        }

        impl_case!(20, Up, HalfUp, HalfDown => -10 000000000 000000000 E -1);

        impl_case!(20, Down, Ceiling => -99 999999999 999999999 E -2);

        impl_case!(21, Up, HalfUp, HalfDown => -100 000000000 000000000 E -2);
        impl_case!(21, Down, Ceiling => -999 999999999 999999999 E -3);

        // impl_case!(21, Up, HalfUp, HalfDown => -10 000000000 000000000 E -2);
    }

    mod case_neg_17801000000000 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(-17801 000000000 E 0) }
        }


        impl_case!(3, Up => -179 E 11);
        impl_case!(4, Up => -1781 E 10);
        impl_case!(5, Up => -17801 E 9);

        impl_case!(6, Up, Floor => -178010 E 8);

        impl_case!(11, Up, Floor, HalfUp, HalfEven, HalfDown => -17 801000000 E 3);
        impl_case!(14, Up, Floor => -17801 000000000 E 0);

        impl_case!(22, Up => -1780 100000000 000000000 E -8);
        impl_case!(23, Up => -17801 000000000 000000000 E -9);

        impl_case!(3, Down, Ceiling => -178 E 11);
        impl_case!(5, Down, Ceiling => -17800 E 9);
        impl_case!(6, Down, Ceiling => -178009 E 8);
        impl_case!(7, Down, Ceiling => -1780099 E 7);
        impl_case!(8, Down, Ceiling => -17800999 E 6);
        impl_case!(9, Down, Ceiling => -178009999 E 5);
        impl_case!(10, Down, Ceiling => -1 780099999 E 4);
        impl_case!(11, Down, Ceiling => -17 800999999 E 3);
        impl_case!(12, Down, Ceiling => -178 009999999 E 2);
        impl_case!(13, Down, Ceiling => -1780 099999999 E 1);

        impl_case!(14, Down, Ceiling => -17800 999999999 E 0);
        impl_case!(15, Down, Ceiling => -178009 999999999 E -1);

        impl_case!(20, Down, Ceiling => -17 800999999 999999999 E -6);
        impl_case!(21, Down => -178 009999999 999999999 E -7);

        impl_case!(22, Down => -1780 099999999 999999999 E -8);

        impl_case!(23, Down => -17800 999999999 999999999 E -9);
    }

    mod case_81710470447344799214256850000_E_neg26 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(81 710470447 344799214 256850000 E -26) }
        }


        impl_case!(15, Up, Ceiling, HalfDown, HalfEven, HalfUp => 817104 704473448 E -12);
        impl_case!(16, Up, Ceiling, HalfDown, HalfEven, HalfUp => 8171047 044734480 E -13);
        impl_case!(17, Up, Ceiling => 81710470 447344800 E -14);
        impl_case!(18, Up, Ceiling => 817104704 473447993 E -15);


        impl_case!(15, Down, Floor => 817104 704473447 E -12);

        impl_case!(17, Down, Floor => 81710470 447344799 E -14);
        impl_case!(18, Down, Floor, HalfDown, HalfEven, HalfUp  => 817104704 473447992 E -15);

        impl_case!(25, Up => 8171047 044734479 921425686 E -22);
        impl_case!(26, Up => 81710470 447344799 214256851 E -23);
        impl_case!(27, Up => 817104704 473447992 142568501 E -24);
        impl_case!(28, Up => 8 171047044 734479921 425685001 E -25);
        impl_case!(29, Up => 81 710470447 344799214 256850001 E -26);
        impl_case!(30, Up => 817 104704473 447992142 568500001 E -27);
    }

    mod case_747349068880200326999999999 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(7 473490688 802003267 999999999 E -14) }
        }

        impl_case!(28, Up => 7 473490688 802003268 000000000 E -14);
        impl_case!(28, Down => 7 473490688 802003267 999999999 E -14);
        impl_case!(30, Up => 747 349068880 200326799 999999901 E -16);
        impl_case!(30, Down => 747 349068880 200326799 999999900 E -16);
    }

    mod case_999999999999999995000000000 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(999999999 999999995 000000000 E 0) }
        }

        impl_case!(8, Up, HalfUp, HalfDown, HalfEven => 10000000 E 20);
        impl_case!(9, Up, HalfUp, HalfDown, HalfEven => 100000000 E 19);
        impl_case!(10, Up, HalfUp, HalfDown, HalfEven => 1 000000000 E 18);
        impl_case!(11, Up, HalfUp, HalfDown, HalfEven => 10 000000000 E 17);

        impl_case!(16, Up, HalfUp, HalfDown, HalfEven => 1000000 000000000 E 12);
        impl_case!(17, Up, HalfUp, HalfDown, HalfEven => 10000000 000000000 E 11);
        impl_case!(18, Up, Ceiling => 999999999 999999996 E 9);
        impl_case!(19, Up, Ceiling => 9 999999999 999999951 E 8);
        impl_case!(20, Up, Ceiling => 99 999999999 999999501 E 7);

        impl_case!(8, Down => 99999999 E 19);
        impl_case!(16, Down, Floor => 9999999 999999999 E 11);
        impl_case!(17, Down, Floor => 99999999 999999999 E 10);
        impl_case!(18, Down, Floor, HalfUp, HalfDown, HalfEven => 999999999 999999995 E 9);
        impl_case!(19, Down, Floor, HalfUp, HalfDown, HalfEven => 9 999999999 999999950 E 8);
        impl_case!(27, Down => 999999999 999999995 000000000 E 0);
        impl_case!(28, Down => 9 999999999 999999950 000000000 E -1);
        impl_case!(29, Down => 99 999999999 999999500 000000000 E -2);
    }

    mod case_999999999999999999999999999 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(999999999 999999999 999999999 E -2) }
        }

        impl_case!(20, Up => 10 000000000 000000000 E 6);
        impl_case!(27, Up => 100000000 000000000 000000000 E -1);
        impl_case!(27, Down => 999999999 999999999 999999999 E -2);
        impl_case!(28, Down => 9 999999999 999999999 999999990 E -3);
    }

    mod case_neg999999999999999999999999999 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(-999999999 999999999 999999999 E -2) }
        }

        impl_case!(27, Up => -999999999 999999999 999999999 E -2);
        impl_case!(27, Down => -999999999 999999999 999999998 E -2);
        impl_case!(28, Up, Floor => -9 999999999 999999999 999999990 E -3);
        impl_case!(28, Down => -9 999999999 999999999 999999989 E -3);

        impl_case!(58, Up, Floor => -9999 999999999 999999999 999990000 000000000 000000000 000000000 E -33);
        impl_case!(58, Down => -9999 999999999 999999999 999989999 999999999 999999999 999999999 E -33);
    }

    mod case_3999999999999999999999999999 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(3 999999999 999999999 999999999 E -2) }
        }

        impl_case!(28, Up => 4 000000000 000000000 000000000 E -2);
        impl_case!(28, Down => 3 999999999 999999999 999999999 E -2);
    }

    mod case_neg_3999999999999999999999999999Eneg7 {
        use super::*;

        macro_rules! case_input {
            () => { digit_info!(-3 999999999 999999999 999999999 E -7) }
        }

        impl_case!(21, Up => -400 000000000 000000000 E 0);
        impl_case!(26, Up => -40000000 000000000 000000000 E -5);
        impl_case!(27, Up => -400000000 000000000 000000000 E -6);
        impl_case!(28, Up => -3 999999999 999999999 999999999 E -7);
        impl_case!(32, Up => -39999 999999999 999999999 999990000 E -11);

        impl_case!(21, Down, Ceiling => -399 999999999 999999999 E 0);

        impl_case!(26, Down, Ceiling => -39999999 999999999 999999999 E -5);
        impl_case!(28, Down => -3 999999999 999999999 999999998 E -7);

        impl_case!(32, Down => -39999 999999999 999999999 999989999 E -11);
    }
}
