//!
//! Addition algorithms BigDigit
//!

use std::num::NonZeroUsize;
use std::ops::Not;

use crate::bigdigit::{
    self, BigDigit, BigDigitVec, BigDigitSplitterIter, DigitInfo
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
    let a_end_pos = (a.scale - a.scale) as usize;
    let b_end_pos = (b.scale - a.scale) as usize;
    let a_start_pos = a.count_digits() - 1;
    let b_start_pos = b.count_digits() + b_end_pos - 1;

    let max_start_pos = usize::max(a_start_pos, b_start_pos);

    match max_start_pos.checked_sub(precision.get()) {
        // not enough digits to worry about precision/rounding
        None => {
            result.scale = a.scale;
            let (a_skip, b_shift) = div_rem(b_end_pos, bigdigit::MAX_DIGITS_PER_BIGDIGIT);
            let b_digits = BigDigitSplitterIter::from_slice_shifting_left(&b.digits, b_shift);
            // match a_skip.checked_sub(a.digits.len()) {
            //    None => {
            if a_skip < a.digits.len() {
                    let (only_a, a_digits) = a.digits.split_at(a_skip);
                    result.digits.extend_from_slice(&only_a);
                    let a_digits = BigDigitSplitterIter::from_slice_shifting_left(&a_digits, 0);
                    let mut carry = BigDigit::zero();
                    _impl_add_digits(a_digits, b_digits, &mut result.digits, &mut carry);
                    if !carry.is_zero() {
                        result.digits.push(carry);
                    }
                }
                // a & b are "disjoint" - we just copy the values
                // Some(_) => {
            else {
                    result.digits.extend_from_slice(&a.digits);
                    result.digits.resize(a_skip, BigDigit::zero());
                    b_digits.extend_vector(&mut result.digits);
            }
            return;
        }
        // digit count matches precision but digits are disjoint
        Some(0) if b_end_pos > a_start_pos + 1 => {
            result.scale = a.scale + 1;
            let (a_skip, b_shift) = div_rem(b_end_pos - 1, bigdigit::MAX_DIGITS_PER_BIGDIGIT);
            debug_assert!(a_skip > a.digits.len());
            let (rounding_pair, _) = a.digits.get_rounding_info(1);
            // let rounding_pair = div_rem((a.digits[0] % 100u32).as_u8(), 10);
            let rounded = rounding.round(result.sign, rounding_pair, true);
            let mut carry = BigDigit::from_raw_integer(rounded);
            let mut a_digits = BigDigitSplitterIter::from_slice_shifting_right(&a.digits, 1);
            let a0 = a_digits.next().unwrap();
            let rounded_a0 = a0.sub_with_carry(rounding_pair.0, &mut carry);
            result.digits.push(rounded_a0);

            while !carry.is_zero() {
                match a_digits.next() {
                    Some(digit) => result.digits.push(digit.add_carry(&mut carry)),
                    None => {
                        result.digits.push(carry);
                        unimplemented!();
                    }
                }
            }
            a_digits.extend_vector(&mut result.digits);
            result.digits.resize(a_skip, BigDigit::zero());

            let b_digits = BigDigitSplitterIter::from_slice_shifting_left(&b.digits, b_shift);
            b_digits.extend_vector(&mut result.digits);
            return;
        }
        // digit count matches precision - overflow *might* happen
        Some(0) => {
            result.scale = a.scale;
            let (a_skip, b_shift) = div_rem(b_end_pos, bigdigit::MAX_DIGITS_PER_BIGDIGIT);
            debug_assert!(a_skip < a.digits.len());
            let (only_a, a_digits) = a.digits.split_at(a_skip);
            result.digits.extend_from_slice(&only_a);
            let a_digits = BigDigitSplitterIter::from_slice(&a_digits);
            let b_digits = BigDigitSplitterIter::from_slice_shifting_left(&b.digits, b_shift);
            let mut carry = BigDigit::zero();
            _impl_add_digits(a_digits, b_digits, &mut result.digits, &mut carry);
            let overflowed = if !carry.is_zero() {
                result.digits.push(carry);
                true
            } else {
                result.digits.count_digits() > precision.get()
            };
            if overflowed {
                result.scale += 1;
                // round the sum to one decimal place
                let rounding_pair = div_rem((result.digits[0].as_digit_base() % 100) as u8, 10);
                let replacement_digit = rounding.round(result.sign, rounding_pair, true);
                result.digits.shift_right_and_replace_digit(1, replacement_digit.into());
            }
        }
        // a is too small to affect b
        Some(insignificant_pos) if b_end_pos > a_start_pos && insignificant_pos > a_start_pos => {
            add_jot_into(b, precision, rounding, result);
        }
        // b digits are all significant, rounding *might* not be affected by a
        // sum does not "start" before the precision/rounding point
        Some(insignificant_pos) if insignificant_pos < b_end_pos => {
            let significant_pos = insignificant_pos + 1;
            result.scale = a.scale + significant_pos as i64;

            // insignificant_a is the digit-index of the first insignificant digit
            let (sig_a_index, sig_a_offset) = div_rem(significant_pos, bigdigit::MAX_DIGITS_PER_BIGDIGIT);
            let rounded = a.digits.round_at(rounding, result.sign, significant_pos);

            // iterator over significant digits
            let mut a_digits = BigDigitSplitterIter::from_slice_shifting_right(
                &a.digits[sig_a_index..], sig_a_offset
            );

            let (a_skip, b_offset) = div_rem(b_end_pos - significant_pos, bigdigit::MAX_DIGITS_PER_BIGDIGIT);
            let mut b_digits = BigDigitSplitterIter::from_slice_shifting_left(&b.digits, b_offset);

            let a0 = match a_digits.next() {
                Some(a0) => a0,
                None => unreachable!(),
            };

            let old_digit = a0 % 10u8;
            let mut carry = BigDigit::from_raw_integer(rounded);
            let rounded_a0 = a0.sub_with_carry(old_digit, &mut carry);

            // case where b-digits start within the rounded a-bigdigit
            if a_skip == 0 {
                let b0 = b_digits.next().unwrap();
                let mut tmp = BigDigit::zero();
                let sum0 = rounded_a0.add_with_carry(&b0, &mut tmp);
                result.digits.push(sum0);
                carry.add_assign(tmp);
            } else {
                result.digits.push(rounded_a0);
                for _ in 1..a_skip {
                    match a_digits.next() {
                        None => {
                            result.digits.push(carry);
                            carry = BigDigit::zero();
                        }
                        Some(a_digit) => {
                            result.digits.push(a_digit.add_carry(&mut carry));
                        }
                    }
                }
            }
            _impl_add_digits(a_digits, b_digits, &mut result.digits, &mut carry);
            if !carry.is_zero() {
                result.digits.push(carry);
            }
        }
        // more digits than precision - we *must* round
        Some(insignificant_pos) => {
            let significant_pos = insignificant_pos + 1;
            result.scale = a.scale + significant_pos as i64;

            // the case where b_end_pos > significant_pos is handled
            // in the above match arm
            let significant_b = significant_pos - b_end_pos;

            // align a and b digits to the "significant" position
            // by (virtually) adding zeros to the end (right side
            // of the digits)

            // 12345678 => (12345 678000000)
            //     ^ pos=3        ^^^ bottom_digits=3
            let a_keeps_bottom_n_digits = significant_pos % bigdigit::MAX_DIGITS_PER_BIGDIGIT;
            let b_keeps_bottom_n_digits = significant_b % bigdigit::MAX_DIGITS_PER_BIGDIGIT;

            let shift_factor = if a_keeps_bottom_n_digits == 0 {
                0
            } else {
                bigdigit::MAX_DIGITS_PER_BIGDIGIT - a_keeps_bottom_n_digits
            };

            // shift b's lowest digit position relative to a's lowest digit position
            let shift_b_end = b_end_pos + shift_factor;
            let shift_significant_b = significant_b + shift_factor;

            // skip any insignificant 'a' bigdigits which do not overlap
            // with 'b' digits
            let shifted_a_digits_to_skip = shift_b_end / bigdigit::MAX_DIGITS_PER_BIGDIGIT;
            let (sig_b_index, sig_b_offset) = div_rem(
                shift_significant_b, bigdigit::MAX_DIGITS_PER_BIGDIGIT
            );

            let mut trailing_zeros = true;

            // we need to know which aligned a-digit matches
            // the first b digit
            //
            // this is an optimization so we don't add the trailing
            // zeros of 'b'
            let mut a_digits = if shifted_a_digits_to_skip == 0 {
                // not skipping any bigdigits in a
                BigDigitSplitterIter::from_slice_starting_bottom(
                    &a.digits, a_keeps_bottom_n_digits
                )
            } else if shift_factor == 0 {
                let (insig_a_digits, sig_a_digits) = a.digits.split_at(shifted_a_digits_to_skip);
                trailing_zeros = insig_a_digits.iter().all(BigDigit::is_zero);
                BigDigitSplitterIter::from_slice(sig_a_digits)
            } else {
                let (insig_a_digits, sig_a_digits) = a.digits.split_at(
                    shifted_a_digits_to_skip - 1
                );
                trailing_zeros = insig_a_digits.iter().all(BigDigit::is_zero);

                if !trailing_zeros {
                    BigDigitSplitterIter::from_slice_shifting_right(
                        sig_a_digits, a_keeps_bottom_n_digits
                    )
                } else {
                    let mut digits = BigDigitSplitterIter::from_slice_starting_bottom(
                        sig_a_digits, a_keeps_bottom_n_digits
                    );
                    let skipped_digits = digits.next().unwrap();
                    trailing_zeros &= skipped_digits.is_zero();
                    digits
                }
            };

            let mut b_digits = BigDigitSplitterIter::from_slice_starting_bottom(
                &b.digits, b_keeps_bottom_n_digits
            );

            let mut carry = BigDigit::zero();

            // loop through insignificant sums to calculate the carry
            // start at 1 to skip the last
            for i in 1..sig_b_index {
                match (a_digits.next(), b_digits.next()) {
                    (None, None) => {
                        unreachable!();
                    }
                    (Some(a_digit), Some(b_digit)) => {
                        let sum = BigDigit::add_with_carry(&a_digit, &b_digit, &mut carry);
                        trailing_zeros &= sum.is_zero();
                    }
                    (Some(digit), None) | (None, Some(digit)) if carry.is_zero() => {
                        trailing_zeros &= digit.is_zero();
                    }
                    (Some(digit), None) | (None, Some(digit)) => {
                        let sum = digit.add_carry(&mut carry);
                        trailing_zeros &= sum.is_zero();
                    }
                }
            }

            // the last insignificant addition
            let a_digit = a_digits.next().unwrap();
            let b_digit = b_digits.next().unwrap();
            let insig_sum = BigDigit::add_with_carry(&a_digit, &b_digit, &mut carry);

            // the first significant addition
            let a0 = a_digits.next().unwrap_or(BigDigit::zero());
            let b0 = b_digits.next().unwrap_or(BigDigit::zero());
            let s0 = BigDigit::add_with_carry(&a0, &b0, &mut carry);

            let (low_digit, remainder) = insig_sum.split_highest_digit();
            trailing_zeros &= remainder == 0;
            let high_digit = s0.lowest_digit();
            let rounding_pair = (high_digit, low_digit as u8);

            let rounded = rounding.round(result.sign, rounding_pair, trailing_zeros);
            let mut tmp =  BigDigit::from_raw_integer(rounded);
            let rounded_sum = s0.sub_with_carry(high_digit, &mut tmp);
            carry.add_assign(tmp);

            result.digits.push(rounded_sum);
            _impl_add_digits(a_digits, b_digits, &mut result.digits, &mut carry);
            let overflowed = if !carry.is_zero() {
                result.digits.push(carry);
                true
            } else {
                result.digits.count_digits() > precision.get()
            };

            if overflowed {
                result.scale += 1;
                // round the sum to one decimal place
                let rounding_pair = div_rem((result.digits[0].as_digit_base() % 100) as u8, 10);
                let replacement_digit = rounding.round(result.sign, rounding_pair, true);
                result.digits.shift_right_and_replace_digit(1, replacement_digit.into());
            }
        }
    }

    debug_assert_eq!(result.count_digits(), precision.get() as usize);
}


/// Does not push final carry
///
/// Should this return overflow?
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
                continue;
            }
            (Some(a_digit), None) => {
                sum.push(a_digit.add_carry(carry));
                while !carry.is_zero() {
                    if let Some(a_digit) = a_digits.next() {
                        sum.push(a_digit.add_carry(carry));
                    } else {
                        return;
                    }
                }
                a_digits.extend_vector(sum);
            }
            (None, Some(b_digit)) => {
                sum.push(b_digit.add_carry(carry));
                while !carry.is_zero() {
                    if let Some(b_digit) = b_digits.next() {
                        sum.push(b_digit.add_carry(carry));
                    } else {
                        return;
                    }
                }
                b_digits.extend_vector(sum);
            }
            (None, None) => { }
        }
        return;
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
