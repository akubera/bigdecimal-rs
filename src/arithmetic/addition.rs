//!
//! Addition algorithms BigDigit
//!

use std::num::NonZeroUsize;
use std::ops::Not;

use crate::bigdigit::{
    self, BigDigit, BigDigitVec, BigDigitBaseDouble, BigDigitSplitterIter,
    DigitInfo, to_power_of_ten, MAX_DIGITS_PER_BIGDIGIT
};

use crate::context::{Context, RoundingMode};

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
        digit_shift as usize, MAX_DIGITS_PER_BIGDIGIT
    );

    result.extend_from_slice(&b[..skip]);

    if a_offset == 0 {
        return extend_digit_slice_sum_into(a, &b[skip..], result);
    }

    let mut aligned_a_digits = BigDigitSplitterIter::new(a_offset as u32, a.iter());
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
}


/// Add an insignificant number to n, respecting rounding and precision rules
///
/// This is to be used by functions which detect that one of the operands in
/// an addition operation is too small to have an effect on the other, but
/// rounding may be required.
///
#[inline]
pub(crate) fn add_jot_into(
    n: &DigitInfo,
    precision: NonZeroUsize,
    rounding: RoundingMode,
    result: &mut DigitInfo
) {
    use crate::Sign;
    use crate::Ordering::*;

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
            let high = (d0 % 10) as u8;

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
                        let scaled_bigdigit = incremented_bigdigit / 10;
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
                        result.digits.push(fnm_bigdigit.add_unchecked(1u32));
                        result.digits.extend_from_slice(&n.digits[fnm_idx+1..]);
                    },
                    // handle case where first-non-max bigdigit is the last digit
                    Some((fnm_idx, fnm_bigdigit)) => {
                        result.digits.resize(fnm_idx, BigDigit::zero());
                        let added_number = fnm_bigdigit.add_unchecked(1u32);
                        if !added_number.is_power_of_ten() {
                            result.digits.push(added_number);
                        } else {
                            // 9999 999999999
                            result.scale += 1;
                            result.digits.push(added_number / 10);
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
            let (new_prec_bigdigit_count, new_prec_bigdigit_offset) = div_rem(new_prec_digit_count, MAX_DIGITS_PER_BIGDIGIT);

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

            let (index, offset) = div_rem(idx, MAX_DIGITS_PER_BIGDIGIT);

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
                // 1.234000 + 1e-100 = 1.234000..1
                //     ^                   ^
                ((l, 0), true, _) => {
                    (l, 1)
                }
                // -1.234010 + 1e-100 = -1.2340099....
                //      ^                    ^
                ((l, 0), false, Sign::Minus) => {
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
                            result.digits.resize(last_idx, BigDigit::zero());
                            debug_assert_eq!(result.digits[last_idx - 1], BigDigit::zero());
                            result.digits[last_idx - 1] = BigDigit::max_power_of_ten();
                        } else if last_digit.is_power_of_ten() {
                            result.scale += 1;
                            result.digits[last_idx] /= 10;
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
