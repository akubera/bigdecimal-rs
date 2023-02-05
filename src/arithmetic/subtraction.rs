//! Subtraction algorithms
//!
use std::num::NonZeroUsize;
use std::ops::{Neg, Not};

use crate::bigdigit::{
    self,
    BigDigit,
    BigDigitVec,
    BigDigitSplitterIter,
    BigDigitSliceSplitterIter,
    DigitInfo,
    DigitInfoRef,
    BigDigitLoc,
};

use crate::context::{Context, RoundingMode};
use crate::Sign;

use super::addition::add_digits_into_impl;


/// Calculate a - b
#[allow(unreachable_code)]
pub(crate) fn subtract_digits_into(
    a: &DigitInfo,
    b: &DigitInfo,
    precision: NonZeroUsize,
    rounding: RoundingMode,
    result: &mut DigitInfo
) {
    // route to something
    match (a.sign, b.sign, a.scale > b.scale) {
        (Sign::Plus, Sign::Minus, true) => {
            add_digits_into_impl(a.as_ref(), b.neg_ref(), precision, rounding, result)
        }
        (Sign::Plus, Sign::Minus, false) => {
            add_digits_into_impl(b.neg_ref(), a.as_ref(), precision, rounding, result)
        }
        (Sign::Minus, Sign::Plus, true) => {
            add_digits_into_impl(a.neg_ref(), b.as_ref(), precision, rounding, result)
        }
        (Sign::Minus, Sign::Plus, false) => {
            add_digits_into_impl(b.neg_ref(), a.as_ref(), precision, rounding, result)
        }
        (Sign::NoSign, _, _) => {
            result.copy_with_precision(b.neg_ref(), precision, rounding)
        }
        (_, Sign::NoSign, _) => {
            result.copy_with_precision(a.as_ref(), precision, rounding)
        }
        _ => {
            _call_subtract_digits_into_impl(a.as_ref(), b.as_ref(), precision, rounding, result)
        }
    }
}


pub(crate) fn _call_subtract_digits_into_impl(
    a: DigitInfoRef,
    b: DigitInfoRef,
    precision: NonZeroUsize,
    rounding: RoundingMode,
    result: &mut DigitInfo
) {
    use std::cmp::Ordering::*;
    debug_assert_eq!(a.sign, b.sign);

    match bigdigit::cmp_bigdigitvecs(&a.digits, a.scale, &b.digits, b.scale) {
        Equal => {
            result.digits.push(BigDigit::zero());
            result.sign = Sign::NoSign;
            result.scale = 0;
            return;
        }
        Greater => {
            subtract_digits_into_impl(a, b, precision, rounding, result)
        }
        Less => {
            subtract_digits_into_impl(b, a, precision, rounding, result);
            result.sign = result.sign.neg();
            return;
        }
    }
}

/// actual calculation of a - b
#[inline]
pub(crate) fn subtract_digits_into_impl(
    a: DigitInfoRef,
    b: DigitInfoRef,
    precision: NonZeroUsize,
    rounding: RoundingMode,
    result: &mut DigitInfo
) {
    use arithmetic::subtraction::BigDigitLoc::*;
    use std::cmp::Ordering::*;

    debug_assert_eq!(a.sign, b.sign);
    debug_assert_eq!(bigdigit::cmp_bigdigitvecs(a.digits, a.scale, b.digits, b.scale), Greater);

    // index of first non-zero bigdigit
    let (a_fnz_idx, b_fnz_idx) = {
        let nonzero_a = a.digits.position(|d| !d.is_zero());
        let nonzero_b = b.digits.position(|d| !d.is_zero());

        match (nonzero_a, nonzero_b) {
            (Some(a_idx), Some(b_idx)) => (a_idx, b_idx),
            (None, None) => {
                result.digits.push(BigDigit::zero());
                result.scale = 0;
                result.sign = Sign::Plus;
                return;
            }
            (None, _) => {
                result.copy_with_precision(b.neg(), precision, rounding);
                return;
            }
            (_, None) => {
                result.copy_with_precision(a, precision, rounding);
                return;
            }
        }
    };

    let trailing_zero_count_a = a_fnz_idx * bigdigit::MAX_DIGITS_PER_BIGDIGIT;
    let trailing_zero_count_b = b_fnz_idx * bigdigit::MAX_DIGITS_PER_BIGDIGIT;

    // ignore the trailing zeros
    let a_scale = a.scale + trailing_zero_count_a as i64;
    let b_scale = b.scale + trailing_zero_count_b as i64;

    // digit positions relative to smallest end of number
    //
    //   aaaaaaaa.aaaaaa
    //   │             └──────> a-low-pos=2
    //   └────────────────────> a-high-pos=15
    //       bbbb.bbbbbbbb
    //       │           └────> b-low-pos=0
    //       └────────────────> b-high-pos=11
    //
    let min_scale = i64::min(a_scale, b_scale);
    let a_low_pos = (a_scale - min_scale) as usize;
    let b_low_pos = (b_scale - min_scale) as usize;

    let a_high_pos = a.digits.count_digits() - trailing_zero_count_a + a_low_pos - 1;
    let b_high_pos = b.digits.count_digits() - trailing_zero_count_b + b_low_pos - 1;

    let digit_boundary = usize::max(a_high_pos, b_high_pos) + 1;

    if digit_boundary < precision.get() {
        todo!("Precision is greater than number of digits");
    }

    // position of first significant digit relative to smallest known digit
    let rounding_point = digit_boundary - precision.get();

    result.scale = a.scale + rounding_point as i64 - a_low_pos as i64;
    result.sign = a.sign;

    // trim trailing zeros from digit slices
    let (_, a_digits_nz) = a.digits.split_at(a_fnz_idx);
    let (_, b_digits_nz) = b.digits.split_at(b_fnz_idx);

    let (
        mut a_digits,
        a_loc,
        skipped_a_digits,
    ) = bigdigit::align_with(
        a_digits_nz,
        a_low_pos,
        a_high_pos,
        rounding_point,
        usize::min(b_low_pos, rounding_point),
    );

    let (
        mut b_digits,
        b_loc,
        skipped_b_digits,
    ) = bigdigit::align_with(
        b_digits_nz,
        b_low_pos,
        b_high_pos,
        rounding_point,
        usize::min(a_low_pos, rounding_point),
    );

    assert!(
          ((skipped_a_digits.len() > 0) ^ (skipped_b_digits.len() > 0))
        || (skipped_a_digits.len() == 0 && skipped_b_digits.len() == 0)
    );

    // handle cases where all digits are ignorable
    let (a_loc, b_loc) = match (a_loc, b_loc) {
        (None, None) => unreachable!(),
        (Some(a_loc), Some(b_loc)) => (a_loc, b_loc),
        (Some(a_loc), None) => {
            todo!("b is ignorable");
        }
        (None, Some(b_loc)) => {
            todo!("a is ignorable");
        }
    };

    let mut borrow = BigDigit::zero();
    let mut carry = BigDigit::zero();

    match (a_loc.low, b_loc.low) {
        (Insignificant(_), Insignificant(_)) => {
            let insig_digit = subtract_insig_digits(
                &mut a_digits, a_loc, skipped_a_digits,
                &mut b_digits, b_loc, skipped_b_digits,
                &mut borrow,
            );
            let (rounding_digit0, remaining) = insig_digit.split_highest_digit();
            let trailing_zeros = remaining == 0;

            match (a_digits.next(), b_digits.next()) {
                (Some(a_digit), Some(b_digit)) => {
                    let d0 = a_digit.sub_with_borrow(b_digit, &mut borrow);
                    let (
                        rounding_digit2,
                        rounding_digit1,
                    ) = rounding_digits(d0.as_digit_base());

                    let mut rounding_carry = BigDigit::zero();
                    let mut rounding_borrow = BigDigit::zero();
                    let rounded_d0 = make_rounded_value(
                        d0,
                        rounding,
                        result.sign,
                        (rounding_digit1, rounding_digit0),
                        trailing_zeros,
                        &mut rounding_borrow,
                        &mut borrow,
                        &mut carry,
                    );
                    result.digits.clear();
                    result.digits.push(rounded_d0);
                }
                _ => todo!(),
            }
        }
        _ => todo!()
    }


    loop {
        match (a_digits.next(), b_digits.next()) {
            (None, None) => break,
            (Some(a_digit), Some(b_digit)) => {
                let d = a_digit.sub_with_carry_borrow(&b_digit, &mut carry, &mut borrow);
                result.digits.push(d);
            }
            _ => todo!(),
        }
    }
}

#[cfg(test)]
#[allow(non_snake_case)]
mod test_subtract_digits_into {
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
                    subtract_digits_into(&a, &b, precision, mode, &mut result);
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
        ( - $($a:literal)+ E $a_exp:literal - - $($b:literal)+ E $b_exp:literal ) => {
            fn build_case_input() -> (DigitInfo, DigitInfo) {
                let a = digit_info!(- $($a)* E $a_exp);
                let b = digit_info!(- $($b)* E $b_exp);
                (a, b)
            }
        };
        ( -$($a:literal)+ E $a_exp:literal - $($b:literal)+ E $b_exp:literal ) => {
            fn build_case_input() -> (DigitInfo, DigitInfo) {
                let a = digit_info!(- $($a)* E $a_exp);
                let b = digit_info!($($b)* E $b_exp);
                (a, b)
            }
        };
        ( $($a:literal)+ E $a_exp:literal - - $($b:literal)+ E $b_exp:literal ) => {
            fn build_case_input() -> (DigitInfo, DigitInfo) {
                let a = digit_info!($($a)* E $a_exp);
                let b = digit_info!(- $($b)* E $b_exp);
                (a, b)
            }
        };
        ( $($a:literal)+ E $a_exp:literal - $($b:literal)+ E $b_exp:literal ) => {
            fn build_case_input() -> (DigitInfo, DigitInfo) {
                let a = digit_info!($($a)* E $a_exp);
                let b = digit_info!($($b)* E $b_exp);
                (a, b)
            }
        };
    }

    mod case_0_0 {
        use super::*;

        case_input! {
              0 E 0
            - 0 E 0
        }

        impl_case!(5 :: Up => 0 E 0);
    }

    mod case_10_1 {
        use super::*;

        case_input! {
              10 E 0
            - 1 E 0
        }

        impl_case!(1 :: Up => 9 E 0);
    }

    mod case_10_neg_1 {
        use super::*;

        case_input! {
              10 E 0
            - -1 E 0
        }

        impl_case!(2 :: Up => 11 E 0);
    }

    mod case_neg_10_1 {
        use super::*;

        case_input! {
              -10 E 0
            - 1 E 0
        }

        impl_case!(2 :: Up => -11 E 0);
    }


/// Perform subtraction of the region where the digits dont overlap
///
/// Handles both cases where 'a' digits or 'b' digts extend
/// beyond (i.e. to the right) of the other.
///
fn perform_nonoverlap_subtraction<'a, 'b, A: Iterator<Item = &'a BigDigit>, B: Iterator<Item = &'b BigDigit>>(
    a_digits: &mut BigDigitSplitterIter<'a, A>,
    b_digits: &mut BigDigitSplitterIter<'b, B>,
    a_start_pos: usize,
    b_start_pos: usize,
    borrow: &mut BigDigit,
    dest: &mut BigDigitVec,
) {
    if b_start_pos > a_start_pos {
        let count = b_start_pos - a_start_pos;
        copy_values_into(
            a_digits,
            count,
            dest
        );
    } else if a_start_pos > b_start_pos {
        let count = a_start_pos - b_start_pos;
        subtract_digits_from_zero(
            b_digits,
            count,
            borrow,
            dest
        );
    }
}


/// Perform <digits> - 0
///
fn copy_values_into<'a, I: Iterator<Item = &'a BigDigit>>(
    digits: &mut BigDigitSplitterIter<'a, I>,
    count: usize,
    dest: &mut BigDigitVec,
) {
    for i in 0..count {
        match digits.next() {
            None => {
                dest.resize(count - i, BigDigit::zero());
                break;
            }
            Some(digit) => {
                dest.push(digit)
            }
        }
    }
}


/// Perform 0 - <digits>
fn subtract_digits_from_zero<'a, I: Iterator<Item = &'a BigDigit>>(
    digits: &mut BigDigitSplitterIter<'a, I>,
    count: usize,
    borrow: &mut BigDigit,
    dest: &mut BigDigitVec,
) {
    let zero = BigDigit::zero();
    for _ in 0..count {
        match digits.next() {
            None => todo!(),
            Some(digit) => {
                dest.push(
                    zero.sub_with_borrow(digit, borrow)
                );
            }
        }
    }
}


fn subtract_insig_digits<'a>(
    a_digits: &mut BigDigitSliceSplitterIter<'a>,
    a_range: AlignmentRange,
    a_trailing_digits: &'a [BigDigit],
    b_digit_it: &mut BigDigitSliceSplitterIter<'a>,
    b_range: AlignmentRange,
    b_trailing_digits: &'a [BigDigit],
    borrow: &mut BigDigit,
) -> BigDigit
{
    use arithmetic::subtraction::BigDigitLoc::*;
    use std::cmp::Ordering::*;

    // either must have insignificant digits
    debug_assert!(
         match a_range.low { Insignificant(_) => true, _ => false }
      || match b_range.low { Insignificant(_) => true, _ => false }
    );

    debug_assert_eq!(borrow, &BigDigit::zero());

    match dbg!(a_range.low, b_range.low) {
        (Significant(_), Significant(_)) => unreachable!(),

        // "subtract" zeros from 'a'
        (Insignificant(a_lo), Significant(_)) => {
            for _ in 1..a_lo.get() {
                match a_digits.next() {
                    Some(_) => { }
                    None => { return BigDigit::zero(); }
                }
            }

            // return the last 'a' (or zero)
            return a_digits.next().unwrap_or(BigDigit::zero());
        }

        // handle case where 𝑎 has more insignificant digits than 𝑏
        (Insignificant(a_lo), Insignificant(b_lo)) if a_lo >= b_lo => {
            match dbg!(a_range.high, b_range.high) {
                (Insignificant(_), Insignificant(_)) => unreachable!(),
                (Significant(a_high), Insignificant(b_high)) => todo!(),

                // both digits span the rounding point
                (Significant(a_high), Significant(b_high)) => {
                    debug_assert!(a_high >= b_high);

                    for _ in 0..(a_lo.get() - b_lo.get()) {
                        a_digits.next().unwrap();
                    }

                    for _ in 1..b_lo.get() {
                        match (a_digits.next(), b_digit_it.next()) {
                            (Some(a_digit), Some(b_digit)) => {
                                let diff = a_digit.sub_with_borrow(b_digit, borrow);
                                dbg!(a_digit, b_digit, diff, &borrow);
                            }
                            _ => unreachable!()
                        }
                    }

                    match (a_digits.next(), b_digit_it.next()) {
                        (Some(a_digit), Some(b_digit)) => {
                            let diff = a_digit.sub_with_borrow(b_digit, borrow);
                            dbg!(a_digit, b_digit, diff, &borrow);
                            return diff;
                        }
                        _ => unreachable!()
                    }

                }
                _ => todo!(),
            }
        }
        _ => todo!()
    }
}
