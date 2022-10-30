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
            subtract_digits_into_impl(a.as_ref(), b.as_ref(), precision, rounding, result)
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
    debug_assert_eq!(a.sign, b.sign);

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

    let a0 = a.digits[a_fnz_idx];
    let b0 = b.digits[b_fnz_idx];

    let mut borrow = BigDigit::zero();

    result.scale = a.scale;
    result.sign = a.sign;
    result.digits.push(BigDigit::sub_with_borrow(&a0, b0, &mut borrow));
    debug_assert_eq!(borrow, BigDigit::zero())
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
}
