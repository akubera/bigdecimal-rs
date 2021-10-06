// \file src/context.rs

//! A `Context` object is the set of parameters that define otherwise
//! ambiguous arithmetical operations.
//!
//! Each BigDecimal object has its own context object, and all
//! operations will follow the more 'restricted' rule.

#![allow(unreachable_code)]

use num_integer::Integer;
use num_integer::div_mod_floor;
use num_integer::div_rem;

use num_traits::Zero;
use crate::Sign;

use crate::BigDecimal;
use crate::bigdigit::BigDigitBase;
use crate::bigdigit::BigDigitBaseDouble;
use crate::bigdigit::MAX_DIGITS_PER_BIGDIGIT;
use crate::bigdigit::BIG_DIGIT_RADIX;
use crate::bigdigit::IntoBigDigitVec;
use crate::bigdigit::convert_to_base_u32_vec;
// use crate::arithmetic::multiplication::multiply_digit_vecs_into;

macro_rules! ten_to_pow {
    ($n:expr) => {{
        match $n {
            0 => 1,
            1 => 10,
            2 => 100,
            3 => 1000,
            4 => 10000,
            5 => 100000,
            6 => 1000000,
            7 => 10000000,
            8 => 100000000,
            9 => 1000000000,
            _ => unreachable!(),
        }
    }};
}

macro_rules! digit_vec {
    ( (FROM-BASE-TEN) $e:expr ) => {{
        // change base to 2^32
        let (high, low) = div_rem($e, 1 << 32);
        if high == 0 {
            digit_vec![low as u32]
        } else {
            digit_vec![low as u32, high as u32]
        }
    }};
    // ( (FROM-BASE-TEN) [$e:expr ) => {{
    //     // change base to 2^32
    //     let (high, low) = div_rem($e, 1 << 32);
    //     if high == 0 {
    //         digit_vec![low as u32]
    //     } else {
    //         digit_vec![low as u32, high as u32]
    //     }
    // }};
    ( $($e:expr),* ) => {
        vec![$($e),*]
    };
}

/// Information regarding behavior of certain BigDecimal operations
///
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct Context {
    /// The maximum number of digits to store
    pub precision: u64,

    /// Method to round numbers
    pub rounding_mode: RoundingMode,
}

#[cfg(test)]
mod test_to_decimal_bytes {
    use super::*;
    use std::str::FromStr;

    #[test]
    fn test_1() {
        let bigint = num_bigint::BigInt::from_str("1234").unwrap();
        let dec_digits = IntoBigDigitVec::into(&bigint);
        assert_eq!(&dec_digits, &[1234]);
    }
}

fn count_significant_digits(n: BigDigitBase) -> usize {
    if n < 10 {
        1
    } else {
        (n as f64).log10().floor() as usize + 1
    }
}

fn count_total_significant_digits(digit_vec: &[BigDigitBase]) -> usize {
    let high_digit_block = digit_vec.last().unwrap();
    count_significant_digits(*high_digit_block) + (digit_vec.len() - 1) * MAX_DIGITS_PER_BIGDIGIT
}

#[inline(always)]
fn estimate_dec_digit_count(bigdigit_count: usize, digit_base: BigDigitBaseDouble) -> usize {
    let output_digit_per_bigdigit = (digit_base as f64).log10();

    (bigdigit_count as f64 * output_digit_per_bigdigit).ceil() as usize
}

/// Information containing digits and location used for rounding a
/// number expressed as a BigDigit slice.
///
#[derive(PartialEq, Debug)]
struct RoundingInfo {
    /// digit to the left of rounding point
    pub left: u8,
    /// digit to the right of rounding point
    pub right: u8,
    /// slice location of rounding point in BigDigit slice
    pub index: usize,
    /// offset in bigdigit of rounding point in BigDigit slice
    pub offset: u8,
    /// true if all trailing decimals following rounding point are zero
    pub suffix_zeros: bool,
    /// power of ten used to mask digits (10^(offset-1))
    pub digit_mask: u64,
}

impl RoundingInfo {
    #[inline]
    pub fn from(digit_vec: &[BigDigitBase], rounding_point: usize) -> RoundingInfo {
        if rounding_point == 0 {
            return RoundingInfo {
                left: (digit_vec[0] % 10) as u8,
                right: 0,
                index: 0,
                offset: 0,
                suffix_zeros: true,
                digit_mask: 1,
            };
        }

        let (digit_index, digit_offset) = div_rem(rounding_point, MAX_DIGITS_PER_BIGDIGIT);
        let digit_mask = ten_to_pow!(digit_offset.saturating_sub(1));

        if digit_index >= digit_vec.len() {
            return RoundingInfo {
                left: 0,
                right: 0,
                index: digit_index,
                offset: digit_offset as u8,
                suffix_zeros: digit_vec.iter().all(|&d| d == 0),
                digit_mask: digit_mask,
            };
        }

        debug_assert!(digit_index < digit_vec.len());

        let (left_digit, right_digit) = if digit_offset == 0 {
            let high = digit_vec[digit_index] % 10;
            let low = digit_vec[digit_index - 1] / 100000000;
            (high, low)
        } else {
            let shifted_digits = digit_vec[digit_index] as u64 / digit_mask;
            let high = ((shifted_digits / 10) % 10) as u32;
            let low = (shifted_digits % 10) as u32;
            (high, low)
        };

        let trailing_zeros =
            (digit_vec[digit_index] as u64 % digit_mask) == 0 && digit_vec[..digit_index].iter().all(|d| *d == 0);

        return RoundingInfo {
            left: left_digit as u8,
            right: right_digit as u8,
            index: digit_index,
            offset: digit_offset as u8,
            suffix_zeros: trailing_zeros,
            digit_mask: digit_mask,
        };
    }
}

fn get_rounding_digit_pair(digit_vec: &[BigDigitBase], rounding_point: usize) -> (u8, u8) {
    if rounding_point == 0 {
        let (higher_digits, first_digit) = div_rem(digit_vec[0], 10);
        return ((higher_digits % 10) as u8, first_digit as u8);
    }

    let get_ten_to_pow = |n| match n {
        0 => 1,
        1 => 10,
        2 => 100,
        3 => 1000,
        4 => 10000,
        5 => 100000,
        6 => 1000000,
        7 => 10000000,
        8 => 100000000,
        9 => 1000000000,
        _ => unreachable!(),
    };

    let (digit_index, digit_offset) = div_rem(rounding_point, MAX_DIGITS_PER_BIGDIGIT);

    if digit_index >= digit_vec.len() {
        return (0, 0);
    }

    debug_assert!(digit_index < digit_vec.len());

    #[rustfmt::skip]
    let (left_digit, right_digit) = match (digit_index, digit_offset) {
        (0, 0) => { unreachable!() }
        (idx, 0) => {
            ((digit_vec[idx] / 10) % 10, digit_vec[idx] % 10)
        }
        (idx, 8) if (idx+1) == digit_vec.len() => {
            (0, digit_vec[idx] / (BIG_DIGIT_RADIX / 10) as BigDigitBase)
        }
        (idx, 8) => {
            (digit_vec[idx + 1] % 10, digit_vec[idx] / (BIG_DIGIT_RADIX / 10) as BigDigitBase)
        }
        (idx, off) => {
            let pow_ten = get_ten_to_pow(off);
            let shifted_digits = digit_vec[idx] / pow_ten;
            ((shifted_digits / 10) % 10, shifted_digits % 10)
        }
    };

    return (left_digit as u8, right_digit as u8);
}

#[cfg(test)]
mod test_get_rounding_digit_pair {
    use super::*;
    use crate::bigdigit;
    use num_bigint::BigInt;
    use std::str::FromStr;

    macro_rules! test_case {
        ($idx:literal; $left:literal, $right:literal, $index:expr, $offset:expr, $suffix_zeros:literal) => {
            paste! {
                #[test]
                fn [< test_case_index_ $idx >] () {
                    let rounding_info = RoundingInfo::from(&DIGITS, $idx);
                    let expected = RoundingInfo {
                        left: $left,
                        right: $right,
                        index: $index,
                        offset: $offset,
                        suffix_zeros: $suffix_zeros,
                        digit_mask: ten_to_pow!( ($offset as u8).saturating_sub(1) ),
                    };

                    assert_eq!(rounding_info, expected);
                }
            }
        };
        ($idx:literal; $left:literal, $right:literal, $index:literal, $offset:literal) => {
            test_case!($idx; $left, $right, $index, $offset, false);
        };
        ($idx:literal; $left:literal, $right:literal, $trailing_zeros:literal) => {
            test_case!($idx; $left, $right, $idx / MAX_DIGITS_PER_BIGDIGIT, $idx % MAX_DIGITS_PER_BIGDIGIT as u8, $trailing_zeros);
        };
        ($idx:literal; $left:literal, $right:literal) => {
            test_case!($idx; $left, $right, false);
        };
    }

    mod case_8013663911278000000000000000 {
        use super::*;

        lazy_static! {
            static ref DIGITS: Vec<BigDigitBase> = bigdigit::to_bigdigit_vec(
                BigInt::from_str("8013663911278000000000000000")
                    .unwrap()
                    .iter_u64_digits(),
                std::u64::MAX as u128 + 1
            );
        }

        test_case!(0; 0, 0, 0, 0, true);
        test_case!(1; 0, 0, 0, 1, true);
        test_case!(2; 0, 0, 0, 2, true);
        test_case!(8; 0, 0, true);
        test_case!(9; 0, 0, true);
        test_case!(10; 0, 0, true);
        test_case!(15; 8, 0, true);
        test_case!(16; 7, 8, true);
        test_case!(17; 2, 7, false);
        test_case!(19; 1, 1, false);
        test_case!(27; 8, 0, false);
        test_case!(28; 0, 8, false);
    }

    mod case_5825884393831776092094971288 {
        use super::*;

        lazy_static! {
            static ref DIGITS: Vec<BigDigitBase> = bigdigit::to_bigdigit_vec(
                BigInt::from_str("5825884393831776092094971288")
                    .unwrap()
                    .iter_u64_digits(),
                std::u64::MAX as u128 + 1
            );
        }

        test_case!(0; 8, 0, 0, 0, true);
        test_case!(1; 8, 8, 0, 1, true);
        test_case!(2; 2, 8, 0, 2);
        test_case!(3; 1, 2);
        test_case!(4; 7, 1);
        test_case!(7; 9, 4);
        test_case!(8; 0, 9);
        test_case!(9; 2, 0);
        test_case!(10; 9, 2);
        test_case!(12; 6, 0);
        test_case!(18; 3, 8);
        test_case!(19; 9, 3);
        test_case!(20; 3, 9);
        test_case!(26; 8, 2);
        test_case!(27; 5, 8);
        test_case!(28; 0, 5);
        test_case!(29; 0, 0);
    }

    macro_rules! make_test_case {
        ($idx:literal; $left:literal, $right:literal) => {
            paste! {
                #[test]
                fn [< test_case_index_ $idx >] () {
                    let (l, r) = get_rounding_digit_pair(&DIGITS, $idx);
                    assert_eq!((l, r), ($left, $right));
                }
            }
        };
    }

    #[test]
    fn _0_123() {
        let (l, r) = get_rounding_digit_pair(&[321], 0);
        assert_eq!(l, 2);
        assert_eq!(r, 1);

        let (l, r) = get_rounding_digit_pair(&[123], 1);
        assert_eq!(l, 1);
        assert_eq!(r, 2);
    }

    mod case_12345678900 {
        use super::*;

        lazy_static! {
            static ref DIGITS: Vec<BigDigitBase> = bigdigit::to_bigdigit_vec(
                BigInt::from_str("12345678900").unwrap().iter_u64_digits(),
                crate::MAX_BIG_DIGIT_BASE_DOUBLE
            );
        }

        make_test_case!(0; 0, 0);
        make_test_case!(2; 8, 9);
        make_test_case!(7; 3, 4);
        make_test_case!(8; 2, 3);
        make_test_case!(9; 1, 2);
    }

    mod case_6394267984578837493714331685623619705438 {
        use super::*;

        lazy_static! {
            static ref DIGITS: Vec<BigDigitBase> = bigdigit::to_bigdigit_vec(
                BigInt::from_str("6394267984578837493714331685623619705438")
                    .unwrap()
                    .iter_u64_digits(),
                crate::MAX_BIG_DIGIT_BASE_DOUBLE
            );
        }
        make_test_case!(33; 6, 7);
        make_test_case!(34; 2, 6);
    }

    mod case_639426798457883776 {
        use super::*;

        lazy_static! {
            static ref DIGITS: Vec<BigDigitBase> = bigdigit::to_bigdigit_vec(
                BigInt::from_str("639426798457883776").unwrap().iter_u64_digits(),
                std::u64::MAX as u128 + 1
            );
        }

        make_test_case!(0; 7, 6);
        make_test_case!(1; 7, 7);
        make_test_case!(5; 7, 8);
        make_test_case!(6; 5, 7);
        make_test_case!(8; 8, 4);
        make_test_case!(9; 9, 8);
        make_test_case!(10; 7, 9);

        make_test_case!(15; 3, 9);
        make_test_case!(16; 6, 3);
        make_test_case!(17; 0, 6);
        make_test_case!(18; 0, 0);
        make_test_case!(19; 0, 0);
    }

    mod case_5825884393831776092094988288 {
        use super::*;

        lazy_static! {
            static ref DIGITS: Vec<BigDigitBase> = bigdigit::to_bigdigit_vec(
                BigInt::from_str("5825884393831776092094988288")
                    .unwrap()
                    .iter_u64_digits(),
                std::u64::MAX as u128 + 1
            );
        }

        make_test_case!(1; 2, 8);
        make_test_case!(11; 6, 0);
        make_test_case!(17; 3, 8);
        make_test_case!(18; 9, 3);
        make_test_case!(19; 3, 9);
        make_test_case!(25; 8, 2);
    }
}

impl Context {
    pub fn with_rounding(&self, mode: RoundingMode) -> Context {
        Context {
            precision: self.precision,
            rounding_mode: mode,
        }
    }

    /// Round decimal to n digits
    ///
    /// ```
    /// let ctx = Context::default();
    /// let d = BigDecimal::from_str("3.14159").unwrap();
    /// assert_eq!(ctx.round(&d, 3), BigDecimal::from_str("3.142").unwrap());
    /// ```
    ///
    /// Providing a negative number of digits rounds to the left of
    /// the decimal point
    /// ```
    /// let ctx = Context::default();
    /// let d = BigDecimal::from_str("13345.234").unwrap();
    /// assert_eq!(
    ///    ctx.with_rounding(RoundingMode::Up).round(&d, -2),
    ///    BigDecimal::from_str("13300").unwrap()
    /// );
    ///
    /// assert_eq!(
    ///    ctx.with_rounding(RoundingMode::Up).round(&d, -1),
    ///    BigDecimal::from_str("13350").unwrap()
    /// );
    ///
    /// assert_eq!(
    ///    ctx.with_rounding(RoundingMode::Up).round(&d, -6),
    ///    BigDecimal::from_str("1e6").unwrap()
    /// );
    /// ```
    pub fn round(&self, decimal: &BigDecimal, n_digits: i64) -> BigDecimal {
        // index of digit from 'right' of the decimal point
        //
        // |------[decimal_digit_count = 40]-------|
        //    |----------[scale = 38]--------------|
        // 63.94267984578837493714331685623619705438
        //        ^------[rounding_point = 33]-----|  (if n_digits = 5)
        //  ^------------[rounding_point = 38]-----|  (if n_digits = 0)
        //                  [rounding_point = 0]---^  (if n_digits = 38)
        //
        let rounding_point = decimal.scale - n_digits;

        // no rounding to do, just clone the decimal
        if rounding_point == 0 {
            return decimal.clone();
        }

        let digit_vec: Vec<BigDigitBase> = IntoBigDigitVec::into(&decimal.int_val);

        // we are extending precision of the decimal (to the right),
        // increase bigint and set 'ndigits' as the scale
        if rounding_point < 0 {
            // TODO: check if precision should play a part here
            let trailing_zeros = (-rounding_point) as usize;

            let (zero_bigdigit_count, offset) = div_rem(trailing_zeros, MAX_DIGITS_PER_BIGDIGIT);

            let mut new_digits = Vec::with_capacity(digit_vec.len() + 1 + zero_bigdigit_count);
            new_digits.resize(zero_bigdigit_count, 0);

            if offset == 0 {
                new_digits.extend_from_slice(&digit_vec);
            } else {
                let digit_splitter = ten_to_pow!(MAX_DIGITS_PER_BIGDIGIT - offset);
                let digit_shifter = ten_to_pow!(offset);

                // let mut i = new_digits.len() - 1;

                new_digits.push(0);
                for (&digit, i) in digit_vec.iter().zip(new_digits.len() - 1..) {
                    let (high, low) = div_rem(digit, digit_splitter);
                    // *new_digits.last_mut().unwrap() += low * digit_shifter;
                    new_digits[i] += low * digit_shifter;
                    new_digits.push(high);
                    // i += 1;
                }
            }

            let new_digits = crate::bigdigit::convert_to_base_u32_vec(&new_digits);
            let int_val = crate::BigInt::new(decimal.sign(), new_digits);

            return BigDecimal {
                int_val: int_val,
                scale: n_digits,
                context: decimal.context.clone(),
            };
        }

        // at this point, rounding_point > 0
        let rounding_point = rounding_point as usize;
        let rounding_info = RoundingInfo::from(&digit_vec, rounding_point);
        dbg!(&rounding_info);

        let rounded_digit = match (
            self.rounding_mode,
            decimal.sign(),
            rounding_info.left,
            rounding_info.right,
            rounding_info.suffix_zeros,
        ) {
            // all digits following "left" are zero -> never change "left"
            (_, _, left, 0, true) => left,
            // Towards +∞
            (RoundingMode::Ceiling, Sign::Plus, left, _, _) => left + 1,
            (RoundingMode::Ceiling, Sign::NoSign, left, _, _) => left,
            (RoundingMode::Ceiling, Sign::Minus, left, _, _) => left,
            // Away from 0
            (RoundingMode::Up, _, left, _, _) => left + 1,
            // Handle rounding-point = 5
            (RoundingMode::HalfUp, _, left, 5, true) => left + 1,
            (RoundingMode::HalfUp, _, left, right, _) => left + (right >= 5) as u8,
            (RoundingMode::HalfEven, _, left, 5, true) => left + left % 2,
            (RoundingMode::HalfEven, _, left, right, _) => left + (right >= 5) as u8,
            (RoundingMode::HalfDown, _, left, 5, true) => left,
            (RoundingMode::HalfDown, _, left, right, _) => left + (right >= 5) as u8,
            // Towards 0
            (RoundingMode::Down, _, left, _, _) => left,
            // Towards -∞
            (RoundingMode::Floor, Sign::Plus | Sign::NoSign, left, _, _) => left,
            (RoundingMode::Floor, Sign::Minus, left, _, _) => left + 1,
        } as BigDigitBaseDouble;

        dbg!(&rounded_digit);

        let digit_shifter = ten_to_pow!(rounding_info.offset);
        let digit_booster = ten_to_pow!(MAX_DIGITS_PER_BIGDIGIT as u8 - rounding_info.offset);

        // rounding to the left of the decimal point
        if n_digits < 0 {
            if digit_vec.len() == rounding_info.index + 1 {
                let number = digit_vec[rounding_info.index] as BigDigitBaseDouble;
                let shifted_number = number / digit_shifter;
                let new_digit_number = (shifted_number - shifted_number % 10) + rounded_digit;
                let new_digits = digit_vec![ (FROM-BASE-TEN) new_digit_number ];

                return BigDecimal {
                    int_val: crate::BigInt::new(decimal.sign(), new_digits),
                    scale: n_digits,
                    context: decimal.context.clone(),
                };
            }
        }

        if digit_vec.len() < rounding_info.index {
            let digit = match (decimal.sign(), self.rounding_mode) {
                (_, RoundingMode::Up) => 1,
                (Sign::Minus, RoundingMode::Ceiling) => 0,
                (Sign::NoSign, RoundingMode::Ceiling) => 0,
                (Sign::Plus, RoundingMode::Ceiling) => 1,
                (_, RoundingMode::Down) => 0,
                (Sign::Minus, RoundingMode::Floor) => 1,
                (Sign::NoSign, RoundingMode::Floor) => 0,
                (Sign::Plus, RoundingMode::Floor) => 0,
                (_, RoundingMode::HalfUp) => 0,
                (_, RoundingMode::HalfDown) => 0,
                (_, RoundingMode::HalfEven) => 0,
            };

            return BigDecimal {
                int_val: crate::BigInt::new(decimal.sign(), vec![digit]),
                scale: n_digits,
                context: decimal.context.clone(),
            };
        }

        // only process one digit
        if digit_vec.len() - rounding_info.index == 1 {
            let number = digit_vec[rounding_info.index] as BigDigitBaseDouble;
            let shifted_number = number / digit_shifter;
            let new_digit_number = (shifted_number - shifted_number % 10) + rounded_digit;
            let new_digits = digit_vec![ (FROM-BASE-TEN) new_digit_number ];

            return BigDecimal {
                int_val: crate::BigInt::new(decimal.sign(), new_digits),
                scale: n_digits,
                context: decimal.context.clone(),
            };
        }

        let d0 = {
            let number = digit_vec[rounding_info.index] as BigDigitBaseDouble;
            let x = number / digit_shifter;
            x - x % 10 + rounded_digit
        };
        dbg!(d0);

        if rounding_info.offset == MAX_DIGITS_PER_BIGDIGIT as u8 - 1 {
            let tmp = digit_vec[rounding_info.index + 1] as BigDigitBaseDouble;
            let next_digit = tmp - tmp % 10 + d0;
            let result = if next_digit >= BIG_DIGIT_RADIX {
                let mut v = Vec::with_capacity(digit_vec.len() - rounding_info.index);
                v.push(next_digit as BigDigitBase);
                v.extend_from_slice(&digit_vec[rounding_info.index + 2..]);
                v
            } else {
                let (mut carry, x) = div_rem(next_digit, BIG_DIGIT_RADIX);
                let mut v = Vec::with_capacity(digit_vec.len() - rounding_info.index + 1);
                v.push(x as BigDigitBase);
                let mut it = digit_vec[rounding_info.index + 2..].iter();
                while carry != 0 {
                    match it.next() {
                        None => {
                            v.push(carry as BigDigitBase);
                            carry = 0;
                        }
                        Some(&next_digit) => {
                            let (crry, x) = div_rem(next_digit as BigDigitBaseDouble + carry, BIG_DIGIT_RADIX);
                            v.push(x as BigDigitBase);
                            carry = crry;
                        }
                    }
                }

                for next_digit in it {
                    v.push(*next_digit);
                }

                v
            };

            let new_digits = crate::bigdigit::convert_to_base_u32_vec(&result);

            let int_val = crate::BigInt::new(decimal.sign(), new_digits);
            let scale = n_digits;
            let context = decimal.context.clone();

            return BigDecimal {
                int_val,
                scale,
                context,
            };
        }

        // let approx_bigdigit_count = digit_vec.len() * MAX_DIGITS_PER_BIGDIGIT - rounding_point;
        let approx_bigdigit_count = (digit_vec.len() * MAX_DIGITS_PER_BIGDIGIT)
            .saturating_sub(rounding_point)
            .max(1);
        dbg!(approx_bigdigit_count);
        // let approx_bigdigit_count = estimate_dec_digit_count(digit_vec.len(), 100000);

        let mut result = Vec::with_capacity(approx_bigdigit_count);

        let d_i = digit_vec[rounding_info.index + 1] as BigDigitBaseDouble;
        dbg!(d_i);

        let (h, l) = div_rem(d_i, digit_shifter);
        dbg!(h);
        dbg!(l);

        let (mut carry, x) = div_rem(d0 + (l * digit_booster), BIG_DIGIT_RADIX);
        dbg!(carry);
        dbg!(x);
        result.push(x as BigDigitBase);
        result.push(h as BigDigitBase);
        dbg!(&result);

        let mut i = 2;

        // while std::intrinsics::unlikely(carry != 0) {
        while carry != 0 {
            debug_assert_eq!(carry, 1);

            if rounding_info.index + i == digit_vec.len() {
                let new_digits = vec![0];
                let int_val = crate::BigInt::new(decimal.sign(), new_digits);
                let scale = n_digits;
                let context = decimal.context.clone();

                return BigDecimal {
                    int_val,
                    scale,
                    context,
                };
            }

            let d_i = digit_vec[rounding_info.index + i] as BigDigitBaseDouble;
            let (h, l) = div_rem(d_i, digit_shifter);

            let (crry, x) = div_rem(
                result[i - 1] as BigDigitBaseDouble + (l * digit_booster) + carry,
                BIG_DIGIT_RADIX,
            );
            carry = crry;

            result[i - 1] = x as BigDigitBase;
            result.push(h as BigDigitBase);

            i += 1;
        }

        dbg!(dbg!(rounding_info.index + i) < dbg!(digit_vec.len()));
        while rounding_info.index + i < digit_vec.len() {
            let d_i = digit_vec[rounding_info.index + i] as BigDigitBaseDouble;
            let (h, l) = div_rem(d_i, digit_shifter);
            result[i - 1] += (l * digit_booster) as BigDigitBase;
            result.push(h as BigDigitBase);
            i += 1;
        }

        let new_digits = crate::bigdigit::convert_to_base_u32_vec(&result);

        let int_val = crate::BigInt::new(decimal.sign(), new_digits);
        let scale = n_digits;
        let context = decimal.context.clone();

        return BigDecimal {
            int_val,
            scale,
            context,
        };
    }
}

impl Default for Context {
    fn default() -> Context {
        Context {
            precision: 34,
            rounding_mode: RoundingMode::HalfUp,
        }
    }
}

/// Determines how to calculate the last digit of the number
///
/// Default rounding mode is HalfUp
///
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum RoundingMode {
    /// Always round away from zero
    ///
    ///
    /// * 5.5 -> 6.0
    /// * 2.5 -> 3.0
    /// * 1.6 -> 2.0
    /// * 1.1 -> 2.0
    /// * 1.0 -> 1.0
    /// * -1.0 -> -1.0
    /// * -1.1 -> -2.0
    /// * -1.6 -> -2.0
    /// * -2.5 -> -3.0
    /// * -5.5 -> -6.0
    Up,

    /// Always round towards zero
    ///
    /// |  |      |
    /// |-----:|:-----|
    /// | 5.5  | 5.0  |
    /// | 2.5  | 2.0  |
    /// | 1.6  | 1.0  |
    /// | 1.1  | 1.0  |
    /// | 1.0  | 1.0  |
    /// | -1.0 | -1.0 |
    /// | -1.1 | -1.0 |
    /// | -1.6 | -1.0 |
    /// | -2.5 | -2.0 |
    /// | -5.5 | -5.0 |
    Down,

    /// Towards +∞
    ///
    /// * 5.5 -> 6.0
    /// * 2.5 -> 3.0
    /// * 1.6 -> 2.0
    /// * 1.1 -> 2.0
    /// * 1.0 -> 1.0
    /// * -1.0 -> -1.0
    /// * -1.1 -> -1.0
    /// * -1.6 -> -1.0
    /// * -2.5 -> -2.0
    /// * -5.5 -> -5.0
    Ceiling,

    /// Towards -∞
    ///
    /// * 5.5 -> 5.0
    /// * 2.5 -> 2.0
    /// * 1.6 -> 1.0
    /// * 1.1 -> 1.0
    /// * 1.0 -> 1.0
    /// * -1.0 -> -1.0
    /// * -1.1 -> -2.0
    /// * -1.6 -> -2.0
    /// * -2.5 -> -3.0
    /// * -5.5 -> -6.0
    Floor,

    /// Round to 'nearest neighbor', or up if ending decimal is 5
    ///
    /// * 5.5 -> 6.0
    /// * 2.5 -> 3.0
    /// * 1.6 -> 2.0
    /// * 1.1 -> 1.0
    /// * 1.0 -> 1.0
    /// * -1.0 -> -1.0
    /// * -1.1 -> -1.0
    /// * -1.6 -> -2.0
    /// * -2.5 -> -3.0
    /// * -5.5 -> -6.0
    HalfUp,

    /// Round to 'nearest neighbor', or down if ending decimal is 5
    ///
    /// * 5.5 -> 5.0
    /// * 2.5 -> 2.0
    /// * 1.6 -> 2.0
    /// * 1.1 -> 1.0
    /// * 1.0 -> 1.0
    /// * -1.0 -> -1.0
    /// * -1.1 -> -1.0
    /// * -1.6 -> -2.0
    /// * -2.5 -> -2.0
    /// * -5.5 -> -5.0
    HalfDown,

    /// Round to 'nearest neighbor', if equidistant, round towards
    /// nearest even digit
    ///
    /// * 5.5 -> 6.0
    /// * 2.5 -> 2.0
    /// * 1.6 -> 2.0
    /// * 1.1 -> 1.0
    /// * 1.0 -> 1.0
    /// * -1.0 -> -1.0
    /// * -1.1 -> -1.0
    /// * -1.6 -> -2.0
    /// * -2.5 -> -2.0
    /// * -5.5 -> -6.0
    HalfEven,
}

#[cfg(test)]
#[allow(non_snake_case)]
#[allow(non_upper_case_globals)]
mod test_rounding {
    use super::*;
    use std::str::FromStr;

    macro_rules! test_case {
        (- $n:literal, $mode:ident; $expected:literal) => {
            paste! {
                #[test]
                fn [< to_neg $n _ $mode >]() {
                    test_case!(IMPL -$n, $mode; $expected);
                }
            }
        };
        ($n:literal, $mode:ident; $expected:literal) => {
            paste! {
                #[test]
                fn [< to_ $n _ $mode >]() {
                    test_case!(IMPL $n, $mode; $expected);
                }
            }
        };
        (IMPL $n:literal, $mode:ident; $expected:literal) => {
            let expected = BigDecimal::from_str($expected).unwrap();
            let ctx = Context {
                rounding_mode: RoundingMode::$mode,
                ..Context::default()
            };
            let result = ctx.round(&test_decimal, $n);
            assert_eq!(result, expected);
            assert_eq!(result.int_val, expected.int_val);
        };
    }

    mod case_393_070615 {
        use super::*;

        lazy_static! {
            static ref test_decimal: BigDecimal = BigDecimal::from_str("393.070615").unwrap();
        }

        test_case!(7, Down; "393.0706150");

        test_case!(6, Down; "393.070615");
        test_case!(6, Up; "393.070615");
        test_case!(6, HalfEven; "393.070615");
        test_case!(6, HalfUp; "393.070615");

        test_case!(5, Down; "393.07061");
        test_case!(5, Up; "393.07062");
        test_case!(5, HalfEven; "393.07062");
        test_case!(5, HalfDown; "393.07061");
        test_case!(5, HalfUp; "393.07062");

        test_case!(4, Down; "393.0706");
        test_case!(4, Up; "393.0707");

        test_case!(3, Down; "393.070");
        test_case!(3, HalfDown; "393.071");
        test_case!(3, HalfUp; "393.071");
        test_case!(3, Up; "393.071");

        test_case!(1, Down; "393.0");
        test_case!(1, Up; "393.1");
        test_case!(1, HalfEven; "393.1");
        test_case!(1, HalfUp; "393.1");
        test_case!(1, HalfDown; "393.1");

        test_case!(0, Down; "393");
        test_case!(0, Up; "394");

        // test_case!(-1, Up; "400");
        // test_case!(-1, Down; "390");

        // test_case!(-2, Up; "4");
        // test_case!(-2, Down; "3");

        test_case!(7, r#Up; "393.0706150");
        test_case!(10, Up; "393.0706150000");
        test_case!(18, Up; "393.070615000000000000");
    }

    mod case_63_9426798457883749371433168562361970543862 {
        use super::*;

        lazy_static! {
            static ref test_decimal: BigDecimal =
                BigDecimal::from_str("63.9426798457883749371433168562361970543862").unwrap();
        }

        test_case!(40, Down; "63.9426798457883749371433168562361970543862");
        test_case!(39, Up;   "63.942679845788374937143316856236197054387");
        test_case!(39, Down; "63.942679845788374937143316856236197054386");
        test_case!(35, Down; "63.94267984578837493714331685623619705");
        test_case!(34, Down; "63.9426798457883749371433168562361970");
        test_case!(33, Down; "63.942679845788374937143316856236197");
        test_case!(32, Down; "63.94267984578837493714331685623619");
        test_case!(31, Down; "63.9426798457883749371433168562361");
        test_case!(30, Down; "63.942679845788374937143316856236");

        test_case!(20, Down; "63.94267984578837493714");
        test_case!(10, Down; "63.9426798457");
        test_case!(1, Down; "63.9");
    }

    mod case_4_9942985969742650387930033522Em11 {
        use super::*;

        lazy_static! {
            static ref test_decimal: BigDecimal = BigDecimal::from_str("4.9942985969742650387930033522E-11").unwrap();
        }
        test_case!(0, Down; "0");
        test_case!(11, Down; "0.00000000004");
        test_case!(12, Down; "0.000000000049");
        test_case!(14, HalfEven; "0.00000000004994");
        test_case!(14, Ceiling; "0.00000000004995");
    }

    mod case_9_999999900em9 {
        use super::*;

        lazy_static! {
            static ref test_decimal: BigDecimal = BigDecimal::from_str("9.999999900E-9").unwrap();
        }

        test_case!(9, Up; "1.0E-8");
    }

    // #[test]
    // pub fn round_up() {
    //     let cases = [(5, "", "63.94267")];

    //     for (prec, src, expected) in cases.iter() {
    //         let ctx = Context {
    //             precision: *prec,
    //             rounding_mode: RoundingMode::Down,
    //         };

    //         let d = BigDecimal::from_str(src).unwrap();
    //         let r = ctx.round(&d, *prec);
    //         assert_eq!(r, BigDecimal::from_str(expected).unwrap());
    //     }
    // }

    /*
    #[test]
    #[rustfmt::skip]
    pub fn round_expanding_right() {
        let cases = [
            (6, RoundingMode::Up, "393.070612", "393.070612"),
            (7, RoundingMode::Up, "393.070612", "393.0706120"),
            (6, RoundingMode::Down, "393.070612", "393.070612"),
            (7, RoundingMode::Down, "393.070612", "393.0706120"),
            (10, RoundingMode::Down, "393.070612", "393.0706120000"),
            // (5, RoundingMode::Down, "393.070612", "393.07061"),
            // (5, RoundingMode::Up, "393.070612", "393.07062"),
        ];
        for (ndigits, mode, src, expected) in cases.iter() {
            let ctx = Context {
                rounding_mode: *mode,
                ..Context::default()
            };

            let d = BigDecimal::from_str(src).unwrap();
            let r = ctx.round(&d, *ndigits);
            assert_eq!(r, BigDecimal::from_str(expected).unwrap());
        }
    }
    */

    #[test]
    #[rustfmt::skip]
    pub fn round_too_large() {
        let cases = [
            (-4, RoundingMode::Up, "393.070612", "10000"),
            (-5, RoundingMode::Up, "393.070612", "100000"),
            (-5, RoundingMode::Ceiling, "393.070612", "100000"),
            (-6, RoundingMode::HalfEven, "393.070612", "0"),
            (-5, RoundingMode::Down, "393.070612", "0"),
            (-5, RoundingMode::Down, "393.070612", "0"),
            (-10, RoundingMode::Down, "500.070", "0"),
            (-5, RoundingMode::Down, "9999.9999", "0"),
        ];
        for (ndigits, mode, src, expected) in cases.iter() {
            let ctx = Context {
                rounding_mode: *mode,
                ..Context::default()
            };
            let d = BigDecimal::from_str(src).unwrap();
            let r = ctx.round(&d, *ndigits);
            assert_eq!(r, BigDecimal::from_str(expected).unwrap());
        }
    }

    #[test]
    pub fn round_most_significant_digit() {
        let cases = [
            (-3, RoundingMode::HalfEven, "500", "0"),
            (-3, RoundingMode::HalfUp, "500", "10000"),
        ];
        for (ndigits, mode, src, expected) in cases.iter() {
            let ctx = Context {
                rounding_mode: *mode,
                ..Context::default()
            };

            let d = BigDecimal::from_str(src).unwrap();
            let r = ctx.round(&d, *ndigits);
            assert_eq!(r, BigDecimal::from_str(expected).unwrap());
        }
    }

    #[test]
    #[rustfmt::skip]
    pub fn round_12_34567() {
        let cases = [
            (0, RoundingMode::Down, "393.070612", "393.1"),
            // (1, RoundingMode::Down, "393.070612", "393.1"),
            // (2, RoundingMode::Down, "393.070612", "393.07"),
            // (3, RoundingMode::Down, "393.070612", "393.070"),
            // (4, RoundingMode::Down, "393.070612", "393.0706"),
            // (5, RoundingMode::Down, "393.070612", "393.07061"),
            // (5, RoundingMode::Up, "393.070612", "393.07062"),
        ];
        for (ndigits, mode, src, expected) in cases.iter() {
            let ctx = Context {
                rounding_mode: *mode,
                ..Context::default()
            };

            let d = BigDecimal::from_str(src).unwrap();
            let r = ctx.round(&d, *ndigits);
            assert_eq!(r, BigDecimal::from_str(expected).unwrap());
        }
    }
    #[test]
    #[rustfmt::skip]
    pub fn round_393_070612() {
        let cases = [
            (1, RoundingMode::Down, "393.070612", "393.1"),
            // (2, RoundingMode::Down, "393.070612", "393.07"),
            // (3, RoundingMode::Down, "393.070612", "393.070"),
            // (4, RoundingMode::Down, "393.070612", "393.0706"),
            // (5, RoundingMode::Down, "393.070612", "393.07061"),
            // (5, RoundingMode::Up, "393.070612", "393.07062"),
        ];
        for (ndigits, mode, src, expected) in cases.iter() {
            let ctx = Context {
                rounding_mode: *mode,
                ..Context::default()
            };

            let d = BigDecimal::from_str(src).unwrap();
            let r = ctx.round(&d, *ndigits);
            assert_eq!(r, BigDecimal::from_str(expected).unwrap());
        }
    }

    // #[rustfmt::skip]
    // #[test]
    // pub fn round_down() {
    //     let cases = [
    //         (
    //             25,
    //             "63.94267984578837493714331685623619705438",
    //             "63.9426798457883749371433169",
    //         ),
    //         (   5,
    //             "63.94267984578837493714331685623619705438",
    //             "63.94267",
    //         ),
    //     ];

    //     for (prec, src, expected) in cases.iter() {
    //         let ctx = Context {
    //             rounding_mode: RoundingMode::Down,
    //             ..Context::default()
    //         };

    //         let d = BigDecimal::from_str(src).unwrap();
    //         let r = ctx.round(&d, *prec);
    //         assert_eq!(r, BigDecimal::from_str(expected).unwrap());
    //     }
    // }
}
