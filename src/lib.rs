// Copyright 2016 Adam Sunderland
//           2016-2023 Andrew Kubera
//           2017 Ruben De Smet
// See the COPYRIGHT file at the top-level directory of this
// distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A Big Decimal
//!
//! `BigDecimal` allows storing any real number to arbitrary precision; which
//! avoids common floating point errors (such as 0.1 + 0.2 ≠ 0.3) at the
//! cost of complexity.
//!
//! Internally, `BigDecimal` uses a `BigInt` object, paired with a 64-bit
//! integer which determines the position of the decimal point. Therefore,
//! the precision *is not* actually arbitrary, but limited to 2<sup>63</sup>
//! decimal places.
//!
//! Common numerical operations are overloaded, so we can treat them
//! the same way we treat other numbers.
//!
//! It is not recommended to convert a floating point number to a decimal
//! directly, as the floating point representation may be unexpected.
//!
//! # Example
//!
//! ```
//! use bigdecimal::BigDecimal;
//! use std::str::FromStr;
//!
//! let input = "0.8";
//! let dec = BigDecimal::from_str(&input).unwrap();
//! let float = f32::from_str(&input).unwrap();
//!
//! println!("Input ({}) with 10 decimals: {} vs {})", input, dec, float);
//! ```
#![cfg_attr(not(feature = "std"), no_std)]
#![allow(clippy::style)]
#![allow(clippy::unreadable_literal)]
#![allow(clippy::needless_return)]
#![allow(clippy::suspicious_arithmetic_impl)]
#![allow(clippy::suspicious_op_assign_impl)]
#![allow(clippy::redundant_field_names)]


pub extern crate num_bigint;
pub extern crate num_traits;
extern crate num_integer;

#[cfg(feature = "serde")]
extern crate serde;

#[cfg(feature = "std")]
include!("./with_std.rs");

#[cfg(not(feature = "std"))]
include!("./without_std.rs");

// make available some standard items
use self::stdlib::cmp::{self, Ordering};
use self::stdlib::convert::TryFrom;
use self::stdlib::default::Default;
use self::stdlib::hash::{Hash, Hasher};
use self::stdlib::num::{ParseFloatError, ParseIntError};
use self::stdlib::ops::{Add, AddAssign, Div, Mul, Neg, Rem, Sub};
use self::stdlib::iter::Sum;
use self::stdlib::str::FromStr;
use self::stdlib::string::{String, ToString};
use self::stdlib::fmt;

use num_bigint::{BigInt, BigUint, ParseBigIntError, Sign};
use num_integer::Integer as IntegerTrait;
pub use num_traits::{FromPrimitive, Num, One, Signed, ToPrimitive, Zero};

use stdlib::f64::consts::LOG2_10;


// const DEFAULT_PRECISION: u64 = ${RUST_BIGDECIMAL_DEFAULT_PRECISION} or 100;
include!(concat!(env!("OUT_DIR"), "/default_precision.rs"));

#[macro_use]
mod macros;

#[cfg(test)]
extern crate paste;

// From<T>, To<T>, TryFrom<T> impls
mod impl_convert;
// Add<T>, Sub<T>, etc...
mod impl_ops;
mod impl_ops_add;
mod impl_ops_sub;
mod impl_ops_mul;
mod impl_ops_div;
mod impl_ops_rem;

// PartialEq
mod impl_cmp;

// Implementations of num_traits
mod impl_num;

mod parsing;
pub mod rounding;
pub use rounding::RoundingMode;

// Mathematical context
mod context;
pub use context::Context;

/// Return 10^pow
///
/// Try to calculate this with fewest number of allocations
///
fn ten_to_the(pow: u64) -> BigInt {
    ten_to_the_uint(pow).into()
}

/// Return 10^pow
fn ten_to_the_uint(pow: u64) -> BigUint {
    if pow < 20 {
        return BigUint::from(10u64.pow(pow as u32));
    }

    // linear case of 10^pow = 10^(19 * count + rem)
    if pow < 590 {
        let ten_to_nineteen = 10u64.pow(19);

        // count factors of 19
        let (count, rem) = pow.div_rem(&19);

        let mut res = BigUint::from(ten_to_nineteen);
        for _ in 1..count {
            res *= ten_to_nineteen;
        }
        if rem != 0 {
            res *= 10u64.pow(rem as u32);
        }

        return res;
    }

    // use recursive algorithm where linear case might be too slow
    let (quotient, rem) = pow.div_rem(&16);
    let x = ten_to_the_uint(quotient);

    let x2 = &x * &x;
    let x4 = &x2 * &x2;
    let x8 = &x4 * &x4;
    let res = &x8 * &x8;

    if rem == 0 {
        res
    } else {
        res * 10u64.pow(rem as u32)
    }
}


/// Return number of decimal digits in integer
fn count_decimal_digits(int: &BigInt) -> u64 {
    count_decimal_digits_uint(int.magnitude())
}

/// Return number of decimal digits in unsigned integer
fn count_decimal_digits_uint(uint: &BigUint) -> u64 {
    if uint.is_zero() {
        return 1;
    }
    let mut digits = (uint.bits() as f64 / LOG2_10) as u64;
    // guess number of digits based on number of bits in UInt
    let mut num = ten_to_the(digits).to_biguint().expect("Ten to power is negative");
    while *uint >= num {
        num *= 10u8;
        digits += 1;
    }
    digits
}


/// Internal function used for rounding
///
/// returns 1 if most significant digit is >= 5, otherwise 0
///
/// This is used after dividing a number by a power of ten and
/// rounding the last digit.
///
#[inline(always)]
fn get_rounding_term(num: &BigInt) -> u8 {
    if num.is_zero() {
        return 0;
    }

    let digits = (num.bits() as f64 / LOG2_10) as u64;
    let mut n = ten_to_the(digits);

    // loop-method
    loop {
        if *num < n {
            return 1;
        }
        n *= 5;
        if *num < n {
            return 0;
        }
        n *= 2;
    }

    // string-method
    // let s = format!("{}", num);
    // let high_digit = u8::from_str(&s[0..1]).unwrap();
    // if high_digit < 5 { 0 } else { 1 }
}

/// A big decimal type.
///
#[derive(Clone, Eq)]
pub struct BigDecimal {
    int_val: BigInt,
    // A positive scale means a negative power of 10
    scale: i64,
}

#[cfg(not(feature = "std"))]
// f64::exp2 is only available in std, we have to use an external crate like libm
fn exp2(x: f64) -> f64 {
    libm::exp2(x)
}

#[cfg(feature = "std")]
fn exp2(x: f64) -> f64 {
    x.exp2()
}

impl BigDecimal {
    /// Creates and initializes a `BigDecimal`.
    ///
    #[inline]
    pub fn new(digits: BigInt, scale: i64) -> BigDecimal {
        BigDecimal {
            int_val: digits,
            scale: scale,
        }
    }

    /// Make a BigDecimalRef of this value
    pub fn to_ref<'a>(&'a self) -> BigDecimalRef<'a> {
        // search for "From<&'a BigDecimal> for BigDecimalRef<'a>"
        self.into()
    }

    /// Creates and initializes a `BigDecimal`.
    ///
    /// Decodes using `str::from_utf8` and forwards to `BigDecimal::from_str_radix`.
    /// Only base-10 is supported.
    ///
    /// # Examples
    ///
    /// ```
    /// use bigdecimal::{BigDecimal, Zero};
    ///
    /// assert_eq!(BigDecimal::parse_bytes(b"0", 10).unwrap(), BigDecimal::zero());
    /// assert_eq!(BigDecimal::parse_bytes(b"13", 10).unwrap(), BigDecimal::from(13));
    /// ```
    #[inline]
    pub fn parse_bytes(buf: &[u8], radix: u32) -> Option<BigDecimal> {
        stdlib::str::from_utf8(buf)
                    .ok()
                    .and_then(|s| BigDecimal::from_str_radix(s, radix).ok())
    }

    /// Return a new BigDecimal object equivalent to self, with internal
    /// scaling set to the number specified.
    /// If the new_scale is lower than the current value (indicating a larger
    /// power of 10), digits will be dropped (as precision is lower)
    ///
    #[inline]
    pub fn with_scale(&self, new_scale: i64) -> BigDecimal {
        if self.int_val.is_zero() {
            return BigDecimal::new(BigInt::zero(), new_scale);
        }

        match new_scale.cmp(&self.scale) {
            Ordering::Greater => {
                let scale_diff = new_scale - self.scale;
                let int_val = &self.int_val * ten_to_the(scale_diff as u64);
                BigDecimal::new(int_val, new_scale)
            }
            Ordering::Less => {
                let scale_diff = self.scale - new_scale;
                let int_val = &self.int_val / ten_to_the(scale_diff as u64);
                BigDecimal::new(int_val, new_scale)
            }
            Ordering::Equal => self.clone(),
        }
    }

    /// Return a new BigDecimal after shortening the digits and rounding
    ///
    /// ```
    /// # use bigdecimal::*;
    ///
    /// let n: BigDecimal = "129.41675".parse().unwrap();
    ///
    /// assert_eq!(n.with_scale_round(2, RoundingMode::Up),  "129.42".parse().unwrap());
    /// assert_eq!(n.with_scale_round(-1, RoundingMode::Down),  "120".parse().unwrap());
    /// assert_eq!(n.with_scale_round(4, RoundingMode::HalfEven),  "129.4168".parse().unwrap());
    /// ```
    pub fn with_scale_round(&self, new_scale: i64, mode: RoundingMode) -> BigDecimal {
        use stdlib::cmp::Ordering::*;

        if self.int_val.is_zero() {
            return BigDecimal::new(BigInt::zero(), new_scale);
        }

        match new_scale.cmp(&self.scale) {
            Ordering::Equal => {
                self.clone()
            }
            Ordering::Greater => {
                // increase number of zeros
                let scale_diff = new_scale - self.scale;
                let int_val = &self.int_val * ten_to_the(scale_diff as u64);
                BigDecimal::new(int_val, new_scale)
            }
            Ordering::Less => {
                let (sign, mut digits) = self.int_val.to_radix_le(10);

                let digit_count = digits.len();
                let int_digit_count = digit_count as i64 - self.scale;
                let rounded_int = match int_digit_count.cmp(&-new_scale) {
                    Equal => {
                        let (&last_digit, remaining) = digits.split_last().unwrap();
                        let trailing_zeros = remaining.iter().all(Zero::is_zero);
                        let rounded_digit = mode.round_pair(sign, (0, last_digit), trailing_zeros);
                        BigInt::new(sign, vec![rounded_digit as u32])
                    }
                    Less => {
                        debug_assert!(!digits.iter().all(Zero::is_zero));
                        let rounded_digit = mode.round_pair(sign, (0, 0), false);
                        BigInt::new(sign, vec![rounded_digit as u32])
                    }
                    Greater => {
                        // location of new rounding point
                        let scale_diff = (self.scale - new_scale) as usize;

                        let low_digit = digits[scale_diff - 1];
                        let high_digit = digits[scale_diff];
                        let trailing_zeros = digits[0..scale_diff-1].iter().all(Zero::is_zero);
                        let rounded_digit = mode.round_pair(sign, (high_digit, low_digit), trailing_zeros);

                        debug_assert!(rounded_digit <= 10);

                        if rounded_digit < 10 {
                            digits[scale_diff] = rounded_digit;
                        } else {
                            digits[scale_diff] = 0;
                            let mut i = scale_diff + 1;
                            loop {
                                if i == digit_count {
                                    digits.push(1);
                                    break;
                                }

                                if digits[i] < 9 {
                                    digits[i] += 1;
                                    break;
                                }

                                digits[i] = 0;
                                i += 1;
                            }
                        }

                        BigInt::from_radix_le(sign, &digits[scale_diff..], 10).unwrap()
                    }
                };

                BigDecimal::new(rounded_int, new_scale)
            }
        }
    }

    /// Return a new BigDecimal object with same value and given scale,
    /// padding with zeros or truncating digits as needed
    ///
    /// Useful for aligning decimals before adding/subtracting.
    ///
    fn take_and_scale(mut self, new_scale: i64) -> BigDecimal {
        if self.int_val.is_zero() {
            return BigDecimal::new(BigInt::zero(), new_scale);
        }

        match new_scale.cmp(&self.scale) {
            Ordering::Greater => {
                self.int_val *= ten_to_the((new_scale - self.scale) as u64);
                BigDecimal::new(self.int_val, new_scale)
            }
            Ordering::Less => {
                self.int_val /= ten_to_the((self.scale - new_scale) as u64);
                BigDecimal::new(self.int_val, new_scale)
            }
            Ordering::Equal => self,
        }
    }

    /// Return a new BigDecimal object with precision set to new value
    ///
    /// ```
    /// # use bigdecimal::*;
    ///
    /// let n: BigDecimal = "129.41675".parse().unwrap();
    ///
    /// assert_eq!(n.with_prec(2),  "130".parse().unwrap());
    ///
    /// let n_p12 = n.with_prec(12);
    /// let (i, scale) = n_p12.as_bigint_and_exponent();
    /// assert_eq!(n_p12, "129.416750000".parse().unwrap());
    /// assert_eq!(i, 129416750000_u64.into());
    /// assert_eq!(scale, 9);
    /// ```
    pub fn with_prec(&self, prec: u64) -> BigDecimal {
        let digits = self.digits();

        match digits.cmp(&prec) {
            Ordering::Greater => {
                let diff = digits - prec;
                let p = ten_to_the(diff);
                let (mut q, r) = self.int_val.div_rem(&p);

                // check for "leading zero" in remainder term; otherwise round
                if p < 10 * &r {
                    q += get_rounding_term(&r);
                }

                BigDecimal {
                    int_val: q,
                    scale: self.scale - diff as i64,
                }
            }
            Ordering::Less => {
                let diff = prec - digits;
                BigDecimal {
                    int_val: &self.int_val * ten_to_the(diff),
                    scale: self.scale + diff as i64,
                }
            }
            Ordering::Equal => self.clone(),
        }
    }

    /// Return this BigDecimal with the given precision, rounding if needed
    #[cfg(rustc_1_46)]  // Option::zip
    pub fn with_precision_round(&self, prec: stdlib::num::NonZeroU64, round: RoundingMode) -> BigDecimal {
        let digit_count = self.digits();
        let new_prec = prec.get().to_i64();
        let new_scale = new_prec
                        .zip(digit_count.to_i64())
                        .and_then(|(new_prec, old_prec)| new_prec.checked_sub(old_prec))
                        .and_then(|prec_diff| self.scale.checked_add(prec_diff))
                        .expect("precision overflow");

        self.with_scale_round(new_scale, round)
    }

    #[cfg(not(rustc_1_46))]
    pub fn with_precision_round(&self, prec: stdlib::num::NonZeroU64, round: RoundingMode) -> BigDecimal {
        let new_scale = self.digits().to_i64().and_then(
                            |old_prec| {
                                prec.get().to_i64().and_then(
                                    |new_prec| { new_prec.checked_sub(old_prec) })})
                            .and_then(|prec_diff| self.scale.checked_add(prec_diff))
                            .expect("precision overflow");

        self.with_scale_round(new_scale, round)
    }

    /// Return the sign of the `BigDecimal` as `num::bigint::Sign`.
    ///
    /// ```
    /// # use bigdecimal::{BigDecimal, num_bigint::Sign};
    ///
    /// fn sign_of(src: &str) -> Sign {
    ///    let n: BigDecimal = src.parse().unwrap();
    ///    n.sign()
    /// }
    ///
    /// assert_eq!(sign_of("-1"), Sign::Minus);
    /// assert_eq!(sign_of("0"),  Sign::NoSign);
    /// assert_eq!(sign_of("1"),  Sign::Plus);
    /// ```
    #[inline]
    pub fn sign(&self) -> num_bigint::Sign {
        self.int_val.sign()
    }

    /// Return the internal big integer value and an exponent. Note that a positive
    /// exponent indicates a negative power of 10.
    ///
    /// # Examples
    ///
    /// ```
    /// use bigdecimal::{BigDecimal, num_bigint::BigInt};
    ///
    /// let n: BigDecimal = "1.23456".parse().unwrap();
    /// let expected = ("123456".parse::<BigInt>().unwrap(), 5);
    /// assert_eq!(n.as_bigint_and_exponent(), expected);
    /// ```
    #[inline]
    pub fn as_bigint_and_exponent(&self) -> (BigInt, i64) {
        (self.int_val.clone(), self.scale)
    }

    /// Convert into the internal big integer value and an exponent. Note that a positive
    /// exponent indicates a negative power of 10.
    ///
    /// # Examples
    ///
    /// ```
    /// use bigdecimal::{BigDecimal, num_bigint::BigInt};
    ///
    /// let n: BigDecimal = "1.23456".parse().unwrap();
    /// let expected = ("123456".parse::<num_bigint::BigInt>().unwrap(), 5);
    /// assert_eq!(n.into_bigint_and_exponent(), expected);
    /// ```
    #[inline]
    pub fn into_bigint_and_exponent(self) -> (BigInt, i64) {
        (self.int_val, self.scale)
    }

    /// Number of digits in the non-scaled integer representation
    ///
    #[inline]
    pub fn digits(&self) -> u64 {
        count_decimal_digits(&self.int_val)
    }

    /// Compute the absolute value of number
    ///
    /// ```
    /// # use bigdecimal::BigDecimal;
    /// let n: BigDecimal = "123.45".parse().unwrap();
    /// assert_eq!(n.abs(), "123.45".parse().unwrap());
    ///
    /// let n: BigDecimal = "-123.45".parse().unwrap();
    /// assert_eq!(n.abs(), "123.45".parse().unwrap());
    /// ```
    #[inline]
    pub fn abs(&self) -> BigDecimal {
        BigDecimal {
            int_val: self.int_val.abs(),
            scale: self.scale,
        }
    }

    /// Multiply decimal by 2 (efficiently)
    ///
    /// ```
    /// # use bigdecimal::BigDecimal;
    /// let n: BigDecimal = "123.45".parse().unwrap();
    /// assert_eq!(n.double(), "246.90".parse().unwrap());
    /// ```
    pub fn double(&self) -> BigDecimal {
        if self.is_zero() {
            self.clone()
        } else {
            BigDecimal {
                int_val: self.int_val.clone() * 2,
                scale: self.scale,
            }
        }
    }

    /// Divide decimal by 2 (efficiently)
    ///
    /// *Note*: If the last digit in the decimal is odd, the precision
    ///         will increase by 1
    ///
    /// ```
    /// # use bigdecimal::BigDecimal;
    /// let n: BigDecimal = "123.45".parse().unwrap();
    /// assert_eq!(n.half(), "61.725".parse().unwrap());
    /// ```
    #[inline]
    pub fn half(&self) -> BigDecimal {
        if self.is_zero() {
            self.clone()
        } else if self.int_val.is_even() {
            BigDecimal {
                int_val: self.int_val.clone().div(2u8),
                scale: self.scale,
            }
        } else {
            BigDecimal {
                int_val: self.int_val.clone().mul(5u8),
                scale: self.scale + 1,
            }
        }
    }

    /// Square a decimal: *x²*
    ///
    /// No rounding or truncating of digits; this is the full result
    /// of the squaring operation.
    ///
    /// *Note*: doubles the scale of bigdecimal, which might lead to
    ///         accidental exponential-complexity if used in a loop.
    ///
    /// ```
    /// # use bigdecimal::BigDecimal;
    /// let n: BigDecimal = "1.1156024145937225657484".parse().unwrap();
    /// assert_eq!(n.square(), "1.24456874744734405154288399835406316085210256".parse().unwrap());
    ///
    /// let n: BigDecimal = "-9.238597585E+84".parse().unwrap();
    /// assert_eq!(n.square(), "8.5351685337567832225E+169".parse().unwrap());
    /// ```
    pub fn square(&self) -> BigDecimal {
        if self.is_zero() || self.is_one() {
            self.clone()
        } else {
            BigDecimal {
                int_val: self.int_val.clone() * &self.int_val,
                scale: self.scale * 2,
            }
        }
    }

    /// Cube a decimal: *x³*
    ///
    /// No rounding or truncating of digits; this is the full result
    /// of the cubing operation.
    ///
    /// *Note*: triples the scale of bigdecimal, which might lead to
    ///         accidental exponential-complexity if used in a loop.
    ///
    /// ```
    /// # use bigdecimal::BigDecimal;
    /// let n: BigDecimal = "1.1156024145937225657484".parse().unwrap();
    /// assert_eq!(n.cube(), "1.388443899780141911774491376394890472130000455312878627147979955904".parse().unwrap());
    ///
    /// let n: BigDecimal = "-9.238597585E+84".parse().unwrap();
    /// assert_eq!(n.cube(), "-7.88529874035334084567570176625E+254".parse().unwrap());
    /// ```
    pub fn cube(&self) -> BigDecimal {
        if self.is_zero() || self.is_one() {
            self.clone()
        } else {
            BigDecimal {
                int_val: self.int_val.clone() * &self.int_val * &self.int_val,
                scale: self.scale * 3,
            }
        }
    }

    /// Take the square root of the number
    ///
    /// Uses default-precision, set from build time environment variable
    //// `RUST_BIGDECIMAL_DEFAULT_PRECISION` (defaults to 100)
    ///
    /// If the value is < 0, None is returned
    ///
    /// ```
    /// # use bigdecimal::BigDecimal;
    /// let n: BigDecimal = "1.1156024145937225657484".parse().unwrap();
    /// assert_eq!(n.sqrt().unwrap(), "1.056220817156016181190291268045893004363809142172289919023269377496528394924695970851558013658193913".parse().unwrap());
    ///
    /// let n: BigDecimal = "-9.238597585E+84".parse().unwrap();
    /// assert_eq!(n.sqrt(), None);
    /// ```
    #[inline]
    pub fn sqrt(&self) -> Option<BigDecimal> {
        if self.is_zero() || self.is_one() {
            return Some(self.clone());
        }
        if self.is_negative() {
            return None;
        }

        // make guess
        let guess = {
            let magic_guess_scale = 1.1951678538495576_f64;
            let initial_guess = (self.int_val.bits() as f64 - self.scale as f64 * LOG2_10) / 2.0;
            let res = magic_guess_scale * exp2(initial_guess);

            if res.is_normal() {
                BigDecimal::try_from(res).unwrap()
            } else {
                // can't guess with float - just guess magnitude
                let scale = (self.int_val.bits() as f64 / -LOG2_10 + self.scale as f64).round() as i64;
                BigDecimal::new(BigInt::from(1), scale / 2)
            }
        };

        // // wikipedia example - use for testing the algorithm
        // if self == &BigDecimal::from_str("125348").unwrap() {
        //     running_result = BigDecimal::from(600)
        // }

        // TODO: Use context variable to set precision
        let max_precision = DEFAULT_PRECISION;

        let next_iteration = move |r: BigDecimal| {
            // division needs to be precise to (at least) one extra digit
            let tmp = impl_division(
                self.int_val.clone(),
                &r.int_val,
                self.scale - r.scale,
                max_precision + 1,
            );

            // half will increase precision on each iteration
            (tmp + r).half()
        };

        // calculate first iteration
        let mut running_result = next_iteration(guess);

        let mut prev_result = BigDecimal::one();
        let mut result = BigDecimal::zero();

        // TODO: Prove that we don't need to arbitrarily limit iterations
        // and that convergence can be calculated
        while prev_result != result {
            // store current result to test for convergence
            prev_result = result;

            // calculate next iteration
            running_result = next_iteration(running_result);

            // 'result' has clipped precision, 'running_result' has full precision
            result = if running_result.digits() > max_precision {
                running_result.with_prec(max_precision)
            } else {
                running_result.clone()
            };
        }

        return Some(result);
    }

    /// Take the cube root of the number
    ///
    #[inline]
    pub fn cbrt(&self) -> BigDecimal {
        if self.is_zero() || self.is_one() {
            return self.clone();
        }
        if self.is_negative() {
            return -self.abs().cbrt();
        }

        // make guess
        let guess = {
            let magic_guess_scale = 1.124960491619939_f64;
            let initial_guess = (self.int_val.bits() as f64 - self.scale as f64 * LOG2_10) / 3.0;
            let res = magic_guess_scale * exp2(initial_guess);

            if res.is_normal() {
                BigDecimal::try_from(res).unwrap()
            } else {
                // can't guess with float - just guess magnitude
                let scale = (self.int_val.bits() as f64 / LOG2_10 - self.scale as f64).round() as i64;
                BigDecimal::new(BigInt::from(1), -scale / 3)
            }
        };

        // TODO: Use context variable to set precision
        let max_precision = DEFAULT_PRECISION;

        let three = BigDecimal::from(3);

        let next_iteration = move |r: BigDecimal| {
            let sqrd = r.square();
            let tmp = impl_division(
                self.int_val.clone(),
                &sqrd.int_val,
                self.scale - sqrd.scale,
                max_precision + 1,
            );
            let tmp = tmp + r.double();
            impl_division(tmp.int_val, &three.int_val, tmp.scale - three.scale, max_precision + 1)
        };

        // result initial
        let mut running_result = next_iteration(guess);

        let mut prev_result = BigDecimal::one();
        let mut result = BigDecimal::zero();

        // TODO: Prove that we don't need to arbitrarily limit iterations
        // and that convergence can be calculated
        while prev_result != result {
            // store current result to test for convergence
            prev_result = result;

            running_result = next_iteration(running_result);

            // result has clipped precision, running_result has full precision
            result = if running_result.digits() > max_precision {
                running_result.with_prec(max_precision)
            } else {
                running_result.clone()
            };
        }

        return result;
    }

    /// Compute the reciprical of the number: x<sup>-1</sup>
    #[inline]
    pub fn inverse(&self) -> BigDecimal {
        if self.is_zero() || self.is_one() {
            return self.clone();
        }
        if self.is_negative() {
            return self.abs().inverse().neg();
        }
        let guess = {
            let bits = self.int_val.bits() as f64;
            let scale = self.scale as f64;

            let magic_factor = 0.721507597259061_f64;
            let initial_guess = scale * LOG2_10 - bits;
            let res = magic_factor * exp2(initial_guess);

            if res.is_normal() {
                BigDecimal::try_from(res).unwrap()
            } else {
                // can't guess with float - just guess magnitude
                let scale = (bits / LOG2_10 + scale).round() as i64;
                BigDecimal::new(BigInt::from(1), -scale)
            }
        };

        let max_precision = DEFAULT_PRECISION;
        let next_iteration = move |r: BigDecimal| {
            let two = BigDecimal::from(2);
            let tmp = two - self * &r;

            r * tmp
        };

        // calculate first iteration
        let mut running_result = next_iteration(guess);

        let mut prev_result = BigDecimal::one();
        let mut result = BigDecimal::zero();

        // TODO: Prove that we don't need to arbitrarily limit iterations
        // and that convergence can be calculated
        while prev_result != result {
            // store current result to test for convergence
            prev_result = result;

            // calculate next iteration
            running_result = next_iteration(running_result).with_prec(max_precision);

            // 'result' has clipped precision, 'running_result' has full precision
            result = if running_result.digits() > max_precision {
                running_result.with_prec(max_precision)
            } else {
                running_result.clone()
            };
        }

        return result;
    }

    /// Return number rounded to round_digits precision after the decimal point
    pub fn round(&self, round_digits: i64) -> BigDecimal {
        // we have fewer digits than we need, no rounding
        if round_digits >= self.scale {
            return self.with_scale(round_digits);
        }

        let (sign, double_digits) = self.int_val.to_radix_le(100);

        let last_is_double_digit = *double_digits.last().unwrap() >= 10;
        let digit_count = (double_digits.len() - 1) * 2 + 1 + last_is_double_digit as usize;

        // relevant digit positions: each "pos" is position of 10^{pos}
        let least_significant_pos = -self.scale;
        let most_sig_digit_pos = digit_count as i64 + least_significant_pos - 1;
        let rounding_pos = -round_digits;

        // digits are too small, round to zero
        if rounding_pos > most_sig_digit_pos + 1 {
            return BigDecimal::zero();
        }

        // highest digit is next to rounding point
        if rounding_pos == most_sig_digit_pos + 1 {
            let (&last_double_digit, remaining) = double_digits.split_last().unwrap();

            let mut trailing_zeros = remaining.iter().all(|&d| d == 0);

            let last_digit = if last_is_double_digit {
                let (high, low) = num_integer::div_rem(last_double_digit, 10);
                trailing_zeros &= low == 0;
                high
            } else {
                last_double_digit
            };

            if last_digit > 5 || (last_digit == 5 && !trailing_zeros) {
                return BigDecimal::new(BigInt::one(), round_digits);
            }

            return BigDecimal::zero();
        }

        let double_digits_to_remove = self.scale - round_digits;
        debug_assert!(double_digits_to_remove > 0);

        let (rounding_idx, rounding_offset) = num_integer::div_rem(double_digits_to_remove as usize, 2);
        debug_assert!(rounding_idx <= double_digits.len());

        let (low_digits, high_digits) = double_digits.as_slice().split_at(rounding_idx);
        debug_assert!(high_digits.len() > 0);

        let mut unrounded_uint = num_bigint::BigUint::from_radix_le(high_digits, 100).unwrap();

        let rounded_uint;
        if rounding_offset == 0 {
            let high_digit = high_digits[0] % 10;
            let (&top, rest) = low_digits.split_last().unwrap_or((&0u8, &[]));
            let (low_digit, lower_digit) = num_integer::div_rem(top, 10);
            let trailing_zeros = lower_digit == 0 && rest.iter().all(|&d| d == 0);

            let rounding = if low_digit < 5 {
                0
            } else if low_digit > 5 || !trailing_zeros {
                1
            } else {
                high_digit % 2
            };

            rounded_uint = unrounded_uint + rounding;
        } else {
            let (high_digit, low_digit) = num_integer::div_rem(high_digits[0], 10);

            let trailing_zeros = low_digits.iter().all(|&d| d == 0);

            let rounding = if low_digit < 5 {
                0
            } else if low_digit > 5 || !trailing_zeros {
                1
            } else {
                high_digit % 2
            };

            // shift unrounded_uint down,
            unrounded_uint /= num_bigint::BigUint::from_u8(10).unwrap();
            rounded_uint = unrounded_uint + rounding;
        }

        let rounded_int = num_bigint::BigInt::from_biguint(sign,  rounded_uint);
        BigDecimal::new(rounded_int, round_digits)
    }

    /// Return true if this number has zero fractional part (is equal
    /// to an integer)
    ///
    #[inline]
    pub fn is_integer(&self) -> bool {
        if self.scale <= 0 {
            true
        } else {
            (self.int_val.clone() % ten_to_the(self.scale as u64)).is_zero()
        }
    }

    /// Evaluate the natural-exponential function e<sup>x</sup>
    ///
    #[inline]
    pub fn exp(&self) -> BigDecimal {
        if self.is_zero() {
            return BigDecimal::one();
        }

        let target_precision = DEFAULT_PRECISION;

        let precision = self.digits();

        let mut term = self.clone();
        let mut result = self.clone() + BigDecimal::one();
        let mut prev_result = result.clone();
        let mut factorial = BigInt::one();

        for n in 2.. {
            term *= self;
            factorial *= n;
            // ∑ term=x^n/n!
            result += impl_division(term.int_val.clone(), &factorial, term.scale, 117 + precision);

            let trimmed_result = result.with_prec(target_precision + 5);
            if prev_result == trimmed_result {
                return trimmed_result.with_prec(target_precision);
            }
            prev_result = trimmed_result;
        }
        unreachable!("Loop did not converge")
    }

    #[must_use]
    pub fn normalized(&self) -> BigDecimal {
        if self == &BigDecimal::zero() {
            return BigDecimal::zero();
        }
        let (sign, mut digits) = self.int_val.to_radix_be(10);
        let trailing_count = digits.iter().rev().take_while(|i| **i == 0).count();
        let trunc_to = digits.len() - trailing_count;
        digits.truncate(trunc_to);
        let int_val = BigInt::from_radix_be(sign, &digits, 10).unwrap();
        let scale = self.scale - trailing_count as i64;
        BigDecimal::new(int_val, scale)
    }
}

#[derive(Debug, PartialEq)]
pub enum ParseBigDecimalError {
    ParseDecimal(ParseFloatError),
    ParseInt(ParseIntError),
    ParseBigInt(ParseBigIntError),
    Empty,
    Other(String),
}

impl fmt::Display for ParseBigDecimalError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use ParseBigDecimalError::*;

        match *self {
            ParseDecimal(ref e) => e.fmt(f),
            ParseInt(ref e) => e.fmt(f),
            ParseBigInt(ref e) => e.fmt(f),
            Empty => "Failed to parse empty string".fmt(f),
            Other(ref reason) => reason[..].fmt(f),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseBigDecimalError {
    fn description(&self) -> &str {
        "failed to parse bigint/biguint"
    }
}

impl From<ParseFloatError> for ParseBigDecimalError {
    fn from(err: ParseFloatError) -> ParseBigDecimalError {
        ParseBigDecimalError::ParseDecimal(err)
    }
}

impl From<ParseIntError> for ParseBigDecimalError {
    fn from(err: ParseIntError) -> ParseBigDecimalError {
        ParseBigDecimalError::ParseInt(err)
    }
}

impl From<ParseBigIntError> for ParseBigDecimalError {
    fn from(err: ParseBigIntError) -> ParseBigDecimalError {
        ParseBigDecimalError::ParseBigInt(err)
    }
}

impl FromStr for BigDecimal {
    type Err = ParseBigDecimalError;

    #[inline]
    fn from_str(s: &str) -> Result<BigDecimal, ParseBigDecimalError> {
        BigDecimal::from_str_radix(s, 10)
    }
}

#[allow(deprecated)] // trim_right_match -> trim_end_match
impl Hash for BigDecimal {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut dec_str = self.int_val.to_str_radix(10);
        let scale = self.scale;
        let zero = self.int_val.is_zero();
        if scale > 0 && !zero {
            let mut cnt = 0;
            dec_str = dec_str
                .trim_right_matches(|x| {
                    cnt += 1;
                    x == '0' && cnt <= scale
                })
                .to_string();
        } else if scale < 0 && !zero {
            dec_str.push_str(&"0".repeat(self.scale.abs() as usize));
        }
        dec_str.hash(state);
    }
}

impl PartialOrd for BigDecimal {
    #[inline]
    fn partial_cmp(&self, other: &BigDecimal) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BigDecimal {
    /// Complete ordering implementation for BigDecimal
    ///
    /// # Example
    ///
    /// ```
    /// use std::str::FromStr;
    ///
    /// let a = bigdecimal::BigDecimal::from_str("-1").unwrap();
    /// let b = bigdecimal::BigDecimal::from_str("1").unwrap();
    /// assert!(a < b);
    /// assert!(b > a);
    /// let c = bigdecimal::BigDecimal::from_str("1").unwrap();
    /// assert!(b >= c);
    /// assert!(c >= b);
    /// let d = bigdecimal::BigDecimal::from_str("10.0").unwrap();
    /// assert!(d > c);
    /// let e = bigdecimal::BigDecimal::from_str(".5").unwrap();
    /// assert!(e < c);
    /// ```
    #[inline]
    fn cmp(&self, other: &BigDecimal) -> Ordering {
        let scmp = self.sign().cmp(&other.sign());
        if scmp != Ordering::Equal {
            return scmp;
        }

        match self.sign() {
            Sign::NoSign => Ordering::Equal,
            _ => {
                let tmp = self - other;
                match tmp.sign() {
                    Sign::Plus => Ordering::Greater,
                    Sign::Minus => Ordering::Less,
                    Sign::NoSign => Ordering::Equal,
                }
            }
        }
    }
}


impl Default for BigDecimal {
    #[inline]
    fn default() -> BigDecimal {
        Zero::zero()
    }
}

impl Zero for BigDecimal {
    #[inline]
    fn zero() -> BigDecimal {
        BigDecimal::new(BigInt::zero(), 0)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.int_val.is_zero()
    }
}

impl One for BigDecimal {
    #[inline]
    fn one() -> BigDecimal {
        BigDecimal::new(BigInt::one(), 0)
    }
}




fn impl_division(mut num: BigInt, den: &BigInt, mut scale: i64, max_precision: u64) -> BigDecimal {
    // quick zero check
    if num.is_zero() {
        return BigDecimal::new(num, 0);
    }

    match (num.is_negative(), den.is_negative()) {
        (true, true) => return impl_division(num.neg(), &den.neg(), scale, max_precision),
        (true, false) => return -impl_division(num.neg(), den, scale, max_precision),
        (false, true) => return -impl_division(num, &den.neg(), scale, max_precision),
        (false, false) => (),
    }

    // shift digits until numerator is larger than denominator (set scale appropriately)
    while num < *den {
        scale += 1;
        num *= 10;
    }

    // first division
    let (mut quotient, mut remainder) = num.div_rem(den);

    // division complete
    if remainder.is_zero() {
        return BigDecimal {
            int_val: quotient,
            scale: scale,
        };
    }

    let mut precision = count_decimal_digits(&quotient);

    // shift remainder by 1 decimal;
    // quotient will be 1 digit upon next division
    remainder *= 10;

    while !remainder.is_zero() && precision < max_precision {
        let (q, r) = remainder.div_rem(den);
        quotient = quotient * 10 + q;
        remainder = r * 10;

        precision += 1;
        scale += 1;
    }

    if !remainder.is_zero() {
        // round final number with remainder
        quotient += get_rounding_term(&remainder.div(den));
    }

    let result = BigDecimal::new(quotient, scale);
    // println!(" {} / {}\n = {}\n", self, other, result);
    return result;
}



impl Signed for BigDecimal {
    #[inline]
    fn abs(&self) -> BigDecimal {
        match self.sign() {
            Sign::Plus | Sign::NoSign => self.clone(),
            Sign::Minus => -self,
        }
    }

    #[inline]
    fn abs_sub(&self, other: &BigDecimal) -> BigDecimal {
        if *self <= *other {
            Zero::zero()
        } else {
            self - other
        }
    }

    #[inline]
    fn signum(&self) -> BigDecimal {
        match self.sign() {
            Sign::Plus => One::one(),
            Sign::NoSign => Zero::zero(),
            Sign::Minus => -Self::one(),
        }
    }

    #[inline]
    fn is_positive(&self) -> bool {
        self.sign() == Sign::Plus
    }

    #[inline]
    fn is_negative(&self) -> bool {
        self.sign() == Sign::Minus
    }
}

impl Sum for BigDecimal {
    #[inline]
    fn sum<I: Iterator<Item = BigDecimal>>(iter: I) -> BigDecimal {
        iter.fold(Zero::zero(), |a, b| a + b)
    }
}

impl<'a> Sum<&'a BigDecimal> for BigDecimal {
    #[inline]
    fn sum<I: Iterator<Item = &'a BigDecimal>>(iter: I) -> BigDecimal {
        iter.fold(Zero::zero(), |a, b| a + b)
    }
}

impl fmt::Display for BigDecimal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Acquire the absolute integer as a decimal string
        let mut abs_int = self.int_val.abs().to_str_radix(10);

        // Split the representation at the decimal point
        let (before, after) = if self.scale >= abs_int.len() as i64 {
            // First case: the integer representation falls
            // completely behind the decimal point
            let scale = self.scale as usize;
            let after = "0".repeat(scale - abs_int.len()) + abs_int.as_str();
            ("0".to_string(), after)
        } else {
            // Second case: the integer representation falls
            // around, or before the decimal point
            let location = abs_int.len() as i64 - self.scale;
            if location > abs_int.len() as i64 {
                // Case 2.1, entirely before the decimal point
                // We should prepend zeros
                let zeros = location as usize - abs_int.len();
                let abs_int = abs_int + "0".repeat(zeros).as_str();
                (abs_int, "".to_string())
            } else {
                // Case 2.2, somewhere around the decimal point
                // Just split it in two
                let after = abs_int.split_off(location as usize);
                (abs_int, after)
            }
        };

        // Alter precision after the decimal point
        let after = if let Some(precision) = f.precision() {
            let len = after.len();
            if len < precision {
                after + "0".repeat(precision - len).as_str()
            } else {
                // TODO: Should we round?
                after[0..precision].to_string()
            }
        } else {
            after
        };

        // Concatenate everything
        let complete_without_sign = if !after.is_empty() {
            before + "." + after.as_str()
        } else {
            before
        };

        let non_negative = matches!(self.int_val.sign(), Sign::Plus | Sign::NoSign);
        //pad_integral does the right thing although we have a decimal
        f.pad_integral(non_negative, "", &complete_without_sign)
    }
}

impl fmt::Debug for BigDecimal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "BigDecimal(\"{}\")", self)
    }
}


/// A big-decimal wrapping a borrowed (immutable) buffer of digits
///
/// The non-digit information like `scale` and `sign` may be changed
/// on these objects, which otherwise would require cloning the full
/// digit buffer in the BigDecimal.
///
/// May be transformed into full BigDecimal object using the to_owned()
/// method.
///
/// BigDecimalRefs should be preferred over using &BigDecimal for most
/// functions that need an immutable reference to a bigdecimal.
///
#[derive(Clone, Copy, Debug)]
pub struct BigDecimalRef<'a> {
    sign: Sign,
    digits: &'a BigUint,
    scale: i64,
}

impl BigDecimalRef<'_> {
    /// Clone digits to make this reference a full BigDecimal object
    pub fn to_owned(&self) -> BigDecimal {
        BigDecimal {
            scale: self.scale,
            int_val: BigInt::from_biguint(self.sign, self.digits.clone()),
        }
    }

    /// Sign of decimal
    pub fn sign(&self) -> Sign {
        self.sign
    }

    /// Count number of decimal digits
    pub fn count_digits(&self) -> u64 {
        count_decimal_digits_uint(self.digits)
    }

    /// Split into components
    #[allow(dead_code)]
    pub(crate) fn as_parts(&self) -> (Sign, i64, &BigUint) {
        (self.sign, self.scale, self.digits)
    }

    /// Take absolute value of the decimal (non-negative sign)
    pub fn abs(&self) -> Self {
        Self {
            sign: self.sign * self.sign,
            digits: self.digits,
            scale: self.scale,
        }
    }
}

impl<'a> From<&'a BigDecimal> for BigDecimalRef<'a> {
    fn from(n: &'a BigDecimal) -> Self {
        let sign = n.int_val.sign();
        let mag = n.int_val.magnitude();
        Self {
            sign: sign,
            digits: mag,
            scale: n.scale,
        }
    }
}

impl<'a> From<BigDecimalRef<'a>> for BigDecimal {
    fn from(n: BigDecimalRef<'a>) -> Self {
        n.to_owned()
    }
}


/// Tools to help serializing/deserializing `BigDecimal`s
#[cfg(feature = "serde")]
mod bigdecimal_serde {
    use super::*;
    use serde::{de, ser};

    #[allow(unused_imports)]
    use num_traits::FromPrimitive;

    impl ser::Serialize for BigDecimal {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: ser::Serializer,
        {
            serializer.collect_str(&self)
        }
    }

    struct BigDecimalVisitor;

    impl<'de> de::Visitor<'de> for BigDecimalVisitor {
        type Value = BigDecimal;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            write!(formatter, "a number or formatted decimal string")
        }

        fn visit_str<E>(self, value: &str) -> Result<BigDecimal, E>
        where
            E: de::Error,
        {
            BigDecimal::from_str(value).map_err(|err| E::custom(format!("{}", err)))
        }

        fn visit_u64<E>(self, value: u64) -> Result<BigDecimal, E>
        where
            E: de::Error,
        {
            Ok(BigDecimal::from(value))
        }

        fn visit_i64<E>(self, value: i64) -> Result<BigDecimal, E>
        where
            E: de::Error,
        {
            Ok(BigDecimal::from(value))
        }

        fn visit_f64<E>(self, value: f64) -> Result<BigDecimal, E>
        where
            E: de::Error,
        {
            BigDecimal::try_from(value).map_err(|err| E::custom(format!("{}", err)))
        }
    }

    #[cfg(not(feature = "string-only"))]
    impl<'de> de::Deserialize<'de> for BigDecimal {
        fn deserialize<D>(d: D) -> Result<Self, D::Error>
        where
            D: de::Deserializer<'de>,
        {
            d.deserialize_any(BigDecimalVisitor)
        }
    }

    #[cfg(feature = "string-only")]
    impl<'de> de::Deserialize<'de> for BigDecimal {
        fn deserialize<D>(d: D) -> Result<Self, D::Error>
        where
            D: de::Deserializer<'de>,
        {
            d.deserialize_str(BigDecimalVisitor)
        }
    }

    #[cfg(test)]
    extern crate serde_json;

    #[test]
    fn test_serde_serialize() {
        let vals = vec![
            ("1.0", "1.0"),
            ("0.5", "0.5"),
            ("50", "50"),
            ("50000", "50000"),
            ("1e-3", "0.001"),
            ("1e12", "1000000000000"),
            ("0.25", "0.25"),
            ("12.34", "12.34"),
            ("0.15625", "0.15625"),
            ("0.3333333333333333", "0.3333333333333333"),
            ("3.141592653589793", "3.141592653589793"),
            ("94247.77960769380", "94247.77960769380"),
            ("10.99", "10.99"),
            ("12.0010", "12.0010"),
        ];
        for (s, v) in vals {
            let expected = format!("\"{}\"", v);
            let value = serde_json::to_string(&BigDecimal::from_str(s).unwrap()).unwrap();
            assert_eq!(expected, value);
        }
    }

    #[test]
    fn test_serde_deserialize_str() {
        let vals = vec![
            ("1.0", "1.0"),
            ("0.5", "0.5"),
            ("50", "50"),
            ("50000", "50000"),
            ("1e-3", "0.001"),
            ("1e12", "1000000000000"),
            ("0.25", "0.25"),
            ("12.34", "12.34"),
            ("0.15625", "0.15625"),
            ("0.3333333333333333", "0.3333333333333333"),
            ("3.141592653589793", "3.141592653589793"),
            ("94247.77960769380", "94247.77960769380"),
            ("10.99", "10.99"),
            ("12.0010", "12.0010"),
        ];
        for (s, v) in vals {
            let expected = BigDecimal::from_str(v).unwrap();
            let value: BigDecimal = serde_json::from_str(&format!("\"{}\"", s)).unwrap();
            assert_eq!(expected, value);
        }
    }

    #[test]
    #[cfg(not(feature = "string-only"))]
    fn test_serde_deserialize_int() {
        let vals = vec![0, 1, 81516161, -370, -8, -99999999999];
        for n in vals {
            let expected = BigDecimal::from_i64(n).unwrap();
            let value: BigDecimal = serde_json::from_str(&serde_json::to_string(&n).unwrap()).unwrap();
            assert_eq!(expected, value);
        }
    }

    #[test]
    #[cfg(not(feature = "string-only"))]
    fn test_serde_deserialize_f64() {
        let vals = vec![
            1.0,
            0.5,
            0.25,
            50.0,
            50000.,
            0.001,
            12.34,
            5.0 * 0.03125,
            stdlib::f64::consts::PI,
            stdlib::f64::consts::PI * 10000.0,
            stdlib::f64::consts::PI * 30000.0,
        ];
        for n in vals {
            let expected = BigDecimal::from_f64(n).unwrap();
            let value: BigDecimal = serde_json::from_str(&serde_json::to_string(&n).unwrap()).unwrap();
            assert_eq!(expected, value);
        }
    }
}

#[rustfmt::skip]
#[cfg(test)]
#[allow(non_snake_case)]
mod bigdecimal_tests {
    use crate::{stdlib, BigDecimal, ToString, FromStr, TryFrom};
    use num_traits::{ToPrimitive, FromPrimitive, Signed, Zero, One};
    use num_bigint;
    use paste::paste;

    #[test]
    fn test_sum() {
        let vals = vec![
            BigDecimal::from_f32(2.5).unwrap(),
            BigDecimal::from_f32(0.3).unwrap(),
            BigDecimal::from_f32(0.001).unwrap(),
        ];

        let expected_sum = BigDecimal::from_str("2.801000011968426406383514404296875").unwrap();
        let sum = vals.iter().sum::<BigDecimal>();

        assert_eq!(expected_sum, sum);
    }

    #[test]
    fn test_sum1() {
        let vals = vec![
            BigDecimal::from_f32(0.1).unwrap(),
            BigDecimal::from_f32(0.2).unwrap(),
        ];

        let expected_sum = BigDecimal::from_str("0.300000004470348358154296875").unwrap();
        let sum = vals.iter().sum::<BigDecimal>();

        assert_eq!(expected_sum, sum);
    }

    #[test]
    fn test_to_i64() {
        let vals = vec![
            ("12.34", 12),
            ("3.14", 3),
            ("50", 50),
            ("50000", 50000),
            ("0.001", 0),
            // TODO: Is the desired behaviour to round?
            //("0.56", 1),
        ];
        for (s, ans) in vals {
            let calculated = BigDecimal::from_str(s).unwrap().to_i64().unwrap();

            assert_eq!(ans, calculated);
        }
    }

    #[test]
    fn test_to_i128() {
        let vals = vec![
            ("170141183460469231731687303715884105727", 170141183460469231731687303715884105727),
            ("-170141183460469231731687303715884105728", -170141183460469231731687303715884105728),
            ("12.34", 12),
            ("3.14", 3),
            ("50", 50),
            ("0.001", 0),
        ];
        for (s, ans) in vals {
            let calculated = BigDecimal::from_str(s).unwrap().to_i128().unwrap();

            assert_eq!(ans, calculated);
        }
    }

    #[test]
    fn test_to_u128() {
        let vals = vec![
            ("340282366920938463463374607431768211455", 340282366920938463463374607431768211455),
            ("12.34", 12),
            ("3.14", 3),
            ("50", 50),
            ("0.001", 0),
        ];
        for (s, ans) in vals {
            let calculated = BigDecimal::from_str(s).unwrap().to_u128().unwrap();

            assert_eq!(ans, calculated);
        }
    }

    #[test]
    fn test_to_f64() {
        let vals = vec![
            ("12.34", 12.34),
            ("3.14", 3.14),
            ("50", 50.),
            ("50000", 50000.),
            ("0.001", 0.001),
        ];
        for (s, ans) in vals {
            let diff = BigDecimal::from_str(s).unwrap().to_f64().unwrap() - ans;
            let diff = diff.abs();

            assert!(diff < 1e-10);
        }
    }

    #[test]
    fn test_from_i8() {
        let vals = vec![
            ("0", 0),
            ("1", 1),
            ("12", 12),
            ("-13", -13),
            ("111", 111),
            ("-128", i8::MIN),
            ("127", i8::MAX),
        ];
        for (s, n) in vals {
            let expected = BigDecimal::from_str(s).unwrap();
            let value = BigDecimal::from_i8(n).unwrap();
            assert_eq!(expected, value);
        }
    }

    #[test]
    fn test_from_f32() {
        let vals = vec![
            ("0.0", 0.0),
            ("1.0", 1.0),
            ("0.5", 0.5),
            ("0.25", 0.25),
            ("50.", 50.0),
            ("50000", 50000.),
            ("0.001000000047497451305389404296875", 0.001),
            ("12.340000152587890625", 12.34),
            ("0.15625", 0.15625),
            ("3.1415927410125732421875", stdlib::f32::consts::PI),
            ("31415.927734375", stdlib::f32::consts::PI * 10000.0),
            ("94247.78125", stdlib::f32::consts::PI * 30000.0),
            ("1048576", 1048576.),
        ];
        for (s, n) in vals {
            let expected = BigDecimal::from_str(s).unwrap();
            let value = BigDecimal::from_f32(n).unwrap();
            assert_eq!(expected, value);
        }
    }

    #[test]
    fn test_from_f64() {
        let vals = vec![
            ("1.0", 1.0f64),
            ("0.5", 0.5),
            ("50", 50.),
            ("50000", 50000.),
            ("0.001000000000000000020816681711721685132943093776702880859375", 0.001),
            ("0.25", 0.25),
            ("12.339999999999999857891452847979962825775146484375", 12.34),
            ("0.15625", 5.0 * 0.03125),
            ("0.333333333333333314829616256247390992939472198486328125", 1.0 / 3.0),
            ("3.141592653589793115997963468544185161590576171875", stdlib::f64::consts::PI),
            ("31415.926535897931898944079875946044921875", stdlib::f64::consts::PI * 10000.0f64),
            ("94247.779607693795696832239627838134765625", stdlib::f64::consts::PI * 30000.0f64),
        ];
        for (s, n) in vals {
            let expected = BigDecimal::from_str(s).unwrap();
            let value = BigDecimal::from_f64(n).unwrap();
            assert_eq!(expected, value);
            // assert_eq!(expected, n);
        }
    }

    #[test]
    fn test_nan_float() {
        assert!(BigDecimal::try_from(f32::NAN).is_err());
        assert!(BigDecimal::try_from(f64::NAN).is_err());
    }

    #[test]
    fn test_rem() {
        let vals = vec![
            ("100", "5", "0"),
            ("2e1", "1", "0"),
            ("2", "1", "0"),
            ("1", "3", "1"),
            ("1", "0.5", "0"),
            ("1.5", "1", "0.5"),
            ("1", "3e-2", "1e-2"),
            ("10", "0.003", "0.001"),
            ("3", "2", "1"),
            ("-3", "2", "-1"),
            ("3", "-2", "1"),
            ("-3", "-2", "-1"),
            ("12.34", "1.233", "0.01"),
        ];
        for &(x, y, z) in vals.iter() {
            let a = BigDecimal::from_str(x).unwrap();
            let b = BigDecimal::from_str(y).unwrap();
            let c = BigDecimal::from_str(z).unwrap();

            let rem = &a % &b;
            assert_eq!(rem, c, "{} [&{} % &{}] == {}", rem, a, b, c);

            let rem = a.clone() % &b;
            assert_eq!(rem, c, "{} [{} % &{}] == {}", rem, a, b, c);

            let rem = &a % b.clone();
            assert_eq!(rem, c, "{} [&{} % {}] == {}", rem, a, b, c);

            let rem = a.clone() % b.clone();
            assert_eq!(rem, c, "{} [{} % {}] == {}", rem, a, b, c);
        }
        let vals = vec![
            (("100", -2), ("50", -1), "0"),
            (("100", 0), ("50", -1), "0"),
            (("100", -2), ("30", 0), "10"),
            (("100", 0), ("30", -1), "10"),
        ];
        for &((x, xs), (y, ys), z) in vals.iter() {
            let a = BigDecimal::from_str(x).unwrap().with_scale(xs);
            let b = BigDecimal::from_str(y).unwrap().with_scale(ys);
            let c = BigDecimal::from_str(z).unwrap();
            let rem = &a % &b;
            assert_eq!(rem, c, "{} [{} % {}] == {}", rem, a, b, c);
        }
    }

    #[test]
    fn test_equal() {
        let vals = vec![
            ("2", ".2e1"),
            ("0e1", "0.0"),
            ("0e0", "0.0"),
            ("0e-0", "0.0"),
            ("-0901300e-3", "-901.3"),
            ("-0.901300e+3", "-901.3"),
            ("-0e-1", "-0.0"),
            ("2123121e1231", "212.3121e1235"),
        ];
        for &(x, y) in vals.iter() {
            let a = BigDecimal::from_str(x).unwrap();
            let b = BigDecimal::from_str(y).unwrap();
            assert_eq!(a, b);
        }
    }

    #[test]
    fn test_not_equal() {
        let vals = vec![
            ("2", ".2e2"),
            ("1e45", "1e-900"),
            ("1e+900", "1e-900"),
        ];
        for &(x, y) in vals.iter() {
            let a = BigDecimal::from_str(x).unwrap();
            let b = BigDecimal::from_str(y).unwrap();
            assert!(a != b, "{} == {}", a, b);
        }
    }

    #[test]
    fn test_hash_equal() {
        use stdlib::DefaultHasher;
        use stdlib::hash::{Hash, Hasher};

        fn hash<T>(obj: &T) -> u64
            where T: Hash
        {
            let mut hasher = DefaultHasher::new();
            obj.hash(&mut hasher);
            hasher.finish()
        }

        let vals = vec![
            ("1.1234", "1.1234000"),
            ("1.12340000", "1.1234"),
            ("001.1234", "1.1234000"),
            ("001.1234", "0001.1234"),
            ("1.1234000000", "1.1234000"),
            ("1.12340", "1.1234000000"),
            ("-0901300e-3", "-901.3"),
            ("-0.901300e+3", "-901.3"),
            ("100", "100.00"),
            ("100.00", "100"),
            ("0.00", "0"),
            ("0.00", "0.000"),
            ("-0.00", "0.000"),
            ("0.00", "-0.000"),
        ];
        for &(x,y) in vals.iter() {
            let a = BigDecimal::from_str(x).unwrap();
            let b = BigDecimal::from_str(y).unwrap();
            assert_eq!(a, b);
            assert_eq!(hash(&a), hash(&b), "hash({}) != hash({})", a, b);
        }
    }

    #[test]
    fn test_hash_not_equal() {
        use stdlib::DefaultHasher;
        use stdlib::hash::{Hash, Hasher};

        fn hash<T>(obj: &T) -> u64
            where T: Hash
        {
            let mut hasher = DefaultHasher::new();
            obj.hash(&mut hasher);
            hasher.finish()
        }

        let vals = vec![
            ("1.1234", "1.1234001"),
            ("10000", "10"),
            ("10", "10000"),
            ("10.0", "100"),
        ];
        for &(x,y) in vals.iter() {
            let a = BigDecimal::from_str(x).unwrap();
            let b = BigDecimal::from_str(y).unwrap();
            assert!(a != b, "{} == {}", a, b);
            assert!(hash(&a) != hash(&b), "hash({}) == hash({})", a, b);
        }
    }

    #[test]
    fn test_hash_equal_scale() {
        use stdlib::DefaultHasher;
        use stdlib::hash::{Hash, Hasher};

        fn hash<T>(obj: &T) -> u64
            where T: Hash
        {
            let mut hasher = DefaultHasher::new();
            obj.hash(&mut hasher);
            hasher.finish()
        }

        let vals = vec![
            ("1234.5678", -2, "1200", 0),
            ("1234.5678", -2, "1200", -2),
            ("1234.5678", 0, "1234.1234", 0),
            ("1234.5678", -3, "1200", -3),
            ("-1234", -2, "-1200", 0),
        ];
        for &(x,xs,y,ys) in vals.iter() {
            let a = BigDecimal::from_str(x).unwrap().with_scale(xs);
            let b = BigDecimal::from_str(y).unwrap().with_scale(ys);
            assert_eq!(a, b);
            assert_eq!(hash(&a), hash(&b), "hash({}) != hash({})", a, b);
        }
    }

    #[test]
    fn test_with_prec() {
        let vals = vec![
            ("7", 1, "7"),
            ("7", 2, "7.0"),
            ("895", 2, "900"),
            ("8934", 2, "8900"),
            ("8934", 1, "9000"),
            ("1.0001", 5, "1.0001"),
            ("1.0001", 4, "1"),
            ("1.00009", 6, "1.00009"),
            ("1.00009", 5, "1.0001"),
            ("1.00009", 4, "1.000"),
        ];
        for &(x, p, y) in vals.iter() {
            let a = BigDecimal::from_str(x).unwrap().with_prec(p);
            assert_eq!(a, BigDecimal::from_str(y).unwrap());
        }
    }


    #[test]
    fn test_digits() {
        let vals = vec![
            ("0", 1),
            ("7", 1),
            ("10", 2),
            ("8934", 4),
        ];
        for &(x, y) in vals.iter() {
            let a = BigDecimal::from_str(x).unwrap();
            assert_eq!(a.digits(), y);
        }
    }

    #[test]
    fn test_get_rounding_term() {
        use num_bigint::BigInt;
        use super::get_rounding_term;
        let vals = vec![
            ("0", 0),
            ("4", 0),
            ("5", 1),
            ("10", 0),
            ("15", 0),
            ("49", 0),
            ("50", 1),
            ("51", 1),
            ("8934", 1),
            ("9999", 1),
            ("10000", 0),
            ("50000", 1),
            ("99999", 1),
            ("100000", 0),
            ("100001", 0),
            ("10000000000", 0),
            ("9999999999999999999999999999999999999999", 1),
            ("10000000000000000000000000000000000000000", 0),
        ];
        for &(x, y) in vals.iter() {
            let a = BigInt::from_str(x).unwrap();
            assert_eq!(get_rounding_term(&a), y, "{}", x);
        }
    }

    #[test]
    fn test_abs() {
        let vals = vec![
            ("10", "10"),
            ("-10", "10"),
        ];
        for &(x, y) in vals.iter() {
            let a = BigDecimal::from_str(x).unwrap().abs();
            let b = BigDecimal::from_str(y).unwrap();
            assert!(a == b, "{} == {}", a, b);
        }
    }

    #[test]
    fn test_count_decimal_digits() {
        use num_bigint::BigInt;
        use super::count_decimal_digits;
        let vals = vec![
            ("10", 2),
            ("1", 1),
            ("9", 1),
            ("999", 3),
            ("1000", 4),
            ("9900", 4),
            ("9999", 4),
            ("10000", 5),
            ("99999", 5),
            ("100000", 6),
            ("999999", 6),
            ("1000000", 7),
            ("9999999", 7),
            ("999999999999", 12),
            ("999999999999999999999999", 24),
            ("999999999999999999999999999999999999999999999999", 48),
            ("999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999", 96),
            ("199999911199999999999999999999999999999999999999999999999999999999999999999999999999999999999000", 96),
            ("999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999991", 192),
            ("199999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999", 192),
            ("-1", 1),
            ("-6", 1),
            ("-10", 2),
            ("-999999999999999999999999", 24),
        ];
        for &(x, y) in vals.iter() {
            let a = BigInt::from_str(x).unwrap();
            let b = count_decimal_digits(&a);
            assert_eq!(b, y);
        }
    }

    #[test]
    fn test_half() {
        let vals = vec![
            ("100", "50."),
            ("2", "1"),
            (".2", ".1"),
            ("42", "21"),
            ("3", "1.5"),
            ("99", "49.5"),
            ("3.141592653", "1.5707963265"),
            ("3.1415926536", "1.5707963268"),
        ];
        for &(x, y) in vals.iter() {
            let a = BigDecimal::from_str(x).unwrap().half();
            let b = BigDecimal::from_str(y).unwrap();
            assert_eq!(a, b);
            assert_eq!(a.scale, b.scale);
        }
    }

    #[test]
    fn test_round() {
        let test_cases = vec![
            ("1.45", 1, "1.4"),
            ("1.444445", 1, "1.4"),
            ("1.44", 1, "1.4"),
            ("0.444", 2, "0.44"),
            ("4.5", 0, "4"),
            ("4.05", 1, "4.0"),
            ("4.050", 1, "4.0"),
            ("4.15", 1, "4.2"),
            ("0.0045", 2, "0.00"),
            ("5.5", -1, "10"),
            ("-1.555", 2, "-1.56"),
            ("-1.555", 99, "-1.555"),
            ("5.5", 0, "6"),
            ("-1", -1, "0"),
            ("5", -1, "0"),
            ("44", -1, "40"),
            ("44", -99, "0"),
            ("44", 99, "44"),
            ("1.4499999999", -1, "0"),
            ("1.4499999999", 0, "1"),
            ("1.4499999999", 1, "1.4"),
            ("1.4499999999", 2, "1.45"),
            ("1.4499999999", 3, "1.450"),
            ("1.4499999999", 4, "1.4500"),
            ("1.4499999999", 10, "1.4499999999"),
            ("1.4499999999", 15, "1.449999999900000"),
            ("-1.4499999999", 1, "-1.4"),
            ("1.449999999", 1, "1.4"),
            ("-9999.444455556666", 10, "-9999.4444555567"),
            ("-12345678987654321.123456789", 8, "-12345678987654321.12345679"),
            ("0.33333333333333333333333333333333333333333333333333333333333333333333333333333333333333", 0, "0"),
            ("0.1165085714285714285714285714285714285714", 0, "0"),
            ("0.1165085714285714285714285714285714285714", 2, "0.12"),
            ("0.1165085714285714285714285714285714285714", 5, "0.11651"),
            ("0.1165085714285714285714285714285714285714", 8, "0.11650857"),
        ];
        for &(x, digits, y) in test_cases.iter() {
            let a = BigDecimal::from_str(x).unwrap();
            let b = BigDecimal::from_str(y).unwrap();
            let rounded = a.round(digits);
            assert_eq!(rounded, b);
        }
    }

    #[test]
    fn round_large_number() {
        use super::BigDecimal;

        let z = BigDecimal::from_str("3.4613133327063255443352353815722045816611958409944513040035462804475524").unwrap();
        let expected = BigDecimal::from_str("11.9806899871705702711783103817684242408972124568942276285200973527647213").unwrap();
        let zsq = &z*&z;
        let zsq = zsq.round(70);
        debug_assert_eq!(zsq, expected);
    }

    #[test]
    fn test_is_integer() {
        let true_vals = vec![
            "100",
            "100.00",
            "1724e4",
            "31.47e8",
            "-31.47e8",
            "-0.0",
        ];

        let false_vals = vec![
            "100.1",
            "0.001",
            "3147e-3",
            "3147e-8",
            "-0.01",
            "-1e-3",
        ];

        for s in true_vals {
            let d = BigDecimal::from_str(&s).unwrap();
            assert!(d.is_integer());
        }

        for s in false_vals {
            let d = BigDecimal::from_str(&s).unwrap();
            assert!(!d.is_integer());
        }
    }

    #[test]
    fn test_inverse() {
        let vals = vec![
            ("100", "0.01"),
            ("2", "0.5"),
            (".2", "5"),
            ("3.141592653", "0.3183098862435492205742690218851870990799646487459493049686604293188738877535183744268834079171116523"),
        ];
        for &(x, y) in vals.iter() {
            let a = BigDecimal::from_str(x).unwrap();
            let i = a.inverse();
            let b = BigDecimal::from_str(y).unwrap();
            assert_eq!(i, b);
            assert_eq!(BigDecimal::from(1)/&a, b);
            assert_eq!(i.inverse(), a);
            // assert_eq!(a.scale, b.scale, "scale mismatch ({} != {}", a, b);
        }
    }

    #[test]
    fn test_sqrt() {
        let vals = vec![
            ("1e-232", "1e-116"),
            ("1.00", "1"),
            ("1.001", "1.000499875062460964823258287700109753027590031219780479551442971840836093890879944856933288426795152"),
            ("100", "10"),
            ("49", "7"),
            (".25", ".5"),
            ("0.0152399025", ".12345"),
            ("152399025", "12345"),
            (".00400", "0.06324555320336758663997787088865437067439110278650433653715009705585188877278476442688496216758600590"),
            (".1", "0.3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295"),
            ("2", "1.414213562373095048801688724209698078569671875376948073176679737990732478462107038850387534327641573"),
            ("125348", "354.0451948551201563108487193176101314241016013304294520812832530590100407318465590778759640828114535"),
            ("18446744073709551616.1099511", "4294967296.000000000012799992691725492477397918722952224079252026972356303360555051219312462698703293"),
            ("3.141592653589793115997963468544185161590576171875", "1.772453850905515992751519103139248439290428205003682302442979619028063165921408635567477284443197875"),
            (".000000000089793115997963468544185161590576171875", "0.000009475922962855041517561783740144225422359796851494316346796373337470068631250135521161989831460407155"),
            ("0.7177700109762963922745342343167413624881759290454997218753321040760896053150388903350654937434826216803814031987652326749140535150336357405672040727695124057298138872112244784753994931999476811850580200000000000000000000000000000000", "0.8472130847527653667042980517799020703921106560594525833177762276594388966885185567535692987624493813"),
            ("0.01234567901234567901234567901234567901234567901234567901234567901234567901234567901234567901234567901", "0.1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111"),
            ("0.1108890000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000444", "0.3330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000667"),
        ];
        for &(x, y) in vals.iter() {
            let a = BigDecimal::from_str(x).unwrap().sqrt().unwrap();
            let b = BigDecimal::from_str(y).unwrap();
            assert_eq!(a, b);
        }
    }

    #[test]
    fn test_big_sqrt() {
        use num_bigint::BigInt;
        let vals = vec![
            (("2", -70), "141421356237309504880168872420969807.8569671875376948073176679737990732478462107038850387534327641573"),
            (("3", -170), "17320508075688772935274463415058723669428052538103806280558069794519330169088000370811.46186757248576"),
            (("9", -199), "9486832980505137995996680633298155601158665417975650480572514558377783315917714664032744325137900886"),
            (("7", -200), "26457513110645905905016157536392604257102591830824501803683344592010688232302836277603928864745436110"),
            (("777", -204), "2.787471972953270789531596912111625325974789615194854615319795902911796043681078997362635440358922503E+103"),
            (("7", -600), "2.645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543611E+300"),
            (("2", -900), "1.414213562373095048801688724209698078569671875376948073176679737990732478462107038850387534327641573E+450"),
            (("7", -999), "8.366600265340755479781720257851874893928153692986721998111915430804187725943170098308147119649515362E+499"),
            (("74908163946345982392040522594123773796", -999), "2.736935584670307552030924971360722787091742391079630976117950955395149091570790266754718322365663909E+518"),
            (("20", -1024), "4.472135954999579392818347337462552470881236719223051448541794490821041851275609798828828816757564550E512"),
            (("3", 1025), "5.477225575051661134569697828008021339527446949979832542268944497324932771227227338008584361638706258E-513"),
        ];
        for &((s, scale), e) in vals.iter() {
            let expected = BigDecimal::from_str(e).unwrap();

            let sqrt = BigDecimal::new(BigInt::from_str(s).unwrap(), scale).sqrt().unwrap();
            assert_eq!(sqrt, expected);
        }
    }

    #[test]
    fn test_cbrt() {
        let vals = vec![
            ("0.00", "0"),
            ("1.00", "1"),
            ("1.001", "1.000333222283909495175449559955220102010284758197360454054345461242739715702641939155238095670636841"),
            ("10", "2.154434690031883721759293566519350495259344942192108582489235506346411106648340800185441503543243276"),
            ("-59283293e25", "-84006090355.84281237113712383191213626687332139035750444925827809487776780721673264524620270275301685"),
            ("94213372931e-127", "2.112049945275324414051072540210070583697242797173805198575907094646677475250362108901530353886613160E-39"),
        ];
        for &(x, y) in vals.iter() {
            let a = BigDecimal::from_str(x).unwrap().cbrt();
            let b = BigDecimal::from_str(y).unwrap();
            assert_eq!(a, b);
        }
    }

    mod double {
        use super::*;

        include!("lib.tests.double.rs");
    }

    #[test]
    fn test_square() {
        let vals = vec![
            ("1.00", "1.00"),
            ("1.5", "2.25"),
            ("1.50", "2.2500"),
            ("5", "25"),
            ("5.0", "25.00"),
            ("-5.0", "25.00"),
            ("5.5", "30.25"),
            ("0.80", "0.6400"),
            ("0.01234", "0.0001522756"),
            ("3.1415926", "9.86960406437476"),
        ];
        for &(x, y) in vals.iter() {
            let a = BigDecimal::from_str(x).unwrap().square();
            let b = BigDecimal::from_str(y).unwrap();
            assert_eq!(a, b);
            assert_eq!(a.scale, b.scale);
        }
    }

    #[test]
    fn test_cube() {
        let vals = vec![
            ("1.00", "1.00"),
            ("1.50", "3.375000"),
            ("5", "125"),
            ("5.0", "125.000"),
            ("5.00", "125.000000"),
            ("-5", "-125"),
            ("-5.0", "-125.000"),
            ("2.01", "8.120601"),
            ("5.5", "166.375"),
            ("0.01234", "0.000001879080904"),
            ("3.1415926", "31.006275093569669642776"),
        ];
        for &(x, y) in vals.iter() {
            let a = BigDecimal::from_str(x).unwrap().cube();
            let b = BigDecimal::from_str(y).unwrap();
            assert_eq!(a, b);
            assert_eq!(a.scale, b.scale);
        }
    }

    #[test]
    fn test_exp() {
        let vals = vec![
            ("0", "1"),
            ("1", "2.718281828459045235360287471352662497757247093699959574966967627724076630353547594571382178525166427"),
            ("1.01", "2.745601015016916493989776316660387624073750819595962291667398087987297168243899027802501018008905180"),
            ("0.5", "1.648721270700128146848650787814163571653776100710148011575079311640661021194215608632776520056366643"),
            ("-1", "0.3678794411714423215955237701614608674458111310317678345078368016974614957448998033571472743459196437"),
            ("-0.01", "0.9900498337491680535739059771800365577720790812538374668838787452931477271687452950182155307793838110"),
            ("-10.04", "0.00004361977305405268676261569570537884674661515701779752139657120453194647205771372804663141467275928595"),
            //("-1000.04", "4.876927702336787390535723208392195312680380995235400234563172353460484039061383367037381490416091595E-435"),
            ("-20.07", "1.921806899438469499721914055500607234723811054459447828795824348465763824284589956630853464778332349E-9"),
            ("10", "22026.46579480671651695790064528424436635351261855678107423542635522520281857079257519912096816452590"),
            ("20", "485165195.4097902779691068305415405586846389889448472543536108003159779961427097401659798506527473494"),
            //("777.7", "5.634022488451236612534495413455282583175841288248965283178668787259870456538271615076138061788051442E+337"),
        ];
        for &(x, y) in vals.iter() {
            let a = BigDecimal::from_str(x).unwrap().exp();
            let b = BigDecimal::from_str(y).unwrap();
            assert_eq!(a, b);
        }
    }

    #[test]
    fn test_from_str() {
        let vals = vec![
            ("1331.107", 1331107, 3),
            ("1.0", 10, 1),
            ("2e1", 2, -1),
            ("0.00123", 123, 5),
            ("-123", -123, 0),
            ("-1230", -1230, 0),
            ("12.3", 123, 1),
            ("123e-1", 123, 1),
            ("1.23e+1", 123, 1),
            ("1.23E+3", 123, -1),
            ("1.23E-8", 123, 10),
            ("-1.23E-10", -123, 12),
            ("123_", 123, 0),
            ("31_862_140.830_686_979", 31862140830686979, 9),
            ("-1_1.2_2", -1122, 2),
            ("999.521_939", 999521939, 6),
            ("679.35_84_03E-2", 679358403, 8),
            ("271576662.__E4", 271576662, -4),
        ];

        for &(source, val, scale) in vals.iter() {
            let x = BigDecimal::from_str(source).unwrap();
            assert_eq!(x.int_val.to_i64().unwrap(), val);
            assert_eq!(x.scale, scale);
        }
    }

    #[test]
    fn test_fmt() {
        let vals = vec![
            // b  s   ( {}        {:.1}     {:.4}      {:4.1}  {:+05.1}  {:<4.1}
            (1, 0,  (  "1",     "1.0",    "1.0000",  " 1.0",  "+01.0",   "1.0 " )),
            (1, 1,  (  "0.1",   "0.1",    "0.1000",  " 0.1",  "+00.1",   "0.1 " )),
            (1, 2,  (  "0.01",  "0.0",    "0.0100",  " 0.0",  "+00.0",   "0.0 " )),
            (1, -2, ("100",   "100.0",  "100.0000", "100.0", "+100.0", "100.0" )),
            (-1, 0, ( "-1",    "-1.0",   "-1.0000",  "-1.0",  "-01.0",  "-1.0" )),
            (-1, 1, ( "-0.1",  "-0.1",   "-0.1000",  "-0.1",  "-00.1",  "-0.1" )),
            (-1, 2, ( "-0.01", "-0.0",   "-0.0100",  "-0.0",  "-00.0",  "-0.0" )),
        ];
        for (i, scale, results) in vals {
            let x = BigDecimal::new(num_bigint::BigInt::from(i), scale);
            assert_eq!(format!("{}", x), results.0);
            assert_eq!(format!("{:.1}", x), results.1);
            assert_eq!(format!("{:.4}", x), results.2);
            assert_eq!(format!("{:4.1}", x), results.3);
            assert_eq!(format!("{:+05.1}", x), results.4);
            assert_eq!(format!("{:<4.1}", x), results.5);
        }
    }

    #[test]
    fn test_debug() {
        let vals = vec![
            ("BigDecimal(\"123.456\")", "123.456"),
            ("BigDecimal(\"123.400\")", "123.400"),
            ("BigDecimal(\"1.20\")", "01.20"),
            // ("BigDecimal(\"1.2E3\")", "01.2E3"), <- ambiguous precision
            ("BigDecimal(\"1200\")", "01.2E3"),
        ];

        for (expected, source) in vals {
            let var = BigDecimal::from_str(source).unwrap();
            assert_eq!(format!("{:?}", var), expected);
        }
    }

    #[test]
    fn test_signed() {
        assert!(!BigDecimal::zero().is_positive());
        assert!(!BigDecimal::one().is_negative());

        assert!(BigDecimal::one().is_positive());
        assert!((-BigDecimal::one()).is_negative());
        assert!((-BigDecimal::one()).abs().is_positive());
    }

    #[test]
    fn test_normalize() {
        use num_bigint::BigInt;

        let vals = vec![
            (BigDecimal::new(BigInt::from(10), 2),
            BigDecimal::new(BigInt::from(1), 1),
            "0.1"),
            (BigDecimal::new(BigInt::from(132400), -4),
            BigDecimal::new(BigInt::from(1324), -6),
            "1324000000"),
            (BigDecimal::new(BigInt::from(1_900_000), 3),
            BigDecimal::new(BigInt::from(19), -2),
            "1900"),
            (BigDecimal::new(BigInt::from(0), -3),
            BigDecimal::zero(),
            "0"),
            (BigDecimal::new(BigInt::from(0), 5),
            BigDecimal::zero(),
            "0"),
        ];

        for (not_normalized, normalized, string) in vals {
            assert_eq!(not_normalized.normalized(), normalized);
            assert_eq!(not_normalized.normalized().to_string(), string);
            assert_eq!(normalized.to_string(), string);
        }
    }

    #[test]
    #[should_panic(expected = "InvalidDigit")]
    fn test_bad_string_nan() {
        BigDecimal::from_str("hello").unwrap();
    }
    #[test]
    #[should_panic(expected = "Empty")]
    fn test_bad_string_empty() {
        BigDecimal::from_str("").unwrap();
    }
    #[test]
    #[should_panic(expected = "InvalidDigit")]
    fn test_bad_string_invalid_char() {
        BigDecimal::from_str("12z3.12").unwrap();
    }
    #[test]
    #[should_panic(expected = "InvalidDigit")]
    fn test_bad_string_nan_exponent() {
        BigDecimal::from_str("123.123eg").unwrap();
    }
    #[test]
    #[should_panic(expected = "Empty")]
    fn test_bad_string_empty_exponent() {
        BigDecimal::from_str("123.123E").unwrap();
    }
    #[test]
    #[should_panic(expected = "InvalidDigit")]
    fn test_bad_string_multiple_decimal_points() {
        BigDecimal::from_str("123.12.45").unwrap();
    }
    #[test]
    #[should_panic(expected = "Empty")]
    fn test_bad_string_only_decimal() {
        BigDecimal::from_str(".").unwrap();
    }
    #[test]
    #[should_panic(expected = "Empty")]
    fn test_bad_string_only_decimal_and_exponent() {
        BigDecimal::from_str(".e4").unwrap();
    }

    #[test]
    fn test_from_i128() {
        let value = BigDecimal::from_i128(-368934881474191032320).unwrap();
        let expected = BigDecimal::from_str("-368934881474191032320").unwrap();
        assert_eq!(value, expected);
    }

    #[test]
    fn test_from_u128() {
        let value = BigDecimal::from_u128(668934881474191032320).unwrap();
        let expected = BigDecimal::from_str("668934881474191032320").unwrap();
        assert_eq!(value, expected);
    }
}


#[cfg(test)]
#[allow(non_snake_case)]
mod test_with_scale_round {
    use super::*;
    use paste::paste;

    include!("lib.tests.with_scale_round.rs");
}


#[cfg(all(test, property_tests))]
extern crate proptest;

#[cfg(all(test, property_tests))]
mod proptests {
    use super::*;
    use paste::paste;
    use proptest::*;

    include!("lib.tests.property-tests.rs");
}
