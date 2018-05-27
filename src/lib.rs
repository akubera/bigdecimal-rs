// Copyright 2016 Adam Sunderland
//           2016-2017 Andrew Kubera
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

extern crate num;
extern crate num_traits as traits;
#[cfg(feature = "serde")]
extern crate serde;

use num::{bigint, integer};

use std::fmt;
use std::error::Error;
use std::cmp::Ordering;
use std::default::Default;
use std::str::{self, FromStr};
use std::hash::{Hash, Hasher};
use std::num::{ParseFloatError, ParseIntError};
use std::ops::{Add, Div, Mul, Rem, Sub, AddAssign, MulAssign, SubAssign, Neg};

use integer::Integer;
use bigint::{BigInt, ParseBigIntError, Sign, ToBigInt};
pub use traits::{Num, Zero, One, FromPrimitive, ToPrimitive, Signed};

macro_rules! forward_val_val_binop {
    (impl $imp:ident for $res:ty, $method:ident) => {
        impl $imp<$res> for $res {
            type Output = $res;

            #[inline]
            fn $method(self, other: $res) -> $res {
                // forward to val-ref
                $imp::$method(self, &other)
            }
        }
    }
}

macro_rules! forward_ref_val_binop {
    (impl $imp:ident for $res:ty, $method:ident) => {
        impl<'a> $imp<$res> for &'a $res {
            type Output = $res;

            #[inline]
            fn $method(self, other: $res) -> $res {
                // forward to ref-ref
                $imp::$method(self, &other)
            }
        }
    }
}

macro_rules! forward_val_ref_binop {
    (impl $imp:ident for $res:ty, $method:ident) => {
        impl<'a> $imp<&'a $res> for $res {
            type Output = $res;

            #[inline]
            fn $method(self, other: &$res) -> $res {
                // forward to ref-ref
                $imp::$method(&self, other)
            }
        }
    }
}


// Forward everything to ref-ref, when reusing storage is not helpful
macro_rules! forward_all_binop_to_ref_ref {
    (impl $imp:ident for $res:ty, $method:ident) => {
        forward_val_val_binop!(impl $imp for $res, $method);
        forward_val_ref_binop!(impl $imp for $res, $method);
        forward_ref_val_binop!(impl $imp for $res, $method);
    };
}


#[inline]
fn ten_to_the(pow: u64) -> BigInt {
    if pow < 20 {
        BigInt::from(10u64.pow(pow as u32))
    } else {
        let (half, rem) = pow.div_rem(&16);

        let mut x = ten_to_the(half);

        for _ in 0..4 {
            x = &x * &x;
        }

        if rem == 0 { x } else { x * ten_to_the(rem) }
    }
}

macro_rules! forward_val_assignop {
    (impl $imp:ident for $res:ty, $method:ident) => {
        impl $imp<$res> for $res {
            #[inline]
            fn $method(&mut self, other: $res) {
                // forward to mutref-ref
                $imp::$method(self, &other)
            }
        }
    }
}

/// A big decimal type.
///
#[derive(Clone, Debug, Eq)]
pub struct BigDecimal {
    int_val: BigInt,
    scale: i64,
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

    /// Creates and initializes a `BigDecimal`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bigdecimal::{BigDecimal, Zero};
    ///
    /// assert_eq!(BigDecimal::parse_bytes(b"0", 10).unwrap(), BigDecimal::zero());
    /// // assert_eq!(BigDecimal::parse_bytes(b"f", 16), BigDecimal::parse_bytes(b"16", 10));
    /// ```
    #[inline]
    pub fn parse_bytes(buf: &[u8], radix: u32) -> Option<BigDecimal> {
        str::from_utf8(buf).ok().and_then(|s| {
            BigDecimal::from_str_radix(s, radix).ok()
        })
    }

    /// Return a new BigDecimal object equivalent to self, with internal
    /// scaling set to the number specified.
    /// If the new_scale is lower than the current value, digits will
    /// be dropped.
    ///
    #[inline]
    pub fn with_scale(&self, new_scale: i64) -> BigDecimal {

        if self.int_val.is_zero() {
            return BigDecimal::new(BigInt::zero(), new_scale);
        }

        if new_scale > self.scale {
            let scale_diff = new_scale - self.scale;
            let int_val = &self.int_val * ten_to_the(scale_diff as u64);
            BigDecimal::new(int_val, new_scale)
        } else if new_scale < self.scale {
            let scale_diff = self.scale - new_scale;
            let int_val = &self.int_val / ten_to_the(scale_diff as u64);
            BigDecimal::new(int_val, new_scale)
        } else {
            self.clone()
        }
    }

    /// Return the sign of the `BigDecimal` as `num::bigint::Sign`.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate num;
    /// extern crate bigdecimal;
    /// use std::str::FromStr;
    ///
    /// assert_eq!(bigdecimal::BigDecimal::from_str("-1").unwrap().sign(), num::bigint::Sign::Minus);
    /// assert_eq!(bigdecimal::BigDecimal::from_str("0").unwrap().sign(), num::bigint::Sign::NoSign);
    /// assert_eq!(bigdecimal::BigDecimal::from_str("1").unwrap().sign(), num::bigint::Sign::Plus);
    /// ```
    #[inline]
    pub fn sign(&self) -> num::bigint::Sign {
        self.int_val.sign()
    }

    /// Return the internal big integer value and an exponent
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate num;
    /// extern crate bigdecimal;
    /// use std::str::FromStr;
    ///
    /// assert_eq!(bigdecimal::BigDecimal::from_str("1.1").unwrap().as_bigint_and_exponent(),
    ///            (num::bigint::BigInt::from_str("11").unwrap(), 1));
    #[inline]
    pub fn as_bigint_and_exponent(&self) -> (BigInt, i64) {
        (self.int_val.clone(), self.scale)
    }

    /// Convert into the internal big integer value and an exponent
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate num;
    /// extern crate bigdecimal;
    /// use std::str::FromStr;
    ///
    /// assert_eq!(bigdecimal::BigDecimal::from_str("1.1").unwrap().into_bigint_and_exponent(),
    ///            (num::bigint::BigInt::from_str("11").unwrap(), 1));
    #[inline]
    pub fn into_bigint_and_exponent(self) -> (BigInt, i64) {
        (self.int_val, self.scale)
    }

    /// Compute the absolute value of number
    #[inline]
    pub fn abs(&self) -> BigDecimal {
        BigDecimal {
            int_val: self.int_val.abs(),
            scale: self.scale,
        }
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

impl Error for ParseBigDecimalError {
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

impl Hash for BigDecimal {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut dec_str = self.int_val.to_str_radix(10).to_string();
        let scale = self.scale;
        let zero = self.int_val.is_zero();
        if scale > 0 && !zero {
                let mut cnt = 0;
                dec_str = dec_str
                    .trim_right_matches(|x| {
                        cnt += 1;
                        x == '0' && cnt <= scale
                    }).to_string();
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

impl PartialEq for BigDecimal {
    #[inline]
    fn eq(&self, rhs: &BigDecimal) -> bool {
        // fix scale and test equality
        if self.scale > rhs.scale {
            let scaled_int_val = &rhs.int_val * ten_to_the((self.scale - rhs.scale) as u64);
            self.int_val == scaled_int_val
        } else if self.scale < rhs.scale {
            let scaled_int_val = &self.int_val * ten_to_the((rhs.scale - self.scale) as u64);
            scaled_int_val == rhs.int_val
        } else {
            self.int_val == rhs.int_val
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

forward_all_binop_to_ref_ref!(impl Add for BigDecimal, add);

impl<'a, 'b> Add<&'b BigDecimal> for &'a BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn add(self, rhs: &BigDecimal) -> BigDecimal {
        if self.scale < rhs.scale {
            let scaled = self.with_scale(rhs.scale);
            BigDecimal::new(scaled.int_val + &rhs.int_val, rhs.scale)

        } else if self.scale > rhs.scale {
            let scaled = rhs.with_scale(self.scale);
            BigDecimal::new(&self.int_val + scaled.int_val, self.scale)

        } else {
            BigDecimal::new(&self.int_val + &rhs.int_val, self.scale)
        }
    }
}

forward_val_assignop!(impl AddAssign for BigDecimal, add_assign);

impl<'a> AddAssign<&'a BigDecimal> for BigDecimal {
    #[inline]
    fn add_assign(&mut self, rhs: &BigDecimal) {
        if self.scale < rhs.scale {
            let scaled = self.with_scale(rhs.scale);
            self.int_val = scaled.int_val + &rhs.int_val;
            self.scale = rhs.scale;

        } else if self.scale > rhs.scale {
            let scaled = rhs.with_scale(self.scale);
            // Whenever `rust-num` implements AddAssign on BigInt
            // this can be simplified. More cases follow.
            self.int_val = &self.int_val + scaled.int_val;

        } else {
            self.int_val = &self.int_val + &rhs.int_val;
        }
    }
}

forward_all_binop_to_ref_ref!(impl Sub for BigDecimal, sub);

impl<'a, 'b> Sub<&'b BigDecimal> for &'a BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn sub(self, rhs: &BigDecimal) -> BigDecimal {
        if self.scale < rhs.scale {
            let scaled = self.with_scale(rhs.scale);
            BigDecimal::new(scaled.int_val - &rhs.int_val, rhs.scale)

        } else if self.scale > rhs.scale {
            let scaled = rhs.with_scale(self.scale);
            BigDecimal::new(&self.int_val - scaled.int_val, self.scale)

        } else {
            BigDecimal::new(&self.int_val - &rhs.int_val, self.scale)
        }
    }
}

forward_val_assignop!(impl SubAssign for BigDecimal, sub_assign);

impl<'a> SubAssign<&'a BigDecimal> for BigDecimal {
    #[inline]
    fn sub_assign(&mut self, rhs: &BigDecimal) {
        if self.scale < rhs.scale {
            let scaled = self.with_scale(rhs.scale);
            self.int_val = scaled.int_val - &rhs.int_val;
            self.scale = rhs.scale;

        } else if self.scale > rhs.scale {
            let scaled = rhs.with_scale(self.scale);
            self.int_val = &self.int_val - scaled.int_val;

        } else {
            self.int_val = &self.int_val - &rhs.int_val;
        }
    }
}

forward_all_binop_to_ref_ref!(impl Mul for BigDecimal, mul);

impl<'a, 'b> Mul<&'b BigDecimal> for &'a BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn mul(self, rhs: &BigDecimal) -> BigDecimal {
        let scale = self.scale + rhs.scale;
        BigDecimal::new(&self.int_val * &rhs.int_val, scale)
    }
}

forward_val_assignop!(impl MulAssign for BigDecimal, mul_assign);

impl<'a> MulAssign<&'a BigDecimal> for BigDecimal {
    #[inline]
    fn mul_assign(&mut self, rhs: &BigDecimal) {
        self.scale += rhs.scale;
        self.int_val = &self.int_val * &rhs.int_val;
    }
}

forward_all_binop_to_ref_ref!(impl Div for BigDecimal, div);

impl<'a, 'b> Div<&'b BigDecimal> for &'a BigDecimal {
    type Output = BigDecimal;

    #[inline]
    #[allow(non_snake_case)]
    fn div(self, other: &BigDecimal) -> BigDecimal {
        let scale = self.scale - other.scale;
        let num = &self.int_val;
        let den = &other.int_val;
        let (quotient, remainder) = num.div_rem(den);

        // no remainder - quotient is final solution
        if remainder == BigInt::zero() {
            return BigDecimal::new(quotient, scale);
        }

        let BIG_TEN = &BigInt::from_i8(10).unwrap();
        let mut remainder = remainder * BIG_TEN;
        let mut quotient = quotient;

        let MAX_ITERATIONS = 100;
        let mut iteration_count = 0;
        while remainder != BigInt::zero() && iteration_count < MAX_ITERATIONS {
            let (q, r) = remainder.div_rem(den);
            quotient = quotient * BIG_TEN + q;
            remainder = r * BIG_TEN;

            iteration_count += 1;
        }
        let scale = scale + iteration_count;
        BigDecimal::new(quotient, scale)
    }
}

forward_all_binop_to_ref_ref!(impl Rem for BigDecimal, rem);

impl<'a, 'b> Rem<&'b BigDecimal> for &'a BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn rem(self, _: &BigDecimal) -> BigDecimal {
        // let (_, r) = self.div_rem(other);
        // return r;
        self.clone()
    }
}

impl Neg for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn neg(mut self) -> BigDecimal {
        self.int_val = -self.int_val;
        self
    }
}

impl<'a> Neg for &'a BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn neg(self) -> BigDecimal {
        -self.clone()
    }
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

impl fmt::Display for BigDecimal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Aquire the absolute integer as a decimal string
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
                let abs_int = abs_int + "0".repeat(zeros as usize).as_str();
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

        let non_negative = match self.int_val.sign() {
            Sign::Plus | Sign::NoSign => true,
            _ => false,
        };
        //pad_integral does the right thing although we have a decimal
        f.pad_integral(non_negative, "", &complete_without_sign)
    }
}

impl Num for BigDecimal {
    type FromStrRadixErr = ParseBigDecimalError;

    /// Creates and initializes a BigDecimal.
    #[inline]
    fn from_str_radix(s: &str, radix: u32) -> Result<BigDecimal, ParseBigDecimalError> {
        if radix != 10 {
            return Err(ParseBigDecimalError::Other(
                String::from("The radix for decimal MUST be 10"),
            ));
        }

        let exp_separator: &[_] = &['e', 'E'];

        // split slice into base and exponent parts
        let (base_part, exponent_value) = match s.find(exp_separator) {
            // exponent defaults to 0 if (e|E) not found
            None => (s, 0),

            // split and parse exponent field
            Some(loc) => {
                // slice up to `loc` and 1 after to skip the 'e' char
                let (base, exp) = (&s[..loc], &s[loc + 1..]);

                // special consideration for rust 1.0.0 which would not
                // parse a leading '+'
                let exp = match exp.chars().next() {
                    Some('+') => &exp[1..],
                    _ => exp,
                };

                (base, try!(i64::from_str(exp)))
            }
        };

        // TEMPORARY: Test for emptiness - remove once BigInt supports similar error
        if base_part == "" {
            return Err(ParseBigDecimalError::Empty);
        }

        // split decimal into a digit string and decimal-point offset
        let (digits, decimal_offset): (String, _) = match base_part.find('.') {
            // No dot! pass directly to BigInt
            None => (base_part.to_string(), 0),

            // decimal point found - necessary copy into new string buffer
            Some(loc) => {
                // split into leading and trailing digits
                let (lead, trail) = (&base_part[..loc], &base_part[loc + 1..]);

                // copy all leading characters into 'digits' string
                let mut digits = String::from(lead);

                // copy all trailing characters after '.' into the digits string
                digits.push_str(trail);

                (digits, trail.len() as i64)
            }
        };

        let scale = decimal_offset - exponent_value;
        let big_int = try!(BigInt::from_str_radix(&digits, radix));

        Ok(BigDecimal::new(big_int, scale))
    }
}

impl ToPrimitive for BigDecimal {
    fn to_i64(&self) -> Option<i64> {
        match self.sign() {
            Sign::Minus | Sign::Plus => self.with_scale(0).int_val.to_i64(),
            Sign::NoSign => Some(0),
        }
    }
    fn to_u64(&self) -> Option<u64> {
        match self.sign() {
            Sign::Plus => self.with_scale(0).int_val.to_u64(),
            Sign::NoSign => Some(0),
            Sign::Minus => None,
        }
    }

    fn to_f64(&self) -> Option<f64> {
        self.int_val.to_f64().map(
            |x| x * 10f64.powi(-self.scale as i32),
        )
    }
}

impl From<i64> for BigDecimal {
    #[inline]
    fn from(n: i64) -> Self {
        BigDecimal {
            int_val: BigInt::from(n),
            scale: 0,
        }
    }
}

impl From<u64> for BigDecimal {
    #[inline]
    fn from(n: u64) -> Self {
        BigDecimal {
            int_val: BigInt::from(n),
            scale: 0,
        }
    }
}

impl From<(BigInt, i64)> for BigDecimal {
    #[inline]
    fn from((int_val, scale): (BigInt, i64)) -> Self {
        BigDecimal {
            int_val: int_val,
            scale: scale,
        }
    }
}


macro_rules! impl_from_type {
    ($FromType:ty, $AsType:ty) => {
        impl From<$FromType> for BigDecimal {
            #[inline]
            fn from(n: $FromType) -> Self {
                BigDecimal::from(n as $AsType)
            }
        }
    }
}

impl_from_type!(u8, u64);
impl_from_type!(u16, u64);
impl_from_type!(u32, u64);

impl_from_type!(i8, i64);
impl_from_type!(i16, i64);
impl_from_type!(i32, i64);

impl From<f32> for BigDecimal {
    #[inline]
    fn from(n: f32) -> Self {
        BigDecimal::from_str(&format!(
            "{:.PRECISION$e}",
            n,
            PRECISION = ::std::f32::DIGITS as usize
        )).unwrap()
    }
}

impl From<f64> for BigDecimal {
    #[inline]
    fn from(n: f64) -> Self {
        BigDecimal::from_str(&format!(
            "{:.PRECISION$e}",
            n,
            PRECISION = ::std::f64::DIGITS as usize
        )).unwrap()
    }
}

impl FromPrimitive for BigDecimal {
    #[inline]
    fn from_i64(n: i64) -> Option<Self> {
        Some(BigDecimal::from(n))
    }

    #[inline]
    fn from_u64(n: u64) -> Option<Self> {
        Some(BigDecimal::from(n))
    }

    #[inline]
    fn from_f32(n: f32) -> Option<Self> {
        Some(BigDecimal::from(n))
    }

    #[inline]
    fn from_f64(n: f64) -> Option<Self> {
        Some(BigDecimal::from(n))
    }
}


impl ToBigInt for BigDecimal {
    fn to_bigint(&self) -> Option<BigInt> {
        Some(self.with_scale(0).int_val)
    }
}

/// Tools to help serializing/deserializing `BigDecimal`s
#[cfg(feature = "serde")]
mod bigdecimal_serde {
    use std::fmt;
    use super::BigDecimal;
    use serde::{ser, de};

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
            use std::str::FromStr;
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
            Ok(BigDecimal::from(value))
        }
    }

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
        use std::str::FromStr;

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
        use std::str::FromStr;

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

    #[cfg_attr(rustfmt, rustfmt_skip)]
    #[test]
    fn test_serde_deserialize_int() {
        use traits::FromPrimitive;

        let vals = vec![
            0,
            1,
            81516161,
            -370,
            -8,
            -99999999999,
        ];
        for n in vals {
            let expected = BigDecimal::from_i64(n).unwrap();
            let value: BigDecimal = serde_json::from_str(&serde_json::to_string(&n).unwrap()).unwrap();
            assert_eq!(expected, value);
        }
    }

    #[test]
    fn test_serde_deserialize_f64() {
        use traits::FromPrimitive;

        let vals = vec![
            1.0,
            0.5,
            0.25,
            50.0,
            50000.,
            0.001,
            12.34,
            5.0 * 0.03125,
            ::std::f64::consts::PI,
            ::std::f64::consts::PI * 10000.0,
            ::std::f64::consts::PI * 30000.0,
        ];
        for n in vals {
            let expected = BigDecimal::from_f64(n).unwrap();
            let value: BigDecimal = serde_json::from_str(&serde_json::to_string(&n).unwrap())
                .unwrap();
            assert_eq!(expected, value);
        }
    }
}


#[cfg(test)]
mod bigdecimal_tests {
    use BigDecimal;
    use traits::{ToPrimitive, FromPrimitive};
    use std::str::FromStr;
    use num;

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
            ("-128", ::std::i8::MIN),
            ("127", ::std::i8::MAX),
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
            ("1.0", 1.0),
            ("0.5", 0.5),
            ("0.25", 0.25),
            ("50.", 50.0),
            ("50000", 50000.),
            ("0.001", 0.001),
            ("12.34", 12.34),
            ("0.15625", 5.0 * 0.03125),
            ("3.141593", ::std::f32::consts::PI),
            ("31415.93", ::std::f32::consts::PI * 10000.0),
            ("94247.78", ::std::f32::consts::PI * 30000.0),
            // ("3.14159265358979323846264338327950288f32", ::std::f32::consts::PI),

        ];
        for (s, n) in vals {
            let expected = BigDecimal::from_str(s).unwrap();
            let value = BigDecimal::from_f32(n).unwrap();
            assert_eq!(expected, value);
            // assert_eq!(expected, n);
        }

    }
    #[test]
    fn test_from_f64() {
        let vals = vec![
            ("1.0", 1.0f64),
            ("0.5", 0.5),
            ("50", 50.),
            ("50000", 50000.),
            ("1e-3", 0.001),
            ("0.25", 0.25),
            ("12.34", 12.34),
            // ("12.3399999999999999", 12.34), // <- Precision 16 decimal points
            ("0.15625", 5.0 * 0.03125),
            ("0.3333333333333333", 1.0 / 3.0),
            ("3.141592653589793", ::std::f64::consts::PI),
            ("31415.92653589793", ::std::f64::consts::PI * 10000.0f64),
            ("94247.77960769380", ::std::f64::consts::PI * 30000.0f64),
        ];
        for (s, n) in vals {
            let expected = BigDecimal::from_str(s).unwrap();
            let value = BigDecimal::from_f64(n).unwrap();
            assert_eq!(expected, value);
            // assert_eq!(expected, n);
        }
    }

    #[test]
    fn test_add() {
        let vals = vec![
            ("12.34", "1.234", "13.574"),
            ("12.34", "-1.234", "11.106"),
            ("1234e6", "1234e-6", "1234000000.001234"),
            ("1234e-6", "1234e6", "1234000000.001234"),
            ("18446744073709551616.0", "1", "18446744073709551617"),
            ("184467440737e3380", "0", "184467440737e3380"),
        ];

        for &(x, y, z) in vals.iter() {

            let mut a = BigDecimal::from_str(x).unwrap();
            let b = BigDecimal::from_str(y).unwrap();
            let c = BigDecimal::from_str(z).unwrap();

            let s = a.clone() + b.clone();
            assert_eq!(s, c);

            a += b;
            assert_eq!(a, c);
        }
    }

    #[test]
    fn test_sub() {
        let vals = vec![
            ("12.34", "1.234", "11.106"),
            ("12.34", "-1.234", "13.574"),
            ("1234e6", "1234e-6", "1233999999.998766"),
        ];

        for &(x, y, z) in vals.iter() {

            let mut a = BigDecimal::from_str(x).unwrap();
            let b = BigDecimal::from_str(y).unwrap();
            let c = BigDecimal::from_str(z).unwrap();

            let d = a.clone() - b.clone();
            assert_eq!(d, c);

            a -= b;
            assert_eq!(a, c);
        }
    }

    #[test]
    fn test_mul() {

        let vals = vec![
            ("2", "1", "2"),
            ("12.34", "1.234", "15.22756"),
            ("2e1", "1", "20"),
            ("3", ".333333", "0.999999"),
            ("2389472934723", "209481029831", "500549251119075878721813"),
            ("1e-450", "1e500", ".1e51"),
        ];

        for &(x, y, z) in vals.iter() {

            let mut a = BigDecimal::from_str(x).unwrap();
            let b = BigDecimal::from_str(y).unwrap();
            let c = BigDecimal::from_str(z).unwrap();

            let p = a.clone() * b.clone();
            assert_eq!(p, c);

            a *= b;
            assert_eq!(a, c);
        }
    }

    #[cfg_attr(rustfmt, rustfmt_skip)]
    #[test]
    fn test_div() {
        let vals = vec![
            ("2", "1", "2"),
            ("2e1", "1", "20"),
            ("1", "2", "0.5"),
            ("1", "2e-2", "5e1"),
            ("5", "4", "1.25"),
            ("5", "4", "125e-2"),
            ("100", "5", "20"),
            ("-50", "5", "-10"),
            ("200", "5", "40."),
            ("1", "3", ".3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333"),
            ("12.34", "1.233", "10.008110300081103000811030008110300081103000811030008110300081103000811030008110300081103000811030008"),
        ];

        for &(x, y, z) in vals.iter() {

            let a = BigDecimal::from_str(x).unwrap();
            let b = BigDecimal::from_str(y).unwrap();
            let c = BigDecimal::from_str(z).unwrap();

            let q = a / b;
            assert_eq!(q, c)
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

    #[cfg_attr(rustfmt, rustfmt_skip)]
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
        use std::hash::{Hash, Hasher};
        use std::collections::hash_map::DefaultHasher;

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
        use std::hash::{Hash, Hasher};
        use std::collections::hash_map::DefaultHasher;

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
        use std::hash::{Hash, Hasher};
        use std::collections::hash_map::DefaultHasher;

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

    #[cfg_attr(rustfmy, rustfmt_skip)]
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
        ];

        for &(source, val, scale) in vals.iter() {
            let x = BigDecimal::from_str(source).unwrap();
            assert_eq!(x.int_val.to_i32().unwrap(), val);
            assert_eq!(x.scale, scale);
        }
    }

    #[cfg_attr(rustfmt, rustfmt_skip)]
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
            let x = BigDecimal::new(num::BigInt::from(i), scale);
            assert_eq!(format!("{}", x), results.0);
            assert_eq!(format!("{:.1}", x), results.1);
            assert_eq!(format!("{:.4}", x), results.2);
            assert_eq!(format!("{:4.1}", x), results.3);
            assert_eq!(format!("{:+05.1}", x), results.4);
            assert_eq!(format!("{:<4.1}", x), results.5);
        }
    }

    #[test]
    fn test_signed() {
        use traits::{One, Signed, Zero};
        assert!(!BigDecimal::zero().is_positive());
        assert!(!BigDecimal::one().is_negative());

        assert!(BigDecimal::one().is_positive());
        assert!((-BigDecimal::one()).is_negative());
        assert!((-BigDecimal::one()).abs().is_positive());
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
}
