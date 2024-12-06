//! Code for num_traits

use num_traits::{Zero, Num, Signed, FromPrimitive, ToPrimitive, AsPrimitive};
use num_bigint::{BigInt, Sign, ToBigInt};

use crate::stdlib;
use stdlib::str::FromStr;
use stdlib::string::{String, ToString};
use stdlib::convert::TryFrom;
use stdlib::ops::Neg;

use crate::BigDecimal;
use crate::ParseBigDecimalError;

#[cfg(not(feature = "std"))]
// f64::powi is only available in std, no_std must use libm
fn powi(x: f64, n: f64) -> f64 {
    libm::pow(x, n)
}

#[cfg(feature = "std")]
fn powi(x: f64, n: i32) -> f64 {
    x.powi(n)
}

impl Num for BigDecimal {
    type FromStrRadixErr = ParseBigDecimalError;

    /// Creates and initializes a BigDecimal.
    #[inline]
    fn from_str_radix(s: &str, radix: u32) -> Result<BigDecimal, ParseBigDecimalError> {
        if radix != 10 {
            return Err(ParseBigDecimalError::Other(String::from(
                "The radix for decimal MUST be 10",
            )));
        }

        let exp_separator: &[_] = &['e', 'E'];

        // split slice into base and exponent parts
        let (base_part, exponent_value) = match s.find(exp_separator) {
            // exponent defaults to 0 if (e|E) not found
            None => (s, 0),

            // split and parse exponent field
            Some(loc) => {
                // slice up to `loc` and 1 after to skip the 'e' char
                let (base, e_exp) = s.split_at(loc);
                (base, i128::from_str(&e_exp[1..])?)
            }
        };

        // TEMPORARY: Test for emptiness - remove once BigInt supports similar error
        if base_part.is_empty() {
            return Err(ParseBigDecimalError::Empty);
        }

        let mut digit_buffer = String::new();

        let last_digit_loc = base_part.len() - 1;

        // split decimal into a digit string and decimal-point offset
        let (digits, decimal_offset) = match base_part.find('.') {
            // No dot! pass directly to BigInt
            None => (base_part, 0),
            // dot at last digit, pass all preceding digits to BigInt
            Some(loc) if loc == last_digit_loc => {
                (&base_part[..last_digit_loc], 0)
            }
            // decimal point found - necessary copy into new string buffer
            Some(loc) => {
                // split into leading and trailing digits
                let (lead, trail) = (&base_part[..loc], &base_part[loc + 1..]);

                digit_buffer.reserve(lead.len() + trail.len());
                // copy all leading characters into 'digits' string
                digit_buffer.push_str(lead);
                // copy all trailing characters after '.' into the digits string
                digit_buffer.push_str(trail);

                // count number of trailing digits
                let trail_digits = trail.chars().filter(|c| *c != '_').count();

                (digit_buffer.as_str(), trail_digits as i128)
            }
        };

        // Calculate scale by subtracing the parsed exponential
        // value from the number of decimal digits.
        // Return error if anything overflows outside i64 boundary.
        let scale = decimal_offset
                    .checked_sub(exponent_value)
                    .and_then(|scale| scale.to_i64())
                    .ok_or_else(||
                        ParseBigDecimalError::Other(
                            format!("Exponent overflow when parsing '{}'", s))
                    )?;

        let big_int = BigInt::from_str_radix(digits, radix)?;

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
    fn to_i128(&self) -> Option<i128> {
        match self.sign() {
            Sign::Minus | Sign::Plus => self.with_scale(0).int_val.to_i128(),
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
    fn to_u128(&self) -> Option<u128> {
        match self.sign() {
            Sign::Plus => self.with_scale(0).int_val.to_u128(),
            Sign::NoSign => Some(0),
            Sign::Minus => None,
        }
    }

    fn to_f64(&self) -> Option<f64> {
        if self.int_val.is_zero() {
            return Some(0.0);
        }
        if self.scale == 0 {
            return self.int_val.to_f64();
        }

        // borrow bigint value
        let (mut int_cow, mut scale) = self.as_bigint_and_scale();

        // approximate number of base-10 digits
        let digit_count = ((int_cow.bits() + 1) as f64 * stdlib::f64::consts::LOG10_2).floor() as u64;
        let digits_to_remove = digit_count.saturating_sub(25);

        let ten_to_19 = 10u64.pow(19);
        let iter_count = digits_to_remove / 19;
        for _ in 0..iter_count {
            *int_cow.to_mut() /= ten_to_19;
            scale -= 19;
        }

        match scale.to_i32().and_then(|x| x.checked_neg()) {
            Some(pow) if -1 < pow  => {
                let f = int_cow.to_f64()?;
                (f * powi(10.0, pow)).into()
            }
            Some(exp) => {
                let s = format!("{}e{}", int_cow, exp);
                s.parse().ok()
            }
            None => {
                let result = if self.is_negative() {
                    stdlib::f64::INFINITY
                } else {
                    stdlib::f64::NEG_INFINITY
                };
                result.into()
            }
        }
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
    fn from_i128(n: i128) -> Option<Self> {
        Some(BigDecimal::from(n))
    }

    #[inline]
    fn from_u128(n: u128) -> Option<Self> {
        Some(BigDecimal::from(n))
    }

    #[inline]
    fn from_f32(n: f32) -> Option<Self> {
        BigDecimal::try_from(n).ok()
    }

    #[inline]
    fn from_f64(n: f64) -> Option<Self> {
        BigDecimal::try_from(n).ok()
    }
}

impl ToBigInt for BigDecimal {
    fn to_bigint(&self) -> Option<BigInt> {
        Some(self.with_scale(0).int_val)
    }
}


#[cfg(test)]
mod test {
    use super::*;

    mod from_str_radix {
        use super::*;

        #[test]
        fn out_of_bounds() {
            let d = BigDecimal::from_str_radix("1e-9223372036854775808", 10);
            assert_eq!(d.unwrap_err(), ParseBigDecimalError::Other("Exponent overflow when parsing '1e-9223372036854775808'".to_string()));

        }
    }
}
