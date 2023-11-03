//! Code for num_traits

use num_traits::{Num, FromPrimitive, ToPrimitive, AsPrimitive};
use num_bigint::{BigInt, Sign, ToBigInt};

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
                let (base, exp) = (&s[..loc], &s[loc + 1..]);

                // special consideration for rust 1.0.0 which would not
                // parse a leading '+'
                let exp = match exp.chars().next() {
                    Some('+') => &exp[1..],
                    _ => exp,
                };

                (base, i64::from_str(exp)?)
            }
        };

        // TEMPORARY: Test for emptiness - remove once BigInt supports similar error
        if base_part.is_empty() {
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

                // count number of trailing digits
                let trail_digits = trail.chars().filter(|c| *c != '_').count();

                (digits, trail_digits as i64)
            }
        };

        let scale = match decimal_offset.checked_sub(exponent_value) {
            Some(scale) => scale,
            None => {
                return Err(ParseBigDecimalError::Other(
                    format!("Exponent overflow when parsing '{}'", s)
                ))
            }
        };

        let big_int = BigInt::from_str_radix(&digits, radix)?;

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
        self.int_val.to_f64().map(|f| {
            // return f * powi(10f64, self.scale.neg().as_());
            if f == 0.0 || self.scale <= 0 {
                return f;
            }

            let mantissa_mask = (1u64 << 52) - 1;
            let exp_mask = (1u64 << 12) - 1;

            let bits = f.to_bits();
            let e = (bits >> 52) & exp_mask;
            let m = (bits & mantissa_mask) | (1 << 52);

            let scale = self.scale as i32;

            // split 53-digit number by div_rem(5**12 = 244140625 ~= 2**26.7)
            let pow = 12;
            let five_to_the_pow = 5u64.pow(pow);
            let (h, l) = num_integer::div_rem(m, five_to_the_pow);

            let a = h as f64 * powi(5f64, (pow as i32 - scale).as_());
            let b = l as f64 * powi(5f64, (-scale).as_());

            let mut result_bits = (a + b).to_bits();

            // multiply by 2^-scale
            let result_exp = (result_bits >> 52) & exp_mask;
            let exp_shift = result_exp as i32 - 1075;
            let new_exp = e as i32 + exp_shift - scale;
            result_bits &= !(exp_mask << 52);
            result_bits |= (new_exp as u64 & exp_mask) << 52;
            result_bits |= (bits >> 63) << 63;

            f64::from_bits(result_bits)
        })
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


#[cfg(test)]
mod test_to_f64 {
    use super::*;
    use crate::stdlib;

    macro_rules! impl_case {
        ($name:ident: $f:expr) => {
            #[test]
            fn $name() {
                let f: f64 = $f;
                let s = format!("{}", f);
                let n = BigDecimal::from_str(&s).unwrap();
                assert_eq!(n.to_f64().unwrap(), f, "src='{}'", s);
            }
        };
    }

    impl_case!(case_875en6: 0.000875);
    impl_case!(case_8712994288722404: 0.8712994288722404);
    impl_case!(case_f64_min: stdlib::f64::MIN);
    impl_case!(case_f64_max: stdlib::f64::MAX);
    impl_case!(case_zero: 0.0);
    impl_case!(case_neg_zero: -0.0);
    impl_case!(case_pi: stdlib::f64::consts::PI);
    impl_case!(case_pi_5: 3.1415);
    impl_case!(case_pi_6: -3.14159);
    impl_case!(case_1en500: 1e-500);
    impl_case!(case_neg1en500: -1e-500);
}
