//! Implementation of std::fmt & other stringification functions
//!
//! BigDecimals have a potential to take up a lot of space.
//!

use stdlib::fmt;
use stdlib::fmt::Write;
use stdlib::string::{String, ToString};

use crate::{BigDecimal, Sign};

use num_traits::Zero;


impl BigDecimal {
    /// Engineering notation is scientific notation with the exponent coerced to a multiple of three
    ///
    /// ```
    /// # use bigdecimal::BigDecimal;
    /// let n = BigDecimal::from(12345678);
    /// assert_eq!(&n.to_engineering_notation(), "12.345678e6");
    /// ```
    ///
    pub fn to_engineering_notation(&self) -> String {
        let mut output = String::new();
        self.write_engineering_notation(&mut output).expect("Could not write to string");
        output
    }

    pub fn write_engineering_notation<W: Write>(&self, out: &mut W) -> fmt::Result {
        if self.is_zero() {
            return out.write_str("0e0");
        }

        if self.int_val.sign() == Sign::Minus {
            out.write_char('-')?;
        }

        let digits = self.int_val.magnitude();

        let dec_str = digits.to_str_radix(10);
        let digit_count = dec_str.len();

        let top_digit_exponent = digit_count as i128 - self.scale as i128;

        let shift_amount = match top_digit_exponent.rem_euclid(3) {
            0 => 3,
            i => i,
        };

        let (head, rest) = dec_str.split_at(shift_amount as usize);
        let exp = top_digit_exponent - shift_amount;
        debug_assert_eq!(exp % 3, 0);

        out.write_str(head)?;

        if !rest.is_empty() {
            out.write_char('.')?;
            out.write_str(rest)?;
        }

        return write!(out, "e{}", exp);
    }

    pub fn to_scientific_notation(&self) -> String {
        let mut output = String::new();
        self.write_scientific_notation(&mut output).expect("Could not write to string");
        output
    }

    pub fn write_scientific_notation<W: Write>(&self, w: &mut W) -> fmt::Result {
        if self.is_zero() {
            return w.write_str("0e0");
        }

        if self.int_val.sign() == Sign::Minus {
            w.write_str("-")?;
        }

        let digits = self.int_val.magnitude();

        let dec_str = digits.to_str_radix(10);
        let (first_digit, remaining_digits) = dec_str.as_str().split_at(1);
        w.write_str(first_digit)?;
        if !remaining_digits.is_empty() {
            w.write_str(".")?;
            w.write_str(remaining_digits)?;
        }
        write!(w, "e{}", remaining_digits.len() as i64 - self.scale)
    }
}

#[cfg(test)]
mod test_write_scientific_notation {
    use super::*;

    include!("impl_fmt.tests.scientific_notation.rs");
}

#[cfg(test)]
mod test_write_engineering_notation {
    use super::*;

    include!("impl_fmt.tests.engineering_notation.rs");
}


impl fmt::Debug for BigDecimal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.scale.abs() < 40 {
            write!(f, "BigDecimal(\"{}\")", self)
        } else {
            write!(f, "BigDecimal(\"{:?}e{}\")", self.int_val, -self.scale)
        }
    }
}


#[cfg(test)]
mod test_debug {
    use super::*;

    macro_rules! impl_case {
        ($name:ident : $s:literal => $expected:literal) => {
            #[test]
            fn $name() {
                let d: BigDecimal = $s.parse().unwrap();
                let s = format!("{:?}", d);
                assert_eq!(s, $expected)
            }
        };
    }

    impl_case!(case_0: "0" => r#"BigDecimal("0")"#);
    impl_case!(case_1: "1" => r#"BigDecimal("1")"#);
    impl_case!(case_123_400: "123.400" => r#"BigDecimal("123.400")"#);
    impl_case!(case_123_456: "123.456" => r#"BigDecimal("123.456")"#);
    impl_case!(case_01_20: "01.20" => r#"BigDecimal("1.20")"#);
    impl_case!(case_1_20: "1.20" => r#"BigDecimal("1.20")"#);
    impl_case!(case_01_2e3: "01.2E3" => r#"BigDecimal("1200")"#);
    impl_case!(case_avagadro: "6.02214076e1023" => r#"BigDecimal("602214076e1015")"#);
}
