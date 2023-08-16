//! Implementation of std::fmt & other stringification functions
//!
//! BigDecimals have a potential to take up a lot of space.
//!

use stdlib::fmt;
use stdlib::fmt::Write;
use stdlib::string::{String, ToString};

use crate::{BigDecimal, Sign};

use num_traits::Zero;


/// test case builder for mapping decimal-string to formatted-string
/// define test_fmt_function! macro to test your function
#[cfg(test)]
macro_rules! impl_case {
    ($name:ident : $in:literal => $ex:literal) => {
        #[test]
        fn $name() {
            let n: BigDecimal = $in.parse().unwrap();
            let s = test_fmt_function!(n);
            assert_eq!(&s, $ex);
        }
    };
}


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
            i => i as usize,
        };

        let exp = top_digit_exponent - shift_amount as i128;

        // handle adding zero padding
        if let Some(padding_zero_count) = shift_amount.checked_sub(dec_str.len()) {
            let zeros = &"000"[..padding_zero_count];
            out.write_str(&dec_str)?;
            out.write_str(zeros)?;
            return write!(out, "e{}", exp);
        }

        let (head, rest) = dec_str.split_at(shift_amount);
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

    macro_rules! test_fmt_function {
        ($n:expr) => { $n.to_scientific_notation() };
    }

    impl_case!(case_4_1592480782835e9 : "4159248078.2835" => "4.1592480782835e9");
    impl_case!(case_1_234e_5 : "0.00001234" => "1.234e-5");
    impl_case!(case_0 : "0" => "0e0");
    impl_case!(case_1 : "1" => "1e0");
    impl_case!(case_2_00e0 : "2.00" => "2.00e0");
    impl_case!(case_neg_5_70e1 : "-57.0" => "-5.70e1");
}

#[cfg(test)]
mod test_write_engineering_notation {
    use super::*;

    macro_rules! test_fmt_function {
        ($n:expr) => { $n.to_engineering_notation() };
    }

    impl_case!(case_4_1592480782835e9 : "4159248078.2835" => "4.1592480782835e9");
    impl_case!(case_12_34e_6 : "0.00001234" => "12.34e-6");
    impl_case!(case_0 : "0" => "0e0");
    impl_case!(case_1 : "1" => "1e0");
    impl_case!(case_2_00e0 : "2.00" => "2.00e0");
    impl_case!(case_neg_5_70e1 : "-57.0" => "-57.0e0");
    impl_case!(case_5_31e4 : "5.31e4" => "53.1e3");
    impl_case!(case_5_31e5 : "5.31e5" => "531e3");
    impl_case!(case_5_31e6 : "5.31e6" => "5.31e6");
    impl_case!(case_5_31e7 : "5.31e7" => "53.1e6");

    impl_case!(case_4e99999999999999 : "4e99999999999999" => "4e99999999999999");
    impl_case!(case_4e99999999999998 : "4e99999999999998" => "400e99999999999996");
    impl_case!(case_44e99999999999998 : "44e99999999999998" => "4.4e99999999999999");
    impl_case!(case_4e99999999999997 : "4e99999999999997" => "40e99999999999996");
    impl_case!(case_41e99999999999997 : "41e99999999999997" => "410e99999999999996");
    impl_case!(case_413e99999999999997 : "413e99999999999997" => "4.13e99999999999999");
    // impl_case!(case_413e99999999999997 : "413e99999999999997" => "4.13e99999999999999");

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

    macro_rules! test_fmt_function {
        ($n:expr) => { format!("{:?}", $n) };
    }

    impl_case!(case_0: "0" => r#"BigDecimal("0")"#);
    impl_case!(case_1: "1" => r#"BigDecimal("1")"#);
    impl_case!(case_123_400: "123.400" => r#"BigDecimal("123.400")"#);
    impl_case!(case_123_456: "123.456" => r#"BigDecimal("123.456")"#);
    impl_case!(case_01_20: "01.20" => r#"BigDecimal("1.20")"#);
    impl_case!(case_1_20: "1.20" => r#"BigDecimal("1.20")"#);
    impl_case!(case_01_2e3: "01.2E3" => r#"BigDecimal("1200")"#);
    impl_case!(case_avagadro: "6.02214076e1023" => r#"BigDecimal("602214076e1015")"#);

    impl_case!(case_1e99999999999999 : "1e99999999999999" => r#"BigDecimal("1e99999999999999")"#);
}


impl fmt::Display for BigDecimal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Acquire the absolute integer as a decimal string
        let mut abs_int = self.int_val.magnitude().to_str_radix(10);

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
