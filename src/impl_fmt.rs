//! Implementation of std::fmt traits & other stringification functions
//!

use crate::*;
use stdlib::fmt::Write;


impl fmt::Display for BigDecimal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        const EXPONENTIAL_FORMAT_THRESHOLD: i64 = 25;

        // Acquire the absolute integer as a decimal string
        let abs_int = self.int_val.magnitude().to_str_radix(10);

        if (abs_int.len() as i64 - self.scale - 1).abs() > EXPONENTIAL_FORMAT_THRESHOLD {
            format_exponential(self, f, abs_int)
        } else {
            format_full_scale(self, f, abs_int)
        }
    }
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


fn format_full_scale(
    this: &BigDecimal,
    f: &mut fmt::Formatter,
    mut abs_int: String,
) -> fmt::Result {
    // Split the representation at the decimal point
    let (before, after) = if this.scale >= abs_int.len() as i64 {
        // First case: the integer representation falls
        // completely behind the decimal point
        let scale = this.scale as usize;
        let after = "0".repeat(scale - abs_int.len()) + abs_int.as_str();
        ("0".to_string(), after)
    } else {
        // Second case: the integer representation falls
        // around, or before the decimal point
        let location = abs_int.len() as i64 - this.scale;
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

    let non_negative = matches!(this.int_val.sign(), Sign::Plus | Sign::NoSign);
    //pad_integral does the right thing although we have a decimal
    f.pad_integral(non_negative, "", &complete_without_sign)
}


fn format_exponential(
    this: &BigDecimal,
    f: &mut fmt::Formatter,
    mut abs_int: String,
) -> fmt::Result {
    // Steps:
    //  1. Truncate integer based on precision
    //  2. calculate exponent from the scale and the length of the internal integer
    //  3. Place decimal point after a single digit of the number, or omit if there is only a single digit
    //  4. Append `E{exponent}` and format the resulting string based on some `Formatter` flags

    if abs_int.len() > 1 {
        // only modify for precision if there is more than 1 decimal digit
        if let Some(precision) = f.precision() {
            // add 1 precision to consider first digit
            // TODO: Should we round?
            abs_int.truncate(precision + 1);
        }
    }

    // Determine the exponent value based on the scale
    //
    // # First case: the integer representation falls completely behind the
    //   decimal point.
    //
    //   Example of this.scale > abs_int.len():
    //   0.000001234509876
    //   abs_int.len() = 10
    //   scale = 15
    //   target is 1.234509876
    //   exponent = -6
    //
    //   Example of this.scale == abs_int.len():
    //   0.333333333333333314829616256247390992939472198486328125
    //   abs_int.len() = 54
    //   scale = 54
    //   target is 3.33333333333333314829616256247390992939472198486328125
    //   exponent = -1
    //
    // # Second case: the integer representation falls around, or before the
    //   decimal point
    //
    //   ## Case 2.1, entirely before the decimal point.
    //     Example of (abs_int.len() - this.scale) > abs_int.len():
    //     123450987600000
    //     abs_int.len() = 10
    //     scale = -5
    //     location = 15
    //     target is 1.234509876
    //     exponent = 14
    //
    //   ## Case 2.2, somewhere around the decimal point.
    //     Example of (abs_int.len() - this.scale) < abs_int.len():
    //     12.339999999999999857891452847979962825775146484375
    //     abs_int.len() = 50
    //     scale = 48
    //     target is 1.2339999999999999857891452847979962825775146484375
    //     exponent = 1
    //
    //     For the (abs_int.len() - this.scale) == abs_int.len() I couldn't
    //     come up with an example
    let exponent = abs_int.len() as i64 - this.scale - 1;

    if abs_int.len() > 1 {
        // only add decimal point if there is more than 1 decimal digit
        abs_int.insert(1, '.');
    }

    if exponent != 0 {
        abs_int += "E";
        abs_int += &exponent.to_string();
    }

    let non_negative = matches!(this.int_val.sign(), Sign::Plus | Sign::NoSign);
    //pad_integral does the right thing although we have a decimal
    f.pad_integral(non_negative, "", &abs_int)
}


#[inline(never)]
pub(crate) fn write_scientific_notation<W: Write>(n: &BigDecimal, w: &mut W) -> fmt::Result {
    if n.is_zero() {
        return w.write_str("0e0");
    }

    if n.int_val.sign() == Sign::Minus {
        w.write_str("-")?;
    }

    let digits = n.int_val.magnitude();

    let dec_str = digits.to_str_radix(10);
    let (first_digit, remaining_digits) = dec_str.as_str().split_at(1);
    w.write_str(first_digit)?;
    if !remaining_digits.is_empty() {
        w.write_str(".")?;
        w.write_str(remaining_digits)?;
    }
    write!(w, "e{}", remaining_digits.len() as i64 - n.scale)
}


#[inline(never)]
pub(crate) fn write_engineering_notation<W: Write>(n: &BigDecimal, out: &mut W) -> fmt::Result {
    if n.is_zero() {
        return out.write_str("0e0");
    }

    if n.int_val.sign() == Sign::Minus {
        out.write_char('-')?;
    }

    let digits = n.int_val.magnitude();

    let dec_str = digits.to_str_radix(10);
    let digit_count = dec_str.len();

    let top_digit_exponent = digit_count as i128 - n.scale as i128;

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


#[cfg(test)]
mod test {
    use super::*;

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
    fn test_fmt_with_large_values() {
        let vals = vec![
            // b  s   ( {}        {:.1}     {:.4}      {:4.1}  {:+05.1}  {:<4.1}
            // Numbers with large scales
            (1, 10_000, ("1E-10000", "1E-10000", "1E-10000", "1E-10000", "+1E-10000", "1E-10000")),
            (1, -10_000, ("1E10000", "1E10000", "1E10000", "1E10000", "+1E10000", "1E10000")),
            // Numbers with many digits
            (1234506789, 5, (
                "12345.06789",
                "12345.0",
                "12345.0678",
                "12345.0",
                "+12345.0",
                "12345.0"
            )),
            (1234506789, -5, (
                "123450678900000",
                "123450678900000.0",
                "123450678900000.0000",
                "123450678900000.0",
                "+123450678900000.0",
                "123450678900000.0"
            )),
        ];
        for (i, scale, results) in vals {
            let x = BigDecimal::new(num_bigint::BigInt::from(i), scale);
            assert_eq!(format!("{}", x), results.0, "digits={i} scale={scale}");
            assert_eq!(format!("{:.1}", x), results.1, "digits={i} scale={scale}");
            assert_eq!(format!("{:.4}", x), results.2, "digits={i} scale={scale}");
            assert_eq!(format!("{:4.1}", x), results.3, "digits={i} scale={scale}");
            assert_eq!(format!("{:+05.1}", x), results.4, "digits={i} scale={scale}");
            assert_eq!(format!("{:<4.1}", x), results.5, "digits={i} scale={scale}");
        }
    }

    mod fmt_debug {
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

    mod write_scientific_notation {
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

    mod write_engineering_notation {
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

        impl_case!(case_1e2 : "1e2" => "100e0");
        impl_case!(case_1e119 : "1e19" => "10e18");
        impl_case!(case_1e3000 : "1e3000" => "1e3000");
        impl_case!(case_4_2e7 : "4.2e7" => "42e6");
        impl_case!(case_4_2e8 : "4.2e8" => "420e6");

        impl_case!(case_4e99999999999999 : "4e99999999999999" => "4e99999999999999");
        impl_case!(case_4e99999999999998 : "4e99999999999998" => "400e99999999999996");
        impl_case!(case_44e99999999999998 : "44e99999999999998" => "4.4e99999999999999");
        impl_case!(case_4e99999999999997 : "4e99999999999997" => "40e99999999999996");
        impl_case!(case_41e99999999999997 : "41e99999999999997" => "410e99999999999996");
        impl_case!(case_413e99999999999997 : "413e99999999999997" => "4.13e99999999999999");
        // impl_case!(case_413e99999999999997 : "413e99999999999997" => "4.13e99999999999999");
    }
}


#[cfg(all(test, property_tests))]
mod proptests {
    use super::*;
    use paste::paste;
    use proptest::*;

    macro_rules! impl_parsing_test {
        ($t:ty) => {
            paste! { proptest! {
                #[test]
                fn [< roudtrip_to_str_and_back_ $t >](n: $t) {
                    let original = BigDecimal::from(n);
                    let display = format!("{}", original);
                    let parsed = display.parse::<BigDecimal>().unwrap();

                    prop_assert_eq!(&original, &parsed);
                }
            } }
        };
        (from-float $t:ty) => {
            paste! { proptest! {
                #[test]
                fn [< roudtrip_to_str_and_back_ $t >](n: $t) {
                    let original = BigDecimal::try_from(n).unwrap();
                    let display = format!("{}", original);
                    let parsed = display.parse::<BigDecimal>().unwrap();

                    prop_assert_eq!(&original, &parsed);
                }
            } }
        };
    }

    impl_parsing_test!(u8);
    impl_parsing_test!(u16);
    impl_parsing_test!(u32);
    impl_parsing_test!(u64);
    impl_parsing_test!(u128);

    impl_parsing_test!(i8);
    impl_parsing_test!(i16);
    impl_parsing_test!(i32);
    impl_parsing_test!(i64);
    impl_parsing_test!(i128);

    impl_parsing_test!(from-float f32);
    impl_parsing_test!(from-float f64);
}
