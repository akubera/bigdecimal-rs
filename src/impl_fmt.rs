//! Implementation of std::fmt traits & other stringification functions
//!

use crate::*;
use stdlib::fmt::Write;


// const EXPONENTIAL_FORMAT_THRESHOLD: i64 = ${RUST_BIGDECIMAL_EXPONENTIAL_FORMAT_THRESHOLD} or 5;
include!(concat!(env!("OUT_DIR"), "/exponential_format_threshold.rs"));


impl fmt::Display for BigDecimal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        dynamically_format_decimal(self.to_ref(), f, EXPONENTIAL_FORMAT_THRESHOLD)
    }
}

impl fmt::Display for BigDecimalRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        dynamically_format_decimal(*self, f, EXPONENTIAL_FORMAT_THRESHOLD)
    }
}


impl fmt::LowerExp for BigDecimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::LowerExp::fmt(&self.to_ref(), f)
    }
}

impl fmt::LowerExp for BigDecimalRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let abs_int = self.digits.to_str_radix(10);
        format_exponential(*self, f, abs_int, "e")
    }
}


impl fmt::UpperExp for BigDecimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::UpperExp::fmt(&self.to_ref(), f)
    }
}

impl fmt::UpperExp for BigDecimalRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let abs_int = self.digits.to_str_radix(10);
        format_exponential(*self, f, abs_int, "E")
    }
}


impl fmt::Debug for BigDecimal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if f.alternate() {
            write!(f, "BigDecimal(\"{}e{:}\")", self.int_val, -self.scale)
        } else {
            write!(f,
                "BigDecimal(sign={:?}, scale={}, digits={:?})",
                self.sign(), self.scale, self.int_val.magnitude().to_u64_digits()
            )
        }
    }
}


fn dynamically_format_decimal(
    this: BigDecimalRef,
    f: &mut fmt::Formatter,
    threshold: i64,
) -> fmt::Result {
    // Acquire the absolute integer as a decimal string
    let abs_int = this.digits.to_str_radix(10);

    // use exponential form if decimal point is not "within" the number.
    // "threshold" is max number of leading zeros before being considered
    // "outside" the number
    if this.scale < 0 || (this.scale > abs_int.len() as i64 + threshold) {
        format_exponential(this, f, abs_int, "E")
    } else {
        format_full_scale(this, f, abs_int)
    }
}


fn format_full_scale(
    this: BigDecimalRef,
    f: &mut fmt::Formatter,
    abs_int: String,
) -> fmt::Result {
    use stdlib::cmp::Ordering::*;

    let mut digits = abs_int.into_bytes();
    let mut exp = -this.scale;
    let non_negative = matches!(this.sign, Sign::Plus | Sign::NoSign);

    debug_assert_ne!(digits.len(), 0);

    match f.precision() {
        // precision limits the number of digits - we have to round
        Some(prec) if prec < digits.len() && 1 < digits.len() => {
            apply_rounding_to_ascii_digits(&mut digits, &mut exp, prec, this.sign);
            debug_assert_eq!(digits.len(), prec);
        },
        _ => {
            // not limited by precision
        }
    };

    // add the decimal point to 'digits' buffer
    match exp.cmp(&0) {
        // do not add decimal point for "full" integer
        Equal => {
        }

        // never decimal point if only one digit long
        Greater if digits.len() == 1 => {
        }

        // we format with scientific notation if exponent is positive
        Greater => {
            debug_assert!(digits.len() > 1);

            // increase exp by len(digits)-1 (eg [ddddd]E+{exp} => [d.dddd]E+{exp+4})
            exp += digits.len() as i64 - 1;

            // push decimal point and rotate it to index '1'
            digits.push(b'.');
            digits[1..].rotate_right(1);
        }

        // decimal point is within the digits   (ddd.ddddddd)
        Less if (-exp as usize) < digits.len() => {
            let digits_to_shift = digits.len() - exp.abs() as usize;
            digits.push(b'.');
            digits[digits_to_shift..].rotate_right(1);

            // exp = 0 means exponential-part will be ignored in output
            exp = 0;
        }

        // decimal point is to the left of digits (0.0000dddddddd)
        Less => {
            let digits_to_shift = exp.abs() as usize - digits.len();

            digits.push(b'0');
            digits.push(b'.');
            digits.extend(stdlib::iter::repeat(b'0').take(digits_to_shift));
            digits.rotate_right(digits_to_shift + 2);

            exp = 0;
        }
    }

    // move digits back into String form
    let mut buf = String::from_utf8(digits).unwrap();

    // add exp part to buffer (if not zero)
    if exp != 0 {
        write!(buf, "E{:+}", exp)?;
    }

    // write buffer to formatter
    f.pad_integral(non_negative, "", &buf)
}


fn format_exponential(
    this: BigDecimalRef,
    f: &mut fmt::Formatter,
    abs_int: String,
    e_symbol: &str,
) -> fmt::Result {
    // Steps:
    //  1. Truncate integer based on precision
    //  2. calculate exponent from the scale and the length of the internal integer
    //  3. Place decimal point after a single digit of the number, or omit if there is only a single digit
    //  4. Append `E{exponent}` and format the resulting string based on some `Formatter` flags

    let mut exp = -this.scale;
    let mut digits = abs_int.into_bytes();

    if digits.len() > 1 {
        // only modify for precision if there is more than 1 decimal digit
        if let Some(prec) = f.precision() {
            apply_rounding_to_ascii_digits(&mut digits, &mut exp, prec, this.sign);
        }
    }

    let mut abs_int = String::from_utf8(digits).unwrap();

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
    let exponent = abs_int.len() as i128 + exp as i128 - 1;

    if abs_int.len() > 1 {
        // only add decimal point if there is more than 1 decimal digit
        abs_int.insert(1, '.');
    }

    if exponent != 0 {
        write!(abs_int, "{}{:+}", e_symbol, exponent)?;
    }

    let non_negative = matches!(this.sign(), Sign::Plus | Sign::NoSign);
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


/// Round big-endian digits in ascii
fn apply_rounding_to_ascii_digits(ascii_digits: &mut Vec<u8>, exp: &mut i64, prec: usize, sign: Sign) {
    if ascii_digits.len() < prec {
        return;
    }

    // shift exp to align with new length of digits
    *exp += (ascii_digits.len() - prec) as i64;

    // true if all ascii_digits after precision are zeros
    let trailing_zeros = ascii_digits[prec + 1..].iter().all(|&d| d == b'0');

    let sig_digit = ascii_digits[prec - 1] - b'0';
    let insig_digit = ascii_digits[prec] - b'0';
    let rounded_digit = Context::default().round_pair(sign, sig_digit, insig_digit, trailing_zeros);

    // remove insignificant digits
    ascii_digits.truncate(prec - 1);

    // push rounded value
    if rounded_digit < 10 {
        ascii_digits.push(rounded_digit + b'0');
        return
    }

    debug_assert_eq!(rounded_digit, 10);

    // push zero and carry-the-one
    ascii_digits.push(b'0');

    // loop through digits in reverse order (skip the 0 we just pushed)
    let digits = ascii_digits.iter_mut().rev().skip(1);
    for digit in digits {
        if *digit < b'9' {
            // we've carried the one as far as it will go
            *digit += 1;
            return;
        }

        debug_assert_eq!(*digit, b'9');

        // digit was a 9, set to zero and carry the one
        // to the next digit
        *digit = b'0';
    }

    // at this point all digits have become zero
    // just set significant digit to 1 and increase exponent
    //
    // eg: 9999e2 ~> 0000e2 ~> 1000e3
    //
    ascii_digits[0] = b'1';
    *exp += 1;
}


#[cfg(test)]
mod test {
    use super::*;
    use paste::*;

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

    /// "Mock" Formatter
    ///
    /// Given callable, forwards formatter to callable.
    /// Required work-around due to lack of constructor in fmt::Formatter
    ///
    struct Fmt<F>(F)
        where F: Fn(&mut fmt::Formatter) -> fmt::Result;

    impl<F> fmt::Display for Fmt<F>
        where F: Fn(&mut fmt::Formatter) -> fmt::Result
    {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            // call closure with given formatter
            (self.0)(f)
        }
    }

    impl<F> fmt::Debug for Fmt<F>
        where F: Fn(&mut fmt::Formatter) -> fmt::Result
    {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            (self.0)(f)
        }
    }

    mod dynamic_fmt {
        use super::*;

        macro_rules! test_fmt_function {
            ($n:ident) => {{
                format!("{}", Fmt(|f| dynamically_format_decimal($n.to_ref(), f, 2)))
            }};
        }

        impl_case!(case_0d123: "0.123" => "0.123");
        impl_case!(case_0d0123: "0.0123" => "0.0123");
        impl_case!(case_0d00123: "0.00123" => "0.00123");
        impl_case!(case_0d000123: "0.000123" => "1.23E-4");

        impl_case!(case_123d: "123." => "123");
        impl_case!(case_123de1: "123.e1" => "1.23E+3");
    }

    mod fmt_options {
        use super::*;

        macro_rules! impl_case {
            ($name:ident: $fmt:literal => $expected:literal) => {
                #[test]
                fn $name() {
                    let x = test_input();
                    let y = format!($fmt, x);
                    assert_eq!(y, $expected);
                }
            };
        }

        mod dec_1 {
            use super::*;

            fn test_input() -> BigDecimal {
                "1".parse().unwrap()
            }

            impl_case!(fmt_default:      "{}" => "1");
            impl_case!(fmt_d1:        "{:.1}" => "1");
            impl_case!(fmt_d4:        "{:.4}" => "1");
            impl_case!(fmt_4d1:      "{:4.1}" => "   1");
            impl_case!(fmt_r4d1:    "{:>4.1}" => "   1");
            impl_case!(fmt_l4d1:    "{:<4.1}" => "1   ");
            impl_case!(fmt_p05d1:  "{:+05.1}" => "+0001");
        }

        mod dec_123456 {
            use super::*;

            fn test_input() -> BigDecimal {
                "123456".parse().unwrap()
            }

            impl_case!(fmt_default:      "{}" => "123456");
            impl_case!(fmt_p05d1:  "{:+05.1}" => "+1E+5");
            impl_case!(fmt_d1:        "{:.1}" => "1E+5");
            impl_case!(fmt_d4:        "{:.4}" => "1.235E+5");
            impl_case!(fmt_4d1:      "{:4.1}" => "1E+5");
            impl_case!(fmt_r4d3:    "{:>4.3}" => "1.23E+5");
            impl_case!(fmt_r4d4:    "{:>4.4}" => "1.235E+5");
            impl_case!(fmt_l4d1:    "{:<4.1}" => "1E+5");
        }

        mod dec_9999999 {
            use super::*;

            fn test_input() -> BigDecimal {
                "9999999".parse().unwrap()
            }

            impl_case!(fmt_d4:  "{:.4}" => "1.000E+7");
            impl_case!(fmt_d8:  "{:.8}" => "9999999");
        }

        mod dec_19073d97235939614856 {
            use super::*;

            fn test_input() -> BigDecimal {
                "19073.97235939614856".parse().unwrap()
            }

            impl_case!(fmt_default:      "{}" => "19073.97235939614856");
            impl_case!(fmt_p05d7:  "{:+05.7}" => "+19073.97");
            impl_case!(fmt_d3:        "{:.3}" => "1.91E+4");
            impl_case!(fmt_0d4:      "{:0.4}" => "1.907E+4");
            impl_case!(fmt_4d1:      "{:4.1}" => "2E+4");
            impl_case!(fmt_r8d3:    "{:>8.3}" => " 1.91E+4");
            impl_case!(fmt_r8d4:    "{:>8.4}" => "1.907E+4");
            impl_case!(fmt_l8d1:    "{:<8.1}" => "2E+4    ");
        }

        mod dec_491326en12 {
            use super::*;

            fn test_input() -> BigDecimal {
                "491326e-12".parse().unwrap()
            }

            impl_case!(fmt_default:        "{}" => "4.91326E-7");
            impl_case!(fmt_p015d7:  "{:+015.7}" => "+00004.91326E-7");
            impl_case!(fmt_d3:          "{:.3}" => "4.91E-7");
            impl_case!(fmt_0d4:        "{:0.4}" => "4.913E-7");
            impl_case!(fmt_4d1:        "{:4.1}" => "5E-7");
            impl_case!(fmt_r8d3:      "{:>8.3}" => " 4.91E-7");
            impl_case!(fmt_r8d4:      "{:>8.4}" => "4.913E-7");
            impl_case!(fmt_l8d1:      "{:<8.1}" => "5E-7    ");
        }
    }

    #[test]
    fn test_fmt() {
        let vals = vec![
            // b  s   (   {}     {:.1}     {:.4}    {:4.1}   {:+05.7}     {:<6.4}
            (1, 0,  (    "1",      "1",      "1",   "   1",   "+0001",   "1     " )),
            (1, 1,  (  "0.1",    "0.1",    "0.1",   " 0.1",   "+00.1",   "0.1   " )),
            (1, 2,  ( "0.01",   "0.01",   "0.01",   "0.01",   "+0.01",   "0.01  " )),
            (1, -2, ( "1E+2",   "1E+2",   "1E+2",   "1E+2",   "+1E+2",   "1E+2  " )),
            (-1, 0, (   "-1",     "-1",     "-1",   "  -1",   "-0001",   "-1    " )),
            (-1, 1, ( "-0.1",   "-0.1",   "-0.1",   "-0.1",   "-00.1",   "-0.1  " )),
            (-1, 2, ("-0.01",  "-0.01",  "-0.01",  "-0.01",   "-0.01",   "-0.01 " )),
        ];
        for (i, scale, results) in vals {
            let x = BigDecimal::new(num_bigint::BigInt::from(i), scale);
            assert_eq!(format!("{}", x), results.0);
            assert_eq!(format!("{:.1}", x), results.1);
            assert_eq!(format!("{:.4}", x), results.2);
            assert_eq!(format!("{:4.1}", x), results.3);
            assert_eq!(format!("{:+05.7}", x), results.4);
            assert_eq!(format!("{:<6.4}", x), results.5);
        }
    }

    #[test]
    fn test_fmt_with_large_values() {
        let vals = vec![
            // b  s          (                {}         {:.1}          {:2.4}      {:4.2}           {:+05.7}         {:<13.4}
            // Numbers with large scales
            (1,      10_000, (        "1E-10000",   "1E-10000",     "1E-10000",   "1E-10000",     "+1E-10000", "1E-10000     ")),
            (1,     -10_000, (        "1E+10000",   "1E+10000",     "1E+10000",   "1E+10000",     "+1E+10000", "1E+10000     ")),
            // // Numbers with many digits
            (1234506789,  5, (     "12345.06789",       "1E+4",     "1.235E+4",     "1.2E+4",     "+12345.07", "1.235E+4     ")),
            (1234506789, -5, ( "1.234506789E+14",      "1E+14",    "1.235E+14",    "1.2E+14", "+1.234507E+14", "1.235E+14    ")),
        ];
        for (i, scale, results) in vals {
            let x = BigDecimal::new(num_bigint::BigInt::from(i), scale);
            assert_eq!(format!("{}", x), results.0, "digits={} scale={}", i, scale);
            assert_eq!(format!("{:.1}", x), results.1, "digits={} scale={}", i, scale);
            assert_eq!(format!("{:2.4}", x), results.2, "digits={} scale={}", i, scale);
            assert_eq!(format!("{:4.2}", x), results.3, "digits={} scale={}", i, scale);
            assert_eq!(format!("{:+05.7}", x), results.4, "digits={} scale={}", i, scale);
            assert_eq!(format!("{:<13.4}", x), results.5, "digits={} scale={}", i, scale);
        }
    }

    mod fmt_debug {
        use super::*;

        macro_rules! impl_case {
            ($name:ident: $input:literal => $expected:literal => $expected_alt:literal) => {
                paste! {
                    #[test]
                    fn $name() {
                        let x: BigDecimal = $input.parse().unwrap();
                        let y = format!("{:?}", x);
                        assert_eq!(y, $expected);
                    }

                    #[test]
                    fn [< $name _alt >]() {
                        let x: BigDecimal = $input.parse().unwrap();
                        let y = format!("{:#?}", x);
                        assert_eq!(y, $expected_alt);
                    }
                }
            }
        }

        impl_case!(case_0: "0" => r#"BigDecimal(sign=NoSign, scale=0, digits=[])"#
                               => r#"BigDecimal("0e0")"#);

        impl_case!(case_n0: "-0" => r#"BigDecimal(sign=NoSign, scale=0, digits=[])"#
                               => r#"BigDecimal("0e0")"#);

        impl_case!(case_1: "1" => r#"BigDecimal(sign=Plus, scale=0, digits=[1])"#
                               => r#"BigDecimal("1e0")"#);

        impl_case!(case_123_400: "123.400" => r#"BigDecimal(sign=Plus, scale=3, digits=[123400])"#
                                           => r#"BigDecimal("123400e-3")"#);

        impl_case!(case_123_4en2: "123.4e-2" => r#"BigDecimal(sign=Plus, scale=3, digits=[1234])"#
                                             => r#"BigDecimal("1234e-3")"#);

        impl_case!(case_123_456:   "123.456" => r#"BigDecimal(sign=Plus, scale=3, digits=[123456])"#
                                             => r#"BigDecimal("123456e-3")"#);

        impl_case!(case_01_20:       "01.20" => r#"BigDecimal(sign=Plus, scale=2, digits=[120])"#
                                             => r#"BigDecimal("120e-2")"#);

        impl_case!(case_1_20:         "1.20" => r#"BigDecimal(sign=Plus, scale=2, digits=[120])"#
                                             => r#"BigDecimal("120e-2")"#);
        impl_case!(case_01_2e3:     "01.2E3" => r#"BigDecimal(sign=Plus, scale=-2, digits=[12])"#
                                             => r#"BigDecimal("12e2")"#);

        impl_case!(case_avagadro: "6.02214076e1023" => r#"BigDecimal(sign=Plus, scale=-1015, digits=[602214076])"#
                                                    => r#"BigDecimal("602214076e1015")"#);

        impl_case!(case_1e99999999999999 : "1e99999999999999" => r#"BigDecimal(sign=Plus, scale=-99999999999999, digits=[1])"#
                                                              => r#"BigDecimal("1e99999999999999")"#);

        impl_case!(case_n144d3308279 : "-144.3308279" => r#"BigDecimal(sign=Minus, scale=7, digits=[1443308279])"#
                                                      => r#"BigDecimal("-1443308279e-7")"#);

        impl_case!(case_n349983058835858339619e2 : "-349983058835858339619e2"
                                                      => r#"BigDecimal(sign=Minus, scale=-2, digits=[17941665509086410531, 18])"#
                                                      => r#"BigDecimal("-349983058835858339619e2")"#);
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
    use proptest::prelude::*;

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

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1000))]

        #[test]
        fn scientific_notation_roundtrip(f: f64) {
            prop_assume!(!f.is_nan() && !f.is_infinite());
            let n = BigDecimal::from_f64(f).unwrap();
            let s = n.to_scientific_notation();
            let m: BigDecimal = s.parse().unwrap();
            prop_assert_eq!(n, m);
        }

        #[test]
        fn engineering_notation_roundtrip(f: f64) {
            prop_assume!(!f.is_nan() && !f.is_infinite());
            let n = BigDecimal::from_f64(f).unwrap();
            let s = n.to_engineering_notation();
            let m: BigDecimal = s.parse().unwrap();
            prop_assert_eq!(n, m);
        }
    }
}
