//! Implementation of std::fmt traits & other stringification functions
//!

use crate::*;
use stdlib::fmt::Write;


// const EXPONENTIAL_FORMAT_LEADING_ZERO_THRESHOLD: usize = ${RUST_BIGDECIMAL_FMT_EXPONENTIAL_LOWER_THRESHOLD} or 5;
// const EXPONENTIAL_FORMAT_TRAILING_ZERO_THRESHOLD: usize = ${RUST_BIGDECIMAL_FMT_EXPONENTIAL_UPPER_THRESHOLD} or 15;
// const FMT_MAX_INTEGER_PADDING: usize = = ${RUST_BIGDECIMAL_FMT_MAX_INTEGER_PADDING} or  1000;
include!(concat!(env!("OUT_DIR"), "/exponential_format_threshold.rs"));


impl fmt::Display for BigDecimal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        dynamically_format_decimal(
            self.to_ref(),
            f,
            EXPONENTIAL_FORMAT_LEADING_ZERO_THRESHOLD,
            EXPONENTIAL_FORMAT_TRAILING_ZERO_THRESHOLD,
        )
    }
}

impl fmt::Display for BigDecimalRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        dynamically_format_decimal(
            *self,
            f,
            EXPONENTIAL_FORMAT_LEADING_ZERO_THRESHOLD,
            EXPONENTIAL_FORMAT_TRAILING_ZERO_THRESHOLD,
        )
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
    leading_zero_threshold: usize,
    trailing_zero_threshold: usize,
) -> fmt::Result {
    // Acquire the absolute integer as a decimal string
    let abs_int = this.digits.to_str_radix(10);

    // number of zeros between most significant digit and decimal point
    let leading_zero_count = this.scale
                                 .to_usize()
                                 .and_then(|scale| scale.checked_sub(abs_int.len()))
                                 .unwrap_or(0);

    // number of zeros between least significant digit and decimal point
    let trailing_zero_count = this.scale
                                  .checked_neg()
                                  .and_then(|d| d.to_usize());

    // this ignores scientific-formatting if precision is requested
    let trailing_zeros = f.precision().map(|_| 0)
                          .or(trailing_zero_count)
                          .unwrap_or(0);

    // use exponential form if decimal point is outside
    // the upper and lower thresholds of the decimal
    if leading_zero_threshold < leading_zero_count {
        format_exponential(this, f, abs_int, "E")
    } else if trailing_zero_threshold < trailing_zeros {
        // non-scientific notation
        format_dotless_exponential(f, abs_int, this.sign, this.scale, "e")
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
    let mut exp = (this.scale as i128).neg();
    let non_negative = matches!(this.sign, Sign::Plus | Sign::NoSign);

    debug_assert_ne!(digits.len(), 0);

    if this.scale <= 0 {
        // formating an integer value (add trailing zeros to the right)
        zero_right_pad_integer_ascii_digits(&mut digits, &mut exp, f.precision());
    } else {
        let scale = this.scale as usize;
        // no-precision behaves the same as precision matching scale (i.e. no padding or rounding)
        let prec = f.precision().unwrap_or(scale);

        if scale < digits.len() {
            // format both integer and fractional digits (always 'trim' to precision)
            trim_ascii_digits(&mut digits, scale, prec, &mut exp, this.sign);
        } else {
            // format only fractional digits
            shift_or_trim_fractional_digits(&mut digits, scale, prec, &mut exp, this.sign);
        }
        // never print exp when in this branch
        exp = 0;
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

/// Fill appropriate number of zeros and decimal point into Vec of (ascii/utf-8) digits
///
/// Exponent is set to zero if zeros were added
///
fn zero_right_pad_integer_ascii_digits(
    digits: &mut Vec<u8>,
    exp: &mut i128,
    precision: Option<usize>,
) {
    debug_assert!(*exp >= 0);

    let trailing_zero_count = exp.to_usize().unwrap();
    let total_additional_zeros = trailing_zero_count.saturating_add(precision.unwrap_or(0));
    if total_additional_zeros > FMT_MAX_INTEGER_PADDING {
        return;
    }

    // requested 'prec' digits of precision after decimal point
    match precision {
        None if trailing_zero_count > 20 => {
        }
        None | Some(0) => {
            digits.resize(digits.len() + trailing_zero_count, b'0');
            *exp = 0;
        }
        Some(prec) => {
            digits.resize(digits.len() + trailing_zero_count, b'0');
            digits.push(b'.');
            digits.resize(digits.len() + prec, b'0');
            *exp = 0;
        }
    }
}

/// Fill zeros into utf-8 digits
fn trim_ascii_digits(
    digits: &mut Vec<u8>,
    scale: usize,
    prec: usize,
    exp: &mut i128,
    sign: Sign,
) {
    debug_assert!(scale < digits.len());
    // there are both integer and fractional digits
    let integer_digit_count = digits.len() - scale;

    if prec < scale {
        apply_rounding_to_ascii_digits(
            digits, exp, integer_digit_count + prec, sign
        );
    }

    if prec != 0 {
        digits.insert(integer_digit_count, b'.');
    }

    if scale < prec {
        // precision required beyond scale
        digits.resize(digits.len() + (prec - scale), b'0');
    }
}


fn shift_or_trim_fractional_digits(
    digits: &mut Vec<u8>,
    scale: usize,
    prec: usize,
    exp: &mut i128,
    sign: Sign,
) {
    debug_assert!(scale >= digits.len());
    // there are no integer digits
    let leading_zeros = scale - digits.len();

    match prec.checked_sub(leading_zeros) {
        None => {
            digits.clear();
            digits.push(b'0');
            if prec > 0 {
                digits.push(b'.');
                digits.resize(2 + prec, b'0');
            }
        }
        Some(0) => {
            // precision is at the decimal digit boundary, round one value
            let insig_digit = digits[0] - b'0';
            let trailing_zeros = digits[1..].iter().all(|&d| d == b'0');
            let rounded_value = Context::default().round_pair(sign, 0, insig_digit, trailing_zeros);

            digits.clear();
            if leading_zeros != 0 {
                digits.push(b'0');
                digits.push(b'.');
                digits.resize(1 + leading_zeros, b'0');
            }
            digits.push(rounded_value + b'0');
        }
        Some(digit_prec) => {
            let trailing_zeros = digit_prec.saturating_sub(digits.len());
            if digit_prec < digits.len() {
                apply_rounding_to_ascii_digits(digits, exp, digit_prec, sign);
            }
            digits.extend_from_slice(b"0.");
            digits.resize(digits.len() + leading_zeros, b'0');
            digits.rotate_right(leading_zeros + 2);

            // add any extra trailing zeros
            digits.resize(digits.len() + trailing_zeros, b'0');
        }
    }
}


/// Format integer as {int}e+{exp}
///
/// Slightly different than scientific notation,
///
fn format_dotless_exponential(
    f: &mut fmt::Formatter,
    mut abs_int: String,
    sign: Sign,
    scale: i64,
    e_symbol: &str,
) -> fmt::Result {
    debug_assert!(scale <= 0);

    write!(abs_int, "{}{:+}", e_symbol, -scale).unwrap();
    let non_negative = matches!(sign, Sign::Plus | Sign::NoSign);
    f.pad_integral(non_negative, "", &abs_int)
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

    let exp = (this.scale as i128).neg();
    let digits = abs_int.into_bytes();

    format_exponential_bigendian_ascii_digits(
        digits, this.sign, exp, f, e_symbol
    )
}


fn format_exponential_bigendian_ascii_digits(
    mut digits: Vec<u8>,
    sign: Sign,
    mut exp: i128,
    f: &mut fmt::Formatter,
    e_symbol: &str,
) -> fmt::Result {
    // how many zeros to pad at the end of the decimal
    let mut extra_trailing_zero_count = 0;

    if let Some(prec) = f.precision() {
        // 'prec' is number of digits after the decimal point
        let total_prec = prec + 1;
        let digit_count = digits.len();

        match total_prec.cmp(&digit_count) {
            Ordering::Equal => {
                // digit count is one more than precision - do nothing
            }
            Ordering::Less => {
                // round to smaller precision
                apply_rounding_to_ascii_digits(&mut digits, &mut exp, total_prec, sign);
            }
            Ordering::Greater => {
                // increase number of zeros to add to end of digits
                extra_trailing_zero_count = total_prec - digit_count;
            }
        }
    }

    let needs_decimal_point = digits.len() > 1 || extra_trailing_zero_count > 0;

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
    let exponent = abs_int.len() as i128 + exp - 1;

    if needs_decimal_point {
        // only add decimal point if there is more than 1 decimal digit
        abs_int.insert(1, '.');
    }

    if extra_trailing_zero_count > 0 {
        abs_int.extend(stdlib::iter::repeat('0').take(extra_trailing_zero_count));
    }

    // always print exponent in exponential mode
    write!(abs_int, "{}{:+}", e_symbol, exponent)?;

    let non_negative = matches!(sign, Sign::Plus | Sign::NoSign);
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
    write!(w, "e{}", remaining_digits.len() as i128 - n.scale as i128)
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
fn apply_rounding_to_ascii_digits(
    ascii_digits: &mut Vec<u8>,
    exp: &mut i128,
    prec: usize,
    sign: Sign
) {
    if ascii_digits.len() < prec {
        return;
    }

    // shift exp to align with new length of digits
    *exp += (ascii_digits.len() - prec) as i128;

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
#[allow(non_snake_case)]
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
                format!("{}", Fmt(|f| dynamically_format_decimal($n.to_ref(), f, 2, 9)))
            }};
        }

        impl_case!(case_0d123: "0.123" => "0.123");
        impl_case!(case_0d0123: "0.0123" => "0.0123");
        impl_case!(case_0d00123: "0.00123" => "0.00123");
        impl_case!(case_0d000123: "0.000123" => "1.23E-4");

        impl_case!(case_123d: "123." => "123");
        impl_case!(case_123de1: "123.e1" => "1230");
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
            impl_case!(fmt_d1:        "{:.1}" => "1.0");
            impl_case!(fmt_d4:        "{:.4}" => "1.0000");
            impl_case!(fmt_4d1:      "{:4.1}" => " 1.0");
            impl_case!(fmt_r4d1:    "{:>4.1}" => " 1.0");
            impl_case!(fmt_l4d1:    "{:<4.1}" => "1.0 ");
            impl_case!(fmt_p05d1:  "{:+05.1}" => "+01.0");

            impl_case!(fmt_e:      "{:e}" => "1e+0");
            impl_case!(fmt_E:      "{:E}" => "1E+0");
        }

        mod dec_1e1 {
            use super::*;

            fn test_input() -> BigDecimal {
                BigDecimal::new(1.into(), -1)
            }

            impl_case!(fmt_default:      "{}" => "10");
            impl_case!(fmt_debug:      "{:?}" => "BigDecimal(sign=Plus, scale=-1, digits=[1])");
            impl_case!(fmt_debug_alt: "{:#?}" => "BigDecimal(\"1e1\")");
            impl_case!(fmt_d0:        "{:.0}" => "10");
            impl_case!(fmt_d1:        "{:.1}" => "10.0");
            impl_case!(fmt_d2:        "{:.2}" => "10.00");
        }

        mod dec_1en1 {
            use super::*;

            fn test_input() -> BigDecimal {
                BigDecimal::new(1.into(), 1)
            }

            impl_case!(fmt_default:      "{}" => "0.1");
            impl_case!(fmt_d0:        "{:.0}" => "0");
            impl_case!(fmt_d1:        "{:.1}" => "0.1");
            impl_case!(fmt_d2:        "{:.2}" => "0.10");
        }

        mod dec_9en1 {
            use super::*;

            fn test_input() -> BigDecimal {
                BigDecimal::new(9.into(), 1)
            }

            impl_case!(fmt_default:      "{}" => "0.9");
            impl_case!(fmt_d0:        "{:.0}" => "1");
            impl_case!(fmt_d1:        "{:.1}" => "0.9");
            impl_case!(fmt_d4:        "{:.4}" => "0.9000");
        }

        mod dec_800en3 {
            use super::*;

            fn test_input() -> BigDecimal {
                BigDecimal::new(800.into(), 3)
            }

            impl_case!(fmt_default:      "{}" => "0.800");
            impl_case!(fmt_d0:        "{:.0}" => "1");
            impl_case!(fmt_d1:        "{:.1}" => "0.8");
            impl_case!(fmt_d3:        "{:.3}" => "0.800");
            impl_case!(fmt_d9:        "{:.9}" => "0.800000000");
        }

        mod dec_123456 {
            use super::*;

            fn test_input() -> BigDecimal {
                "123456".parse().unwrap()
            }

            impl_case!(fmt_default:      "{}" => "123456");
            impl_case!(fmt_d1:        "{:.1}" => "123456.0");
            impl_case!(fmt_d4:        "{:.4}" => "123456.0000");
            impl_case!(fmt_4d1:      "{:4.1}" => "123456.0");
            impl_case!(fmt_15d2:    "{:15.2}" => "      123456.00");
            impl_case!(fmt_r15d2:  "{:>15.2}" => "      123456.00");
            impl_case!(fmt_l15d2:  "{:<15.2}" => "123456.00      ");
            impl_case!(fmt_p05d1:  "{:+05.7}" => "+123456.0000000");
        }

        mod dec_9999999 {
            use super::*;

            fn test_input() -> BigDecimal {
                "9999999".parse().unwrap()
            }

            impl_case!(fmt_default:  "{}" => "9999999");
            impl_case!(fmt_d8:  "{:.8}" => "9999999.00000000");

            impl_case!(fmt_e:  "{:e}" => "9.999999e+6");
            impl_case!(fmt_E:  "{:E}" => "9.999999E+6");
            impl_case!(fmt_d0e:  "{:.0e}" => "1e+7");
            impl_case!(fmt_d1e:  "{:.1e}" => "1.0e+7");
            impl_case!(fmt_d2e:  "{:.2e}" => "1.00e+7");
            impl_case!(fmt_d4e:  "{:.4e}" => "1.0000e+7");
            impl_case!(fmt_d6e:  "{:.6e}" => "9.999999e+6");
            impl_case!(fmt_d7e:  "{:.7e}" => "9.9999990e+6");
            impl_case!(fmt_d10e:  "{:.10e}" => "9.9999990000e+6");
        }

        mod dec_19073d97235939614856 {
            use super::*;

            fn test_input() -> BigDecimal {
                "19073.97235939614856".parse().unwrap()
            }

            impl_case!(fmt_default:      "{}" => "19073.97235939614856");
            impl_case!(fmt_pd7:      "{:+.7}" => "+19073.9723594");
            impl_case!(fmt_d0:        "{:.0}" => "19074");
            impl_case!(fmt_d1:        "{:.1}" => "19074.0");
            impl_case!(fmt_d3:        "{:.3}" => "19073.972");
            impl_case!(fmt_d4:        "{:.4}" => "19073.9724");
            impl_case!(fmt_8d3:      "{:8.3}" => "19073.972");
            impl_case!(fmt_10d3:    "{:10.3}" => " 19073.972");
            impl_case!(fmt_010d3:  "{:010.3}" => "019073.972");
        }

        mod dec_n90037659d6902 {
            use super::*;

            fn test_input() -> BigDecimal {
                "-90037659.6905".parse().unwrap()
            }

            impl_case!(fmt_default:      "{}" => "-90037659.6905");
            impl_case!(fmt_debug:      "{:?}" => "BigDecimal(sign=Minus, scale=4, digits=[900376596905])");
            impl_case!(fmt_debug_alt: "{:#?}" => "BigDecimal(\"-900376596905e-4\")");
            impl_case!(fmt_pd7:      "{:+.7}" => "-90037659.6905000");
            impl_case!(fmt_d0:        "{:.0}" => "-90037660");
            impl_case!(fmt_d3:        "{:.3}" => "-90037659.690");
            impl_case!(fmt_d4:        "{:.4}" => "-90037659.6905");
            impl_case!(fmt_14d4:      "{:14.4}" => "-90037659.6905");
            impl_case!(fmt_15d4:    "{:15.4}" => " -90037659.6905");
            impl_case!(fmt_l17d5:  "{:<17.5}" => "-90037659.69050  ");
        }

        mod dec_1764031078en13 {
            use super::*;

            fn test_input() -> BigDecimal {
                BigDecimal::new(1764031078.into(), 13)
            }

            impl_case!(fmt_default:    "{}" => "0.0001764031078");
            impl_case!(fmt_d1:      "{:.1}" => "0.0");
            impl_case!(fmt_d3:      "{:.3}" => "0.000");
            impl_case!(fmt_d4:      "{:.4}" => "0.0002");
            impl_case!(fmt_d5:      "{:.5}" => "0.00018");
            impl_case!(fmt_d13:    "{:.13}" => "0.0001764031078");
            impl_case!(fmt_d20:    "{:.20}" => "0.00017640310780000000");

        }

        mod dec_1e15 {
            use super::*;

            fn test_input() -> BigDecimal {
                "1e15".parse().unwrap()
            }

            impl_case!(fmt_default:        "{}" => "1000000000000000");
            impl_case!(fmt_d0:          "{:.0}" => "1000000000000000");
            impl_case!(fmt_d1:          "{:.1}" => "1000000000000000.0");
        }

        mod dec_1e16 {
            use super::*;

            fn test_input() -> BigDecimal {
                "1e16".parse().unwrap()
            }

            impl_case!(fmt_default:        "{}" => "1e16");
            impl_case!(fmt_d0:          "{:.0}" => "10000000000000000");
            impl_case!(fmt_d1:          "{:.1}" => "10000000000000000.0");
        }


        mod dec_491326en12 {
            use super::*;

            fn test_input() -> BigDecimal {
                "491326e-12".parse().unwrap()
            }

            impl_case!(fmt_default:        "{}" => "4.91326E-7");
            impl_case!(fmt_d0:          "{:.0}" => "5E-7");
            impl_case!(fmt_d1:          "{:.1}" => "4.9E-7");
            impl_case!(fmt_d3:          "{:.3}" => "4.913E-7");
            impl_case!(fmt_d5:          "{:.5}" => "4.91326E-7");
            impl_case!(fmt_d6:          "{:.6}" => "4.913260E-7");

            impl_case!(fmt_d9:          "{:.9}" => "4.913260000E-7");
            impl_case!(fmt_d20:        "{:.20}" => "4.91326000000000000000E-7");
        }

        mod dec_0d00003102564500 {
            use super::*;

            fn test_input() -> BigDecimal {
                "0.00003102564500".parse().unwrap()
            }

            impl_case!(fmt_default: "{}" => "0.00003102564500");
            impl_case!(fmt_d0:   "{:.0}" => "0");
            impl_case!(fmt_d4:   "{:.4}" => "0.0000");
            impl_case!(fmt_d5:   "{:.5}" => "0.00003");
            impl_case!(fmt_d10:  "{:.10}" => "0.0000310256");
            impl_case!(fmt_d14:  "{:.14}" => "0.00003102564500");
            impl_case!(fmt_d17:  "{:.17}" => "0.00003102564500000");

            impl_case!(fmt_e:      "{:e}" => "3.102564500e-5");
            impl_case!(fmt_de:    "{:.e}" => "3.102564500e-5");
            impl_case!(fmt_d0e:  "{:.0e}" => "3e-5");
            impl_case!(fmt_d1e:  "{:.1e}" => "3.1e-5");
            impl_case!(fmt_d4e:  "{:.4e}" => "3.1026e-5");
        }

        mod dec_1en100000 {
            use super::*;

            fn test_input() -> BigDecimal {
                "1E-10000".parse().unwrap()
            }

            impl_case!(fmt_default: "{}" => "1E-10000");
            impl_case!(fmt_d1: "{:.1}" => "1.0E-10000");
            impl_case!(fmt_d4: "{:.4}" => "1.0000E-10000");
        }

        mod dec_1e100000 {
            use super::*;

            fn test_input() -> BigDecimal {
                "1e10000".parse().unwrap()
            }

            impl_case!(fmt_default: "{}" => "1E+10000");
            impl_case!(fmt_d1: "{:.1}" => "1.0E+10000");
            impl_case!(fmt_d4: "{:.4}" => "1.0000E+10000");
        }


        mod dec_1234506789E5 {
            use super::*;

            fn test_input() -> BigDecimal {
                BigDecimal::new(1234506789.into(), -5)
            }

            impl_case!(fmt_default: "{}" => "123450678900000");
            impl_case!(fmt_d1: "{:.1}" => "123450678900000.0");
            impl_case!(fmt_d3: "{:.3}" => "123450678900000.000");
            impl_case!(fmt_d4: "{:.4}" => "123450678900000.0000");
            impl_case!(fmt_l13d4: "{:<23.4}" => "123450678900000.0000   ");
            impl_case!(fmt_r13d4: "{:>23.4}" => "   123450678900000.0000");
        }

        mod dec_1234506789E15 {
            use super::*;

            fn test_input() -> BigDecimal {
                BigDecimal::new(1234506789.into(), -15)
            }

            impl_case!(fmt_default: "{}" => "1.234506789E+24");
            impl_case!(fmt_d1: "{:.1}" => "1.2E+24");
            impl_case!(fmt_d3: "{:.3}" => "1.235E+24");
            impl_case!(fmt_d4: "{:.4}" => "1.2345E+24");
            impl_case!(fmt_l13d4: "{:<13.4}" => "1.2345E+24   ");
            impl_case!(fmt_r13d4: "{:>13.4}" => "   1.2345E+24");
        }
    }

    mod fmt_boundaries {
        use super::*;

        macro_rules! impl_case {
            ( $name:ident: $src:expr => $expected:literal ) => {
                #[test]
                fn $name() {
                    let src = $src;
                    let bd: BigDecimal = src.parse().unwrap();
                    let result = bd.to_string();
                    assert_eq!(result, $expected);

                    bd.to_scientific_notation();
                    bd.to_engineering_notation();

                    let round_trip = BigDecimal::from_str(&result).unwrap();
                    assert_eq!(round_trip, bd);
                }
            };
            ( (panics) $name:ident: $src:expr ) => {
                #[test]
                #[should_panic]
                fn $name() {
                    let src = $src;
                    let _bd: BigDecimal = src.parse().unwrap();
                }
            };
        }

        impl_case!(test_max: format!("1E{}", i64::MAX) => "1E+9223372036854775807");
        impl_case!(test_max_multiple_digits: format!("314156E{}", i64::MAX) => "3.14156E+9223372036854775812");
        impl_case!(test_min_scale: "1E9223372036854775808" => "1E+9223372036854775808");
        impl_case!(test_max_scale: "1E-9223372036854775807" => "1E-9223372036854775807");
        impl_case!(test_min_multiple_digits: format!("271828182E-{}", i64::MAX) => "2.71828182E-9223372036854775799");

        impl_case!((panics) test_max_exp_overflow: "1E9223372036854775809");
        impl_case!((panics) test_min_exp_overflow: "1E-9223372036854775808");
    }

    #[test]
    fn test_fmt() {
        let vals = vec![
            // b  s (      {}     {:.1}        {:.4}    {:4.1}   {:+05.1}   {:<4.1}
            (1, 0,  (     "1",    "1.0",    "1.0000",   " 1.0",   "+01.0",   "1.0 " )),
            (1, 1,  (   "0.1",    "0.1",    "0.1000",   " 0.1",   "+00.1",   "0.1 " )),
            (1, 2,  (  "0.01",    "0.0",    "0.0100",   " 0.0",   "+00.0",   "0.0 " )),
            (1, -2, (   "100",  "100.0",  "100.0000",  "100.0",  "+100.0",  "100.0" )),
            (-1, 0, (    "-1",   "-1.0",   "-1.0000",   "-1.0",   "-01.0",   "-1.0" )),
            (-1, 1, (  "-0.1",   "-0.1",   "-0.1000",   "-0.1",   "-00.1",   "-0.1" )),
            (-1, 2, ( "-0.01",   "-0.0",   "-0.0100",   "-0.0",   "-00.0",   "-0.0" )),
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
