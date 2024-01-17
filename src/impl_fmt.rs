//! fmt implementations and stringification routines
//!

use stdlib::fmt;


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


#[rustfmt::skip]
#[cfg(test)]
#[allow(non_snake_case)]
mod bigdecimal_tests {

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
}
