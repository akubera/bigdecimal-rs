use crate::*;
use stdlib::str::FromStr;

impl FromStr for BigDecimal {
    type Err = ParseBigDecimalError;

    #[inline]
    fn from_str(s: &str) -> Result<BigDecimal, ParseBigDecimalError> {
        BigDecimal::from_str_radix(s, 10)
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! impl_case {
        ($name:ident: $input:literal => $int:literal E $exp:literal) => {
            #[test]
            fn $name() {
                let dec = BigDecimal::from_str($input).unwrap();
                assert_eq!(dec.int_val, $int.into());
                assert_eq!(dec.scale, -$exp);
            }
        };
    }

    impl_case!(case_1331d107: "1331.107" => 1331107 E -3 );
    impl_case!(case_1d0: "1.0" => 10 E -1 );
    impl_case!(case_2e1: "2e1" => 2 E 1 );
    impl_case!(case_0d00123: "0.00123" => 123 E -5);
    impl_case!(case_n123: "-123" => -123 E -0);
    impl_case!(case_n1230: "-1230" => -1230 E -0);
    impl_case!(case_12d3: "12.3" => 123 E -1);
    impl_case!(case_123en1: "123e-1" => 123 E -1);
    impl_case!(case_1d23ep1: "1.23e+1" => 123 E -1);
    impl_case!(case_1d23ep3: "1.23E+3" => 123 E 1);
    impl_case!(case_1d23en8: "1.23E-8" => 123 E -10);
    impl_case!(case_n1d23en10: "-1.23E-10" => -123 E -12);
    impl_case!(case_123_: "123_" => 123 E -0);
    impl_case!(case_31_862_140d830_686_979: "31_862_140.830_686_979" => 31862140830686979i128 E -9);
    impl_case!(case_n1_1d2_2: "-1_1.2_2" => -1122 E -2);
    impl_case!(case_999d521_939: "999.521_939" => 999521939 E -6);
    impl_case!(case_679d35_84_03en2: "679.35_84_03E-2" => 679358403 E -8);
    impl_case!(case_271576662d_e4: "271576662.__E4" => 271576662 E 4);
}
