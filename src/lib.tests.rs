
mod decimal_digit_count {
    use super::*;

    macro_rules! impl_case {
        ($name:ident: $input:literal => $expected:literal) => {
            #[test]
            fn $name() {
                let d: BigDecimal = $input.parse().unwrap();
                assert_eq!(d.decimal_digit_count(), $expected);
            }
        };
    }

    impl_case!(case_0: "0" => 1);
    impl_case!(case_1: "1" => 1);
    impl_case!(case_10: "10" => 2);
    impl_case!(case_10d01: "10.01" => 4);
    impl_case!(case_d00099999999999: ".00099999999999" => 11);
}

mod order_of_magnitude {
    use super::*;

    macro_rules! impl_case {
        ($name:ident: $input:literal => $expected:literal) => {
            #[test]
            fn $name() {
                let d: BigDecimal = $input.parse().unwrap();
                assert_eq!(d.order_of_magnitude(), $expected);
            }
        };
    }

    impl_case!(case_0: "0" => 0);
    impl_case!(case_1: "1" => 0);
    impl_case!(case_10: "10" => 1);
    impl_case!(case_1e1: "1e1" => 1);
    impl_case!(case_0e3: "0e3" => 0);
    impl_case!(case_30e2: "30e2" => 3);
    impl_case!(case_99en2: "99e-2" => -1);
    impl_case!(case_n100d0012e1: "-100.0012e1" => 3);
    impl_case!(case_16651567373773d553089: "16651567373773.553089" => 13);
}
