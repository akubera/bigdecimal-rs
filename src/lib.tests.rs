
mod is_one {
    use super::*;

    #[test]
    fn all_from_1_1000() {
        let mut i = BigUint::from(1u8);

        for s in 1..1000 {
            i *= 10u8;
            let d = BigDecimalRef::from(WithScale { value: &i, scale: s });
            assert!(d.is_one(), "{}", s);

            i += 1u8;
            let d = BigDecimalRef::from(WithScale { value: &i, scale: s });
            assert!(!d.is_one(), "{}", s);

            i -= 1u8;
        }
    }

    macro_rules! impl_case {
        ($name:ident: $input:literal => $expected:literal) => {
            #[test]
            fn $name() {
                let d: BigDecimal = $input.parse().unwrap();
                assert_eq!(d.is_one(), $expected);
            }
        };
    }

    impl_case!(case_0: "0" => false);
    impl_case!(case_1: "1" => true);
    impl_case!(case_n1: "-1" => false);
    impl_case!(case_10en1: "10e-1" => true);
    impl_case!(case_100en2: "100e-2" => true);
    impl_case!(case_10000en4: "10000e-4" => true);
    impl_case!(case_1d00000000000000000:   "1.00000000000000000" => true);
    impl_case!(case_1d000000000000000000:  "1.000000000000000000" => true);
    impl_case!(case_1d0000000000000000000: "1.0000000000000000000" => true);
    impl_case!(case_1d00000000000000001:   "1.00000000000000001" => false);
    impl_case!(case_1d000000000000000001:  "1.000000000000000001" => false);
    impl_case!(case_1d0000000000000000001: "1.0000000000000000001" => false);
    impl_case!(case_1d00000000000000000000000000000000: "1.00000000000000000000000000000000" => true);
    impl_case!(case_1d00000000000000000000000000000001: "1.00000000000000000000000000000001" => false);
    impl_case!(case_10d0000000000000000000000000000000000: "10.00000000000000000000000000000000000" => false);
}

mod is_one_quickcheck {
    use super::*;

    #[test]
    fn all_from_1_1e39() {
        let mut i = BigUint::from(1u8);

        for s in 1..39 {
            i *= 10u8;
            let d = BigDecimalRef::from(WithScale { value: &i, scale: s });
            assert_eq!(d.is_one_quickcheck(), Some(true), "{}", s);

            i += 1u8;
            let d = BigDecimalRef::from(WithScale { value: &i, scale: s });
            assert_eq!(d.is_one_quickcheck(), Some(false), "{}", s);

            i -= 1u8;
        }
    }

    macro_rules! impl_case {
        ($name:ident: $input:literal => $expected:expr) => {
            #[test]
            fn $name() {
                let d: BigDecimal = $input.parse().unwrap();
                assert_eq!(d.is_one_quickcheck(), $expected);
            }
        };
    }

    impl_case!(case_0: "0" => Some(false));
    impl_case!(case_1: "1" => Some(true));
    impl_case!(case_n1: "-1" => Some(false));
    impl_case!(case_10000000000000000000en19:   "10000000000000000000e-19" => Some(true));
    impl_case!(case_1d00000000000000000000:   "1.00000000000000000000" => Some(true));
    impl_case!(case_1d00000000000000000000000000000001: "1.00000000000000000000000000000001" => Some(false));

    impl_case!(case_pi15: "3.141592653589793" => Some(false));
    impl_case!(case_pi20: "3.14159265358979323846" => Some(false));
    impl_case!(case_pi50: "3.1415926535897932384626433832795028841971693993751" => None);

    impl_case!(case_10d00000000000000000000:   "10.00000000000000000000" => Some(false));
    impl_case!(case_1000000000d00000000000000000000:   "1000000000.00000000000000000000" => Some(false));
    impl_case!(case_10000000000000000000000000d0000000000000000000000000000000000000000000:   "10000000000000000000000000.0000000000000000000000000000000000000000000" => Some(false));
    impl_case!(case_10000000000000000000000000d0x:   "10000000000000000000000000.0" => Some(false));
}


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
