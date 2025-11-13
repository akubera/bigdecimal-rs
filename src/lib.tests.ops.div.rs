
mod impl_div {
    use super::*;

    macro_rules! impl_case {
        ($name:ident: $numerator:literal / $denominator:literal => $quotient:literal) => {
            #[test]
            fn $name() {
                let a: BigDecimal = $numerator.parse().unwrap();
                let b: BigDecimal = $denominator.parse().unwrap();
                let c: BigDecimal = $quotient.parse().unwrap();

                let q = a.clone() / b.clone();
                assert_eq!(q, c);
                assert_eq!(q.scale, c.scale);
                assert_eq!(a.clone() / &b, c);
                assert_eq!(&a / b.clone(), c);
                assert_eq!(&a / &b, c);
            }
        };
    }

    impl_case!(zero_over_one: "0" / "1" => "0");
    impl_case!(zero_over_ten: "0" / "10" => "0");
    impl_case!(two_over_one: "2" / "1" => "2");
    impl_case!(div_2e1_one: "2e1" / "1" => "2e1");
    impl_case!(div_10_10: "10" / "10" => "1");
    impl_case!(div_100_10d0: "100" / "10.0" => "1e1");

    impl_case!(div_20d0_200: "20.0" / "200" => "0.1");
    impl_case!(div_4_2: "4" / "2" => "2");
    impl_case!(div_15_3: "15" / "3" => "5");
    impl_case!(div_1_2: "1" / "2" => "0.5");
    impl_case!(div_1_2en2: "1" / "2e-2" => "5e1");
    impl_case!(div_1_0d2: "1" / "0.2" => "5");
    impl_case!(div_1d0_0d02: "1.0" / "0.02" => "5e1");
    impl_case!(div_1_0d020: "1" / "0.020" => "5e1");
    impl_case!(div_1d0_0d020: "1.0" / "0.020" => "5e1");
    impl_case!(div_5d0_4d00: "5.0" / "4.00" => "1.25");
    impl_case!(div_5d0_4d000: "5.0" / "4.000" => "1.25");
    impl_case!(div_5_4d000: "5" / "4.000" => "1.25");
    impl_case!(div_5_4: "5" / "4" => "125e-2");
    impl_case!(div_100_5: "100" / "5" => "20");
    impl_case!(div_n50_5: "-50" / "5" => "-10");
    impl_case!(div_200_n5: "200" / "-5" => "-40.");
    impl_case!(div_1_3: "1" / "3" => ".3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333");
    impl_case!(div_n2_n3: "-2" / "-3" => ".6666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666667");
    impl_case!(div_n12d34_1d233: "-12.34" / "1.233" => "-10.00811030008110300081103000811030008110300081103000811030008110300081103000811030008110300081103001");
    impl_case!(div_125348_352d2283: "125348" / "352.2283" => "355.8714617763535752237966114591019517738921035021887792661748076460636467881768727839301952739175132");
    impl_case!(div_22_7: "22" / "7" => "3.142857142857142857142857142857142857142857142857142857142857142857142857142857142857142857142857143");

    #[test]
    #[should_panic(expected = "Division by zero")]
    fn test_division_by_zero_panics() {
        let x = BigDecimal::from_str("3.14").unwrap();
        let _r = x / 0;
    }

    #[test]
    #[should_panic(expected = "Division by zero")]
    fn test_division_by_zero_panics_v2() {
        let x = BigDecimal::from_str("3.14").unwrap();
        let _r = x / BigDecimal::zero();
    }

    #[test]
    fn test_division_by_large_number() {
        let n = 1u8;
        let d: BigDecimal = "79437738588056219546528239237352667078".parse().unwrap();

        let quotient_n_ref_d = n / &d;
        let quotient_n_d = n / d.clone();
        assert_eq!(quotient_n_ref_d, quotient_n_d);

        let expected: BigDecimal = "1.258847517281104957975270408416632052090243053529147458917576143852500316808428812104171430669001064E-38".parse().unwrap();
        assert_eq!(quotient_n_ref_d, expected);
    }
}

#[test]
fn divide_by_f32_infinity() {
    let num: BigDecimal = "123".parse().unwrap();
    let quotient = num / f32::INFINITY;
    assert!(quotient.is_zero());
}

#[test]
fn divide_by_f32_nan() {
    let num: BigDecimal = "123".parse().unwrap();
    let quotient = num / f32::NAN;
    assert!(quotient.is_zero());
}

#[test]
fn divide_by_f64_infinity() {
    let num: BigDecimal = "123".parse().unwrap();
    let quotient = num / f64::INFINITY;
    assert!(quotient.is_zero());
}

#[test]
fn divide_by_f64_nan() {
    let num: BigDecimal = "123".parse().unwrap();
    let quotient = num / f64::NAN;
    assert!(quotient.is_zero());
}

macro_rules! impl_case {
    ($name:ident: num / $denom:literal => $expected:literal)  => {
        #[test]
        fn $name() {
            let num = numerator();
            let den = $denom;

            let expected: BigDecimal = $expected.parse().unwrap();

            {
                let quotient = &num / den;
                assert_eq!(&quotient, &expected);
            }

            let quotient = num / den;
            assert_eq!(quotient, expected);
        }
    };
    ($name:ident: $numer:literal / den => $expected:literal)  => {
        #[test]
        fn $name() {
            let num = $numer;
            let den = denominator();

            let expected: BigDecimal = $expected.parse().unwrap();

            {
                let quotient = num / &den;
                assert_eq!(&quotient, &expected);
            }

            let quotient = num / den;
            assert_eq!(quotient, expected);
        }
    }
}

mod dec123_over_float {
    use super::*;

    fn numerator() -> BigDecimal {
        "123".parse().unwrap()
    }

    impl_case!(divide_by_one: num / 1.0 => "123");
    impl_case!(divide_by_neg_one: num / -1.0 => "-123");
    impl_case!(divide_by_two: num / 2.0 => "61.5");
    impl_case!(divide_by_neg_two: num / -2.0 => "-61.5");
    impl_case!(divide_by_half: num / 0.25 => "492");

    impl_case!(divide_by_0d3: num / 0.3 => "410.0000000000000151730480032104732806385410274753293198491224660103204812897069364682009036747721645");
    impl_case!(divide_by_n10d01: num / -10.01 => "-12.28771228771228797395438676755509642184314950109407611037730443717479254091338404424812715057130341");
}

mod num_float_over_dec123 {
    use super::*;

    fn denominator() -> BigDecimal {
        "123".parse().unwrap()
    }

    impl_case!(num_one: 1.0 / den => "0.008130081300813008130081300813008130081300813008130081300813008130081300813008130081300813008130081301");
    impl_case!(num_123: 123.0 / den => "1");
    impl_case!(num_676d5: 676.5 / den => "5.5");
}

