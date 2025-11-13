
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

            let expected = $expected.parse().unwrap();

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

            let expected = $expected.parse().unwrap();

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

