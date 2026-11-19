//! inverse implementation

use crate::*;
use arithmetic::decimal::get_power_of_ten_u64;

pub(crate) fn inverse_scaled_uint_with_context<'a>(
    n: impl Into<WithScale<&'a BigUint>>,
    sign: Sign,
    ctx: &Context,
) -> BigDecimal {
    let WithScale { value: n, scale } = n.into();
    impl_inverse_signed_uint_scale(n, scale, sign, ctx)
}

/// Implementation of inverse: 1/(sign * n * 10^(-scale)), rounded with ctx
///
/// The sign is needed before rounding, so that Floor and Ceiling
/// round in the right direction for negative numbers.
///
fn impl_inverse_signed_uint_scale(n: &BigUint, scale: i64, sign: Sign, ctx: &Context) -> BigDecimal {
    debug_assert!(!n.is_zero());

    if let Some(small_pow_ten) = n.to_u64().and_then(get_power_of_ten_u64) {
        // optimized inversion for small power of ten:
        //  1/10^{pow - scale} = 10^{scale - pow}

        // create bigint with requested precision
        let prec = ctx.precision().get();
        let inv_int = BigInt::from_biguint(sign, ten_to_the_uint(prec - 1));

        // increase inverted scale by requested precision
        let inv_scale = small_pow_ten as i64 - scale + prec as i64 - 1;

        return BigDecimal::new(inv_int, inv_scale);
    }

    // 1/(n * 10^-scale) = (10^shift / n) * 10^(scale - shift)
    //
    // With shift = prec + digits(n), the integer quotient has 'prec'
    // or 'prec + 1' digits, so it holds every digit we keep.
    let prec = ctx.precision().get();
    let shift = prec + count_decimal_digits_uint(n);
    let (quotient, remainder) = ten_to_the_uint(shift).div_rem(n);

    // Append one more digit: 0 if the division is exact, else 1.
    // This tells the rounding step whether the dropped digits are
    // all zero, so Up/Ceiling/Floor and the half-way modes see the
    // exact value instead of a truncated one.
    let mut digits = quotient * 10u8;
    if !remainder.is_zero() {
        digits += 1u8;
    }

    let result = BigDecimal::new(BigInt::from_biguint(sign, digits), shift as i64 + 1 - scale);
    result.with_precision_round(ctx.precision(), ctx.rounding_mode())
}

#[cfg(test)]
mod test {
    use super::*;
    use paste::paste;
    use stdlib::num::NonZeroU64;

    #[test]
    fn test_inverse_35543972957198043e291() {
        let v = vec![
            0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
            0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
            2324389888, 849200558
        ];
        let x = BigInt::new(Sign::Minus, v);
        let d = BigDecimal::from(x);
        let expected = "-2.813416500187520746852694701086705659180043761702417561798711758892800449936819185796527214192677476E-308".parse::<BigDecimal>().unwrap();
        assert_eq!(d.inverse(), expected);

        assert_eq!(d.neg().inverse(), expected.neg());
    }

    macro_rules! impl_case {
        ($name:ident: $prec:literal, $round:ident => $expected:literal) => {
            #[test]
            fn $name() {
                let n = test_input();
                let prec = NonZeroU64::new($prec).unwrap();
                let rounding = RoundingMode::$round;
                let ctx = Context::new(prec, rounding);

                let result = n.inverse_with_context(&ctx);

                let expected = $expected.parse::<BigDecimal>().unwrap();
                assert_eq!(&result, &expected);

                let product = result * &n;
                let epsilon = BigDecimal::new(BigInt::one(), $prec - 1);
                let diff = (BigDecimal::one() - &product).abs();
                assert!(diff < epsilon);
            }
        };
        (prec=$prec:literal, round=$round:ident => $expected:literal) => {
            paste! {
                #[test]
                fn [< case_prec $prec _round_ $round:lower >] () {
                    let n = test_input();
                    let prec = NonZeroU64::new($prec).unwrap();
                    let rounding = RoundingMode::$round;
                    let ctx = Context::new(prec, rounding);

                    let result = n.inverse_with_context(&ctx);

                    let expected = $expected.parse::<BigDecimal>().unwrap();
                    assert_eq!(&result, &expected);
                    assert_eq!(&result.scale, &expected.scale);
                }
            }
        };
        (prec=$prec:literal, round=$($round:ident),+ => $expected:literal) => {
            $( impl_case!(prec=$prec, round=$round => $expected); )*
        };
    }

    mod invert_one {
        use super::*;

        fn test_input() -> BigDecimal {
            1u8.into()
        }

        impl_case!(prec=1, round=Up,Down => "1");
        impl_case!(prec=2, round=Up,Down => "1.0");
        impl_case!(prec=7, round=Up,Down => "1.000000");
    }

    mod invert_n1d00 {
        use super::*;

        fn test_input() -> BigDecimal {
            "-1.00".parse().unwrap()
        }

        impl_case!(prec=1, round=Up,Down => "-1");
        impl_case!(prec=5, round=Up,Down => "-1.0000");
    }

    mod invert_n1000en8 {
        use super::*;

        fn test_input() -> BigDecimal {
            "1000e-8".parse().unwrap()
        }

        impl_case!(prec=1, round=Up,Down => "1e5");
        impl_case!(prec=5, round=Up,Down => "10000e1");
        impl_case!(prec=6, round=Up,Down => "100000");
        impl_case!(prec=8, round=Up,Down => "100000.00");
    }

    mod invert_seven {
        use super::*;

        fn test_input() -> BigDecimal {
            BigDecimal::from(7u8)
        }

        impl_case!(case_prec10_round_down: 10, Down => "0.1428571428");
        impl_case!(case_prec10_round_up: 10, Up => "0.1428571429");

        impl_case!(case_prec11_round_ceiling: 11, Ceiling => "0.14285714286");
    }

    mod invert_ten {
        use super::*;

        fn test_input() -> BigDecimal {
            10u8.into()
        }

        impl_case!(case_prec1_round_down: 1, Down => "0.1");
        impl_case!(case_prec2_round_down: 2, Down => "0.10");
        impl_case!(prec=10, round=Up, Down => "0.1000000000");
    }

    mod invert_n3242342d34324 {
        use super::*;

        fn test_input() -> BigDecimal {
            "-3242342.34324".parse().unwrap()
        }

        impl_case!(prec=50, round=Up, Floor => "-3.0841900519385698894827476971712670726697831310897E-7");
        impl_case!(prec=50, round=Down, Ceiling => "-3.0841900519385698894827476971712670726697831310896E-7");
    }

    mod invert_n7 {
        use super::*;

        fn test_input() -> BigDecimal {
            BigDecimal::from(-7)
        }

        // -1/7 = -0.142857142857...
        impl_case!(prec=10, round=Up, Floor => "-0.1428571429");
        impl_case!(prec=10, round=Down, Ceiling => "-0.1428571428");
    }

    mod invert_9d99en8 {
        use super::*;

        fn test_input() -> BigDecimal {
            "9.99e-8".parse().unwrap()
        }

        // 1/9.99e-8 = 10010010.01001001...
        // the digits after the 4th are "0010.01...", not zero
        impl_case!(prec=4, round=Up, Ceiling => "1.002e7");
        impl_case!(prec=4, round=Down, Floor, HalfUp, HalfEven => "1.001e7");
        impl_case!(prec=6, round=Up => "1.00101e7");
        impl_case!(prec=6, round=Down => "1.00100e7");
    }

    mod invert_n9d99en8 {
        use super::*;

        fn test_input() -> BigDecimal {
            "-9.99e-8".parse().unwrap()
        }

        impl_case!(prec=4, round=Up, Floor => "-1.002e7");
        impl_case!(prec=4, round=Down, Ceiling => "-1.001e7");
    }


    mod invert_2d8722377233432854650en126 {
        use super::*;

        fn test_input() -> BigDecimal {
            "28722377233432854650456573411382289859440620032075590707304700193738855195818029876568741547799767753181511758371393266031229989006058870578446812747289276920741036671713994469786904880406812933015496296559493964954240161851051500623562557032166800306346000498803201936493334049050141321136859175463065287081665388768669799901545047760009765625e-469"
            .parse().unwrap()
        }

        impl_case!(prec=1,  round=Up => "4e125");
        impl_case!(prec=5,  round=Up => "3.4817e+125");
        impl_case!(prec=25, round=Up => "3.481605968311006434080812E+125");
    }

    #[test]
    fn inv_random_number() {
        let n = BigDecimal::try_from(0.08121970592310568).unwrap();

        let ctx = Context::new(NonZeroU64::new(40).unwrap(), RoundingMode::Down);
        let i = n.inverse_with_context(&ctx);
        assert_eq!(&i, &"12.31228294456944530942557443718279245563".parse::<BigDecimal>().unwrap());

        let product = i * &n;
        assert!(BigDecimal::one() - &product < "1e-39".parse::<BigDecimal>().unwrap());
    }

    #[cfg(property_tests)]
    mod prop {
        use super::*;
        use proptest::*;
        use num_traits::FromPrimitive;

        proptest! {

            #[test]
            fn inverse_multiplies_to_one(f: f64, prec in 1..100u64) {
                // ignore non-normal numbers
                prop_assume!(f.is_normal());
                prop_assume!(f != 0.0);

                let n = BigDecimal::from_f64(f).unwrap();

                let ctx = Context::new(NonZeroU64::new(prec).unwrap(), RoundingMode::Up);
                let i = n.inverse_with_context(&ctx);
                let product = &i * &n;

                // accurate to precision minus one (due to rounding)
                let epsilon = BigDecimal::new(1.into(), prec as i64 - 1);
                let diff_from_one = BigDecimal::one() - &product;

                prop_assert!(diff_from_one.abs() < epsilon, "{} >= {}", diff_from_one.abs(), epsilon);
            }
        }
    }
}
