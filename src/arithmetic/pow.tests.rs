use paste::paste;

#[allow(non_snake_case)]
mod powi_with_context {
    use super::*;

    macro_rules! impl_cases {
        ( pow= - $pow:literal : $( prec=$prec:literal, round=$($round:ident),+ => $expected:literal ; )+ ) => {
            $( paste!{ impl_cases!([<pow_n$pow>]; -$pow; $($round),*; $prec; $expected); } )*
        };
        ( pow=$pow:literal : $( prec=$prec:literal, round=$($round:ident),+ => $expected:literal ; )+ ) => {
            $( paste!{ impl_cases!([<pow_$pow>]; $pow; $($round),*; $prec; $expected); } )*
        };
        ($name:ident; $pow:literal; $round:ident; $prec:literal; $expected:literal) => {
            paste!{
                #[test]
                fn [< $name _prec $prec _round_ $round >]() {
                    let n = test_input();
                    let prec = $prec;
                    let exp = $pow;
                    let ctx = Context::default()
                                    .with_rounding_mode(RoundingMode::$round)
                                    .with_prec(prec).unwrap();
                    let value = n.powi_with_context(exp, &ctx);
                    let expected: BigDecimal = $expected.parse().unwrap();
                    assert_eq!(value, expected);
                    assert_eq!(value.scale, expected.scale);
                }
            }
        };
        ($name:ident; $pow:literal; $($round:ident),+; $prec:literal; $expected:literal) => {
            $( impl_cases!($name; $pow; $round; $prec; $expected); )*
        };
    }

    mod case_999en3 {
        use super::*;

        fn test_input() -> BigDecimal {
            "0.999".parse().unwrap()
        }

        impl_cases!(
            pow=100 :
                prec=1, round=Up   => "1";
                prec=1, round=Down => "0.9";
                prec=2, round=Up   => "0.91";
                prec=2, round=Down => "0.90";
                prec=10, round=Up  => "0.9047921472";
        );

        impl_cases!(
            pow=1001 :
                prec=30, round=Up  => "0.367327729346193080582179333082";
                prec=38, round=Up  => "0.36732772934619308058217933308124088263";
        );

        impl_cases!(
            pow=30_000_000 :
                prec=1, round=Up   => "5E-13036";
                prec=1, round=Down => "4E-13036";
                prec=2, round=Down => "4.4E-13036";
                prec=20, round=Up  => "4.4338344072941502620E-13036";
        );
    }

    mod case_1d5319977452724413736 {
        use super::*;

        fn test_input() -> BigDecimal {
            "1.5319977452724413736".parse().unwrap()
        }

        impl_cases!(
            pow=1:
                prec=5, round=Up   => "1.5320";
                prec=5, round=Down => "1.5319";
        );

        impl_cases!(
            pow=580:
                prec=5, round=Up   => "2.8166E+107";
                prec=5, round=Down => "2.8165E+107";
        );

        impl_cases!(
            pow=-580:
                prec=5, round=Up   => "3.5505E-108";
                prec=5, round=Down => "3.5504E-108";
        );
    }

    mod case_neg1040582726326750d5484 {
        use super::*;

        fn test_input() -> BigDecimal {
            "-1040582726326750.5484".parse().unwrap()
        }

        impl_cases!(
            pow=4:
                prec=19, round=Up, Ceiling    => "1.172482715963826257E+60";
                prec=19, round=Down, HalfEven => "1.172482715963826256E+60";
        );

        impl_cases!(
            pow=-51:
                prec=19, round=Up, Floor     => "-1.314900138431188004E-766";
                prec=19, round=Down, Ceiling => "-1.314900138431188003E-766";
        );
    }


    mod case_4d135846964 {
        use super::*;

        fn test_input() -> BigDecimal {
            "4.135846964236207374549487108400332686443027446631549764347102855558635985583587468810645966176878292".parse().unwrap()
        }

        impl_cases!(
            pow=52 :
                prec=30, round=Up => "1.15173335866675718975392626426e32";
                prec=52, round=Up => "115173335866675718975392626425044.8429283056873556580";
                prec=100, round=Up   => "115173335866675718975392626425044.8429283056873556579339935191839667843520503303080335324003379361749";
                prec=100, round=Down => "115173335866675718975392626425044.8429283056873556579339935191839667843520503303080335324003379361748";
                prec=220, round=Up => "115173335866675718975392626425044.8429283056873556579339935191839667843520503303080335324003379361748091953445157717419294900287105759027634531967229789408468617796286936526237706376914237296824445112814900146493371906508";
        );

        impl_cases!(
            pow=400 :
                prec=30,  round=Down => "4.22458642351596686588868351991e246";
                prec=50,  round=Up   => "4.2245864235159668658886835199155003081243046945638e246";
                prec=100, round=Down => "4.224586423515966865888683519915500308124304694563763586647543454119991635745909994893495905909587954e246";
        );

        impl_cases!(
            pow=527 :
                prec=1, round=Up     => "9e324";
                prec=1, round=HalfUp => "9e324";
                prec=15, round=Down   => "8.50101303706824E+324";
                prec=19, round=Down   => "8.501013037068242474E+324";
                prec=20, round=Down   => "8.5010130370682424747E+324";
        );

        impl_cases!(
            pow=550 :
                prec=1, round=Up   => "2e339";
                prec=5, round=Down => "1.2895e339";
                prec=15, round=Down => "1.28959480113192E+339";
        );
    }

    mod case_23994 {
        use super::*;

        fn test_input() -> BigDecimal {
            "23994".parse().unwrap()
        }

        impl_cases!(
            pow=6 :
                prec=1, round=Up   => "2e26";
                prec=6, round=Down => "1.90816E+26";
                prec=6, round=HalfDown => "1.90817E+26";
                prec=15, round=Down => "1.90816500635331E+26";
                prec=30, round=Up => "190816500635331516320302656";
        );

        impl_cases!(
            pow=20 :
                prec=2, round=Down     => "3.9E+87";
                prec=2, round=HalfEven => "4.0E+87";
                prec=6, round=Down  => "3.99993E+87";
                prec=15, round=Down => "3.99993644008739E+87";
                prec=30, round=Down => "3.99993644008739657595647874758E+87";
        );
    }
}

#[cfg(not(feature = "std"))]
macro_rules! println {
    ( $( $x:expr ),* ) => {}
}

// Test that the 2 numbers are the same, assuming precision in ctx.
fn compare(bd: BigDecimal, bd_expected: BigDecimal, ctx: &Context) {
    let bd_expected_round = bd_expected.with_precision_round(ctx.precision(), ctx.rounding_mode());
    println!("100d  0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789");
    println!("exp   {}", bd_expected);
    println!("val   {}", bd);
    println!("exprd {}", bd_expected_round);

    assert_eq!(bd, bd_expected_round);
}

macro_rules! impl_case {
    ($name:ident: $start:expr, $exp:literal => $expected:literal) => {
        #[test]
        fn $name() {
            let start = BigDecimal::from($start);
            let exp = $exp;
            let expected = $expected;
            let ctx = Context::default();

            println!("Compute {}**{}", start, exp);

            let bd = start.powi_with_context(exp, &ctx);
            let bd_expected = BigDecimal::from_str(expected).unwrap();

            compare(bd, bd_expected, &ctx);
        }
    };
}

mod pow_known {
    use super::*;

    // Wolfram Alpha can get us to these precise values with a bit of log trickery, e.g.:
    // 2**3000000000 = 10**log_10(2**3000000000) = 10**(3000000000 * log_10(2))
    impl_case!(case_2_3000: 2, 3000 => "1.230231922161117176931558813276752514640713895736833715766118029160058800614672948775360067838593459582429649254051804908512884180898236823e903");
    impl_case!(case_2_2048: 2, 2048 => "3.231700607131100730071487668866995196044410266971548403213034542752465513886789089319720141152291346368871796092189801949411955915049092109e616");
    impl_case!(case_2_2001: 2, 2001 => "2.296261390548509048465666402355363968044635404177390400955285473651532522784740627713318972633012539836891929277974925546894237921726110662e602");
    impl_case!(case_2_3000000000: 2, 3000000000 => "9.8162042336235053508313854078782835648991393286913072670026492205522618203568834202759669215027003865712110468405800021098042607617495e903089986");
    // This works as 2 can be exactly inverted with only 1 digit (0.5).
    impl_case!(case_0_5_30000000: BigDecimal::from(2).inverse(), 30000000 => "1.34921314623699835510360889355448887159595110457423959780496317685705095413905406464421931122265203166201415504288117880522818881981650e-9030900");
    impl_case!(case_0_5_minus3000000000: BigDecimal::from(2).inverse(), -3000000000 => "9.8162042336235053508313854078782835648991393286913072670026492205522618203568834202759669215027003865712110468405800021098042607617495e903089986");
    impl_case!(case_2_minus30000000: 2, -30000000 => "1.34921314623699835510360889355448887159595110457423959780496317685705095413905406464421931122265203166201415504288117880522818881981650e-9030900");
    // This tests that the inverse operation carries enough digits to keep the precision.
    impl_case!(case_3_minus30000000: 3, -30000000 => "2.2824965348198962029744520058679746159742143842721452620663907608967745444344346503448190515521985159162206416095535917875712100566195e-14313638");
}

macro_rules! impl_case {
    ($name:ident: $start:expr, $exp:expr) => {
        #[test]
        fn $name() {
            let start = BigDecimal::from_str($start).unwrap();
            let exp = $exp.into();
            let ctx = Context::new(NonZeroU64::new(50).unwrap(), RoundingMode::HalfEven);
            let ctx_large = Context::new(NonZeroU64::new(500).unwrap(), RoundingMode::HalfEven);

            println!("Compute {}**{}", start, exp);

            let bd = start.powi_with_context(exp, &ctx);
            let bd_expected = start.powi_with_context(exp, &ctx_large);

            compare(bd, bd_expected, &ctx);
        }
    };
}

mod pow_misc {
    use super::*;

    // Test a few more misc values, checking that contexts with 50 or 500 precision
    // get the same number, after scaling down the 500 precision result to 50.

    impl_case!(case_misc_1: "-1.87421916986125215986", 3000912415i64);
    impl_case!(case_misc_2: "230231922161117176931558813276752514640713895736833715766118029160058800614672948775360067838593459582429649254051804908512884180898236823e903", 1000151);
    impl_case!(case_misc_3: "9.4215159218712961e-123", u32::MAX);
    impl_case!(case_misc_4: "213", 3);
    impl_case!(case_misc_5: "230231922161117176931558813276752514640713895736833715766118029160058800614672948775360067838593459582429649254051804908512884180898236823e903", -1000151);
    impl_case!(case_misc_6: "9.4215159218712961e-123", i32::MIN);
    // This test case fails without some extra margin (the number ends with 8.489 and gets rounded to 9 instead of 8)
    impl_case!(case_misc_7: "-946773878.6364634037017822265625", 4294967295i64);
}
