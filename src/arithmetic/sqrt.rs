//! square root implementation

use crate::*;


fn impl_division(mut num: BigUint, den: &BigUint, mut scale: i64, max_precision: u64) -> BigDecimal {
    use Sign::Plus;

    // quick zero check
    if num.is_zero() {
        return BigDecimal::new(BigInt::from_biguint(Plus, num), 0);
    }

    // shift digits until numerator is larger than denominator (set scale appropriately)
    while num < *den {
        scale += 1;
        num *= 10u8;
    }

    // first division
    let (mut quotient, mut remainder) = num.div_rem(den);

    // division complete
    if remainder.is_zero() {
        return BigDecimal {
            int_val: BigInt::from_biguint(Plus, quotient),
            scale: scale,
        };
    }

    let mut precision = count_decimal_digits_uint(&quotient);

    // shift remainder by 1 decimal;
    // quotient will be 1 digit upon next division
    remainder *= 10u8;

    while !remainder.is_zero() && precision < max_precision {
        let (q, r) = remainder.div_rem(den);
        quotient = quotient * 10u8 + q;
        remainder = r * 10u8;

        precision += 1;
        scale += 1;
    }

    if !remainder.is_zero() {
        // round final number with remainder
        quotient += get_rounding_term_uint(&remainder.div(den));
    }

    BigDecimal::new(BigInt::from_biguint(Plus, quotient), scale)
}

fn get_rounding_term_uint(num: &BigUint) -> u8 {
    if num.is_zero() {
        return 0;
    }

    let digits = (num.bits() as f64 / LOG2_10) as u64;
    let mut n = ten_to_the_uint(digits);

    // loop-method
    loop {
        if *num < n {
            return 1;
        }
        n *= 5u8;
        if *num < n {
            return 0;
        }
        n *= 2u8;
    }

    // string-method
    // let s = format!("{}", num);
    // let high_digit = u8::from_str(&s[0..1]).unwrap();
    // if high_digit < 5 { 0 } else { 1 }
}

pub(crate) fn impl_sqrt(n: &BigUint, scale: i64, ctx: &Context) -> BigDecimal {
    // make guess
    let guess = {
        let magic_guess_scale = 1.1951678538495576_f64;
        let initial_guess = (n.bits() as f64 - scale as f64 * LOG2_10) / 2.0;
        let res = magic_guess_scale * exp2(initial_guess);

        if res.is_normal() {
            BigDecimal::try_from(res).unwrap()
        } else {
            // can't guess with float - just guess magnitude
            let scale = (n.bits() as f64 / -LOG2_10 + scale as f64).round() as i64;
            BigDecimal::new(BigInt::from(1), scale / 2)
        }
    };

    // // wikipedia example - use for testing the algorithm
    // if self == &BigDecimal::from_str("125348").unwrap() {
    //     running_result = BigDecimal::from(600)
    // }

    // TODO: Use context variable to set precision
    let max_precision = ctx.precision().get();

    let next_iteration = move |r: BigDecimal| {
        // division needs to be precise to (at least) one extra digit
        let tmp = impl_division(
            n.clone(),
            r.int_val.magnitude(),
            scale - r.scale,
            max_precision + 1,
        );

        // half will increase precision on each iteration
        (tmp + r).half()
    };

    // calculate first iteration
    let mut running_result = next_iteration(guess);

    let mut prev_result = BigDecimal::one();
    let mut result = BigDecimal::zero();

    // TODO: Prove that we don't need to arbitrarily limit iterations
    // and that convergence can be calculated
    while prev_result != result {
        // store current result to test for convergence
        prev_result = result;

        // calculate next iteration
        running_result = next_iteration(running_result);

        // 'result' has clipped precision, 'running_result' has full precision
        result = if running_result.digits() > max_precision {
            running_result.with_prec(max_precision)
        } else {
            running_result.clone()
        };
    }

    result
}


#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_sqrt() {
        let vals = vec![
            ("1e-232", "1e-116"),
            ("1.00", "1"),
            ("1.001", "1.000499875062460964823258287700109753027590031219780479551442971840836093890879944856933288426795152"),
            ("100", "10"),
            ("49", "7"),
            (".25", ".5"),
            ("0.0152399025", ".12345"),
            ("152399025", "12345"),
            (".00400", "0.06324555320336758663997787088865437067439110278650433653715009705585188877278476442688496216758600590"),
            (".1", "0.3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295"),
            ("2", "1.414213562373095048801688724209698078569671875376948073176679737990732478462107038850387534327641573"),
            ("125348", "354.0451948551201563108487193176101314241016013304294520812832530590100407318465590778759640828114535"),
            ("18446744073709551616.1099511", "4294967296.000000000012799992691725492477397918722952224079252026972356303360555051219312462698703293"),
            ("3.141592653589793115997963468544185161590576171875", "1.772453850905515992751519103139248439290428205003682302442979619028063165921408635567477284443197875"),
            (".000000000089793115997963468544185161590576171875", "0.000009475922962855041517561783740144225422359796851494316346796373337470068631250135521161989831460407155"),
            ("0.7177700109762963922745342343167413624881759290454997218753321040760896053150388903350654937434826216803814031987652326749140535150336357405672040727695124057298138872112244784753994931999476811850580200000000000000000000000000000000", "0.8472130847527653667042980517799020703921106560594525833177762276594388966885185567535692987624493813"),
            ("0.01234567901234567901234567901234567901234567901234567901234567901234567901234567901234567901234567901", "0.1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111"),
            ("0.1108890000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000444", "0.3330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000667"),
        ];
        for &(x, y) in vals.iter() {
            let a = BigDecimal::from_str(x).unwrap().sqrt().unwrap();
            let b = BigDecimal::from_str(y).unwrap();
            assert_eq!(a, b);
        }
    }

    #[test]
    fn test_big_sqrt() {
        use num_bigint::BigInt;
        let vals = vec![
            (("2", -70), "141421356237309504880168872420969807.8569671875376948073176679737990732478462107038850387534327641573"),
            (("3", -170), "17320508075688772935274463415058723669428052538103806280558069794519330169088000370811.46186757248576"),
            (("9", -199), "9486832980505137995996680633298155601158665417975650480572514558377783315917714664032744325137900886"),
            (("7", -200), "26457513110645905905016157536392604257102591830824501803683344592010688232302836277603928864745436110"),
            (("777", -204), "2.787471972953270789531596912111625325974789615194854615319795902911796043681078997362635440358922503E+103"),
            (("7", -600), "2.645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543611E+300"),
            (("2", -900), "1.414213562373095048801688724209698078569671875376948073176679737990732478462107038850387534327641573E+450"),
            (("7", -999), "8.366600265340755479781720257851874893928153692986721998111915430804187725943170098308147119649515362E+499"),
            (("74908163946345982392040522594123773796", -999), "2.736935584670307552030924971360722787091742391079630976117950955395149091570790266754718322365663909E+518"),
            (("20", -1024), "4.472135954999579392818347337462552470881236719223051448541794490821041851275609798828828816757564550E512"),
            (("3", 1025), "5.477225575051661134569697828008021339527446949979832542268944497324932771227227338008584361638706258E-513"),
        ];
        for &((s, scale), e) in vals.iter() {
            let expected = BigDecimal::from_str(e).unwrap();

            let sqrt = BigDecimal::new(BigInt::from_str(s).unwrap(), scale).sqrt().unwrap();
            assert_eq!(sqrt, expected);
        }
    }

    #[test]
    fn case_sqrt_3242053850483855em13() {
        let d: BigDecimal = "324.2053850483855".parse().unwrap();

        let digitref = d.to_ref();
        let (_, scale, uint) = digitref.as_parts();
        let ctx = Context::default()
                          .with_prec(11).unwrap()
                          .with_rounding_mode(RoundingMode::Down);

        let s = impl_sqrt(uint, scale, &ctx);
        let expected: BigDecimal = "18.005704236".parse().unwrap();
        assert_eq!(s, expected);

        let ctx = Context::default()
                          .with_prec(31).unwrap()
                          .with_rounding_mode(RoundingMode::Up);

        let s = impl_sqrt(uint, scale, &ctx);
        let expected: BigDecimal = "18.00570423639090823994825477228".parse().unwrap();
        assert_eq!(s, expected);
    }

    #[test]
    fn case_sqrt_5085019992340351em25() {
        let d: BigDecimal = "5.085019992340351e-10".parse().unwrap();

        let digitref = d.to_ref();
        let (_, scale, uint) = digitref.as_parts();
        let ctx = Context::default()
                          .with_prec(25).unwrap()
                          .with_rounding_mode(RoundingMode::Down);

        let s = impl_sqrt(uint, scale, &ctx);
        let expected: BigDecimal = "0.00002254998889653906459324292".parse().unwrap();
        assert_eq!(s, expected);
    }

    #[cfg(property_tests)]
    mod prop {
        use super::*;
        use proptest::*;
        use num_traits::FromPrimitive;

        proptest! {
            #[test]
            fn sqrt_of_square_is_self(f: f64, prec in 15..50u64) {
                // ignore non-normal numbers
                prop_assume!(f.is_normal());

                let n = BigDecimal::from_f64(f.abs()).unwrap().with_prec(prec);
                let n_squared = n.square();
                let x = n_squared.sqrt().unwrap();
                prop_assert_eq!(x, n);
            }
        }
    }
}
