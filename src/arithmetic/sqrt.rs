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
            &r.int_val.magnitude(),
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
    fn case_sqrt_3242053850483855em13() {
        let d: BigDecimal = "324.2053850483855".parse().unwrap();

        let digitref = d.to_ref();
        let (_, scale, uint) = digitref.as_parts();
        // let prec = NonZeroUsize::new(11);
        // let ctx = Context::new(prec.unwrap(), RoundingMode::Up);
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
}
