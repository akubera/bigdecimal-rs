//! Implementation of cube-root algorithm

use crate::*;
use num_bigint::BigUint;


/// implementation of cuberoot - always positive
pub(crate) fn impl_cbrt_uint_scale(n: &BigUint, scale: i64, ctx: &Context) -> BigDecimal {
    // make guess based on number of bits in the number
    let guess = make_cbrt_guess(n.bits(), scale);

    let three = BigInt::from(3);

    let n = BigInt::from_biguint(Sign::Plus, n.clone());

    let max_precision = ctx.precision().get();

    let next_iteration = move |r: BigDecimal| {
        let sqrd = r.square();
        let tmp = impl_division(
            n.clone(),
            &sqrd.int_val,
            scale - sqrd.scale,
            max_precision + 1,
        );
        let tmp = tmp + r.double();
        impl_division(tmp.int_val, &three, tmp.scale, max_precision + 3)
    };

    // result initial
    let mut running_result = next_iteration(guess);

    let mut prev_result = BigDecimal::one();
    let mut result = BigDecimal::zero();

    // TODO: Prove that we don't need to arbitrarily limit iterations
    // and that convergence can be calculated
    while prev_result != result {
        // store current result to test for convergence
        prev_result = result;

        running_result = next_iteration(running_result);

        // result has clipped precision, running_result has full precision
        result = if running_result.digits() > max_precision {
            running_result.with_precision_round(ctx.precision(), ctx.rounding_mode())
        } else {
            running_result.clone()
        };
    }

    return result;
}

/// Find initial cbrt guess based on number of bits in integer and the scale
///
/// ```math
/// 2^bit_count * 10^-scale <= *n* < 2^(bit_count+1) * 10^-scale
///
/// cbrt(n2^bit_count * 10^-scale)
/// cbrt(2^bit_count * 10^-scale)
///    => Exp2[1/3 * Log2[2^bit_count * 10^-scale]]
///    => Exp2[1/3 * (bit_count - scale * Log2[10]]
/// ```
///
fn make_cbrt_guess(bit_count: u64, scale: i64) -> BigDecimal {
    // weight of cube root average above minimum within range: 3/4*2^(4/3)
    let magic_guess_scale = 1.1398815748423097_f64;

    let bit_count = bit_count as f64;
    let scale = scale as f64;

    let initial_guess = (bit_count - scale * LOG2_10) / 3.0;
    let res = magic_guess_scale * exp2(initial_guess);

    match BigDecimal::try_from(res) {
        Ok(res) => res,
        Err(_) => {
            // can't guess with float - just guess magnitude
            let scale = (scale - bit_count / LOG2_10).round() as i64;
            BigDecimal::new(BigInt::from(1), scale / 3)
        }
    }
}


#[cfg(test)]
mod test {
    use super::*;
    use stdlib::num::NonZeroU64;

    #[test]
    fn test_cbrt() {
        let vals = vec![
            ("0.00", "0"),
            ("1.00", "1"),
            ("1.001", "1.000333222283909495175449559955220102010284758197360454054345461242739715702641939155238095670636841"),
            ("10", "2.154434690031883721759293566519350495259344942192108582489235506346411106648340800185441503543243276"),
            ("13409.179789484375", "23.7575"),
            ("-59283293e25", "-84006090355.84281237113712383191213626687332139035750444925827809487776780721673264524620270275301685"),
            ("94213372931e-127", "2.112049945275324414051072540210070583697242797173805198575907094646677475250362108901530353886613160E-39"),
        ];
        for &(x, y) in vals.iter() {
            let a = BigDecimal::from_str(x).unwrap().cbrt();
            let b = BigDecimal::from_str(y).unwrap();
            assert_eq!(a, b);
        }
    }


    #[test]
    fn test_cbrt_prec15() {
        let vals = vec![
            ("0.00", "0"),
            ("1.00", "1"),
            ("1.001", "1.00033322228390"),
            ("10", "2.15443469003188"),
            ("13409.179789484375", "23.7575"),
            ("-59283293e25", "-84006090355.8428"),
            ("94213372931e-127", "2.11204994527532E-39"),
        ];

        let ctx = Context::new(NonZeroU64::new(15).unwrap(), RoundingMode::Down);

        for &(x, y) in vals.iter() {
            let a = BigDecimal::from_str(x).unwrap().cbrt_with_context(&ctx);
            let b = y.parse().unwrap();
            assert_eq!(a, b);
        }
    }

    #[cfg(property_tests)]
    mod prop {
        use super::*;
        use proptest::*;
        use num_traits::FromPrimitive;

        proptest! {
            #[test]
            fn cbrt_of_cube_is_self(f: f64, prec in 15..50u64) {
                // ignore non-normal numbers
                prop_assume!(f.is_normal());

                let n = BigDecimal::from_f64(f).unwrap().with_prec(prec);
                let n_cubed = n.cube();
                let x = n_cubed.cbrt();
                prop_assert_eq!(x, n);
            }
        }
    }
}
