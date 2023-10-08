//! Implementation of cube-root algorithm

use crate::*;
use num_bigint::BigUint;


/// implementation of cuberoot - always positive
pub(crate) fn impl_cbrt(n: &BigUint, scale: i64, ctx: &Context) -> BigDecimal {
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
        impl_division(tmp.int_val, &three, tmp.scale, max_precision + 1)
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
            running_result.with_prec(max_precision)
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
