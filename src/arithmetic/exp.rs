//! All the routines for calculating exp(x)
//!

use crate::*;
use super::*;


/// Calculate e^n
pub(crate) fn impl_exp(n: BigDecimalRef, ctx: &Context) -> BigDecimal {
    use arithmetic::division::scaled_uint_division_into;
    use arithmetic::inverse::impl_inverse_uint_scale;

    if n.is_zero() {
        return BigDecimal::one();
    }

    // n ~= x * 2^k
    let (x, k) = factor_two_to_k_scale(WithScale { value: n.digits, scale: n.scale });

    let target_precision = ctx.precision().get();
    let target_precision_bits = digit_to_bit_count(target_precision) + k as u64;

    let mut num = x.clone();
    let mut den = WithScale { value: 1u8.into(), scale: 0 };

    // sum = 1 + x
    let mut sum = WithScale { value: 1u8.into(), scale: 0 };
    addition::addassign_scaled_biguint(&mut sum, num.as_ref());

    // we should have form `1.xxxxx` so only one digit is integer part
    debug_assert_eq!(sum.count_int_digits(), 1);

    let mut delta: WithScale<BigUint> = Default::default();

    // assuming linear convergence, should break after N; we loop
    // through 2*N for safety
    let stop = target_precision * 2;

    for i in 2..stop {
        // each loop iteration:
        //    num = x^i
        //    den = factorial(i)
        //    delta = num / den
        //    sum += delta
        num.mulassign_scaled_biguint(&x);
        den.value *= i;
        remove_trailing_zeros(&mut den, &[1]);
        scaled_uint_division_into(&mut delta, &num, &den, target_precision_bits - i);
        sum.addassign_scaled_biguint(&delta);

        // we have converged if number of leading zeros in delta is
        // larger than the target precision
        let leading_zero_count = delta.count_int_digits().neg();
        if leading_zero_count > target_precision as i64 {
            break;
        }
    }

    // reuse 'delta' as scratchpad
    let mut tmp = delta.value;

    // at this point: sum = exp(n / 2^k)
    //
    // we now square it 'k' times to get final result
    arithmetic::pow::pow_2_k_scaled_biguint(
        &mut sum, &mut tmp, k, target_precision_bits
    );

    if n.sign == Sign::Minus {
        let result = BigDecimal::from(sum).with_prec(target_precision * 2);
        return result.inverse_with_context(&ctx);
    } else {
        return BigDecimal::from(sum).with_prec(target_precision);
    }
}

/// Factor scaled biguint by 2^k
///
/// Returns pair of sacled-BigUint in range [0.0, 0.5] and 'k', the
/// number of times to square the BigUint to return the number to
/// the original value.
///
fn factor_two_to_k_scale(n: WithScale<&BigUint>) -> (WithScale<BigUint>, u16) {
    let log2_n = n.value.bits() as f64;
    let log2_s = (n.scale as f64) * LOG2_10;
    let k = 1.0 + log2_n - log2_s;
    if k <= 0.5 {
        let r = n.value.clone();
        return ((r, n.scale).into(), 0);
    }

    let k = k.ceil() as u64;
    let mut x = BigUint::from(5u8).pow(k);
    x *= n.value;

    let mut result = WithScale {
        value: x,
        scale: n.scale + k as i64,
    };

    // strip trailing zeros at different speeds (last one must be '1')
    remove_trailing_zeros(&mut result, &[8, 1]);

    (result, k.as_())
}

/// Remove trailing zeros by divmoding n by given powers of ten
///
/// Multiple powers may be chosen to speed up removal (should end with '1'
/// to remove all zero, i.e. mod-10)
///
fn remove_trailing_zeros<'a>(
    n: &mut WithScale<BigUint>,
    powers: impl IntoIterator<Item=&'a u8>,
) {
    for &i in powers.into_iter() {
        debug_assert!(i < 20);

        let s = 10u64.pow(i as u32);
        while (&n.value % s).is_zero() {
            n.value /= s;
            n.scale -= i as i64;
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    include!("exp.tests.rs");
}
