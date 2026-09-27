//! Routines for implementing division
//!

use crate::*;

pub(crate) fn scaled_uint_division_into<'a, N, D>(
    dest: &mut WithScale<BigUint>,
    num: N,
    den: D,
    max_precision_bits: u64,
)
where
    N: Into<WithScale<&'a BigUint>>,
    D: Into<WithScale<&'a BigUint>>,
{
    impl_scaled_uint_division_into(dest, num.into(), den.into(), max_precision_bits);
}

/// implement `dest = num / den`, limiting the precision to given number of bits
pub(crate) fn impl_scaled_uint_division_into(
    dest: &mut WithScale<BigUint>,
    num: WithScale<&BigUint>,
    den: WithScale<&BigUint>,
    max_precision_bits: u64,
) {
    debug_assert!(!den.value.is_zero());

    if num.value.is_zero() {
        dest.value = num.value.clone();
        dest.scale = num.scale - den.scale;
        return;
    }

    if den.value.is_one() && den.scale == 0 {
        return;
    }

    let WithScale { value: num, scale: num_scale } = num;
    let WithScale { value: den, scale: den_scale } = den;

    // populate dest with scaled numerator (larger than denominator)
    match den.bits().checked_sub(num.bits()) {
        None => {
            dest.scale = num_scale - den_scale;
            dest.value = num.clone();
        }
        Some(0) => {
            dest.scale = num_scale - den_scale + 1;
            dest.value = num * 10u8;
        }
        Some(diff) => {
            let digit_count = bit_to_digit_count(diff);
            dest.scale = num_scale - den_scale + digit_count as i64;
            dest.value = BigUint::from(10u8).pow(digit_count);
            dest.value *= num;
        }
    }

    let (quotient, mut remainder) = dest.value.div_rem(den);

    dest.value = quotient;

    // precision of results in bits
    let mut precision_bits = dest.bits();

    // increase precision 'step-scale' digits at a time
    let step_scale = 1i64;
    let step_factor = 10u64.pow(step_scale as u32);

    // shift remainder by 2 decimal;
    // quotient will be at most 'step-scale' digit upon next div_rem
    remainder *= step_factor;

    while !remainder.is_zero() && precision_bits < max_precision_bits {
        let (q, r) = remainder.div_rem(den);
        dest.scale += step_scale;
        dest.value *= step_factor;
        dest.value += q;
        precision_bits = dest.bits();
        remainder = r * step_factor;
    }

    let excess_u64_count = precision_bits.saturating_sub(max_precision_bits) / 64;

    // Trim some excess precision from the division
    for _ in 1..excess_u64_count {
        dest.value /= 1_0000000000000000000u64;
        dest.scale -= 19;
    }
}
