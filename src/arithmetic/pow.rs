//! pow implementation

use stdlib::num::NonZeroU64;

use crate::*;

use super::log10;
use super::multiplication::{
    multiply_decimals_with_context,
    multiply_slices_with_prec_into_p19_z,
};

use bigdigit::digitvec::{DigitVec, DigitSlice};
use bigdigit::radix::{RadixType, RADIX_u64, RADIX_10p19_u64};
use bigdigit::endian::{Endianness, LittleEndian};

use arithmetic::multiplication::mul_scaled_slices_truncating_into;


/// Compute bd**exp using exponentiation by squaring algorithm, while maintaining the
/// precision specified in ctx (the number of digits would otherwise explode).
///
/// Algorithm comes from https://en.wikipedia.org/wiki/Exponentiation_by_squaring
pub(crate) fn impl_powi_with_context<'a>(
    bd: impl Into<BigDecimalRef<'a>>,
    exp: i64,
    ctx: &Context,
) -> BigDecimal {
    use crate::bigdigit::radix::RadixPowerOfTen;
    type R = RADIX_10p19_u64;

    if exp == 0 {
        return 1.into();
    }

    let bd = bd.into();

    // When performing a multiplication between 2 numbers, we may lose up to 2 digits
    // of precision.
    // "Proof": https://github.com/akubera/bigdecimal-rs/issues/147#issuecomment-2793431202
    const MARGIN_PER_MUL: u64 = 2;
    // When doing many multiplication, we still introduce additional errors, add 1 more digit
    // per 10 multiplications.
    const MUL_PER_MARGIN_EXTRA: u64 = 10;

    // Count the number of multiplications we're going to perform, one per "1" binary digit
    // in exp, and the number of times we can divide exp by 2.
    let mut n = exp.abs() as u64;
    // Note: 63 - n.leading_zeros() == n.ilog2, but that's only available in recent Rust versions.
    let muls = (n.count_ones() + (63 - n.leading_zeros()) - 1) as u64;
    let margin_extra = num_integer::div_ceil(muls, MUL_PER_MARGIN_EXTRA);
    let margin = margin_extra + MARGIN_PER_MUL * muls;

    let bigdigit_prec = R::divceil_digit_count(ctx.precision().get() as usize) as u64 + 1;

    if exp < 0 {
        let invert_prec = NonZeroU64::new(ctx.precision().get() + margin + MARGIN_PER_MUL).unwrap();
        let invert_bd = bd.inverse_with_context(&ctx.with_precision(invert_prec));
        return impl_powi_with_context(&invert_bd, exp.neg(), ctx);
    };

    let mut tmp = Vec::new();
    let bd_as_base10p19 = DigitVec::from_biguint_using_tmp(bd.digits, &mut tmp);
    tmp.clear();

    let mut y_vec = Vec::with_capacity(bd_as_base10p19.len());
    y_vec.push(1);

    let mut digits_x = WithScale { value: bd_as_base10p19, scale: 0 };
    let mut digits_y = WithScale { value: DigitVec::from_vec(y_vec), scale: 0 };
    let mut prod = WithScale { value: DigitVec::from_vec(tmp), scale: 0 };

    // estimation of number of RADIX-base bigdigits are in the bigdecimal
    let bd_log_base = match bd.to_f64() {
        Some(f) if f.is_normal() => log10(f) / (R::DIGITS as f64),
        _ => {
            // overestimate by just counting bits
            let log2_ceil = bd.digits.bits() + 1;
            log2_ceil as f64 / (R::DIGITS as f64 * LOG2_10)
        }
    };

    // factor product into bdⁿ => bdˣ·bdʸ where x is largest
    // power of two which fits into 'n'
    let final_x_pow = 1 << (63 - n.leading_zeros() as u64);
    let final_y_pow = n - final_x_pow;

    let estimated_final_y = bd_log_base * final_y_pow as f64;
    let max_digit_sum_width = (
        2.0 * log10(R::max() as f64) + log10(estimated_final_y)
    ).ceil() as usize;

    let margin_per_mul = max_digit_sum_width as u64 + 2;
    let mut margin = (muls + 1) * margin_per_mul + bigdigit_prec;

    // disable calculation of trailing zeros for rounding
    let mut trailing_zeros = true;

    while n > 1 {
        if n % 2 == 1 {
            let skipped_bigdigit_count = mul_scaled_slices_truncating_into(
                &mut prod, digits_y.as_digit_slice(), digits_x.as_digit_slice(), margin
            );
            trailing_zeros = trailing_zeros
                && {
                    let skipped = skipped_bigdigit_count.saturating_sub(digits_y.value.len() - 1);
                    digits_x.value.iter_le().take(skipped).all(Zero::is_zero)
                }
                && {
                    let skipped = skipped_bigdigit_count.saturating_sub(digits_x.value.len() - 1);
                    digits_y.value.iter_le().take(skipped).all(Zero::is_zero)
                };
            stdlib::mem::swap(&mut prod, &mut digits_y);
            margin -= margin_per_mul;
            n -= 1;
        }
        // TODO: optimized algorithm for squaring a scaled digitslice to requested precision
        let skipped_bigdigits = mul_scaled_slices_truncating_into(
            &mut prod, digits_x.as_digit_slice(), digits_x.as_digit_slice(), margin
        );
        // detect if truncated digits were non-zero
        trailing_zeros = trailing_zeros
            && {
                let skipped = skipped_bigdigits.saturating_sub(digits_x.value.len() - 1);
                digits_x.value.iter_le().take(skipped).all(Zero::is_zero)
            };

        // store 'prod' in 'digits_x'
        stdlib::mem::swap(&mut prod, &mut digits_x);

        margin -= margin_per_mul;
        n /= 2;
    }
    // debug_assert_eq!(margin, margin_extra);

    let sign = if exp % 2 == 0 {
        Sign::Plus
    } else {
        bd.sign()
    };
    let rounding = crate::rounding::NonDigitRoundingData {
        mode: ctx.rounding_mode(),
        sign: sign,
    };

    prod.value.clear();
    prod.scale = 0;

    multiply_slices_with_prec_into_p19_z(
        &mut prod,
        digits_x.value.as_digit_slice(),
        digits_y.value.as_digit_slice(),
        ctx.precision(),
        rounding,
        trailing_zeros,
    );

    let scale = bd.scale * exp + prod.scale + (digits_x.scale + digits_y.scale) * R::DIGITS as i64;
    let int_val = BigInt::from_biguint(sign, prod.value.into_biguint());

    BigDecimal::new(int_val, scale)
}

#[cfg(test)]
mod test {
    use super::*;

    include!("pow.tests.rs");
}
