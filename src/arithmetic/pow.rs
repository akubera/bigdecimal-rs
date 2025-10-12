//! pow implementation

use stdlib::num::NonZeroU64;

use crate::*;

/// Compute bd**exp using exponentiation by squaring algorithm, while maintaining the
/// precision specified in ctx (the number of digits would otherwise explode).
///
/// Algorithm comes from https://en.wikipedia.org/wiki/Exponentiation_by_squaring
pub(crate) fn impl_pow_with_context(bd: &BigDecimal, exp: i64, ctx: &Context) -> BigDecimal {
    if exp == 0 {
        return 1.into();
    }

    // When performing a multiplication between 2 numbers, we may lose up to 2 digits
    // of precision.
    // "Proof": https://github.com/akubera/bigdecimal-rs/issues/147#issuecomment-2793431202
    const MARGIN_PER_MUL: u64 = 2;
    // When doing many multiplication, we still introduce additional errors, add 1 more digit
    // per 10 multiplications.
    const MUL_PER_MARGIN_EXTRA: u64 = 10;

    fn trim_precision(bd: BigDecimal, ctx: &Context, margin: u64) -> BigDecimal {
        let prec = ctx.precision().get() + margin;
        if bd.digits() > prec {
            bd.with_precision_round(NonZeroU64::new(prec).unwrap(), ctx.rounding_mode())
        } else {
            bd
        }
    }

    // Count the number of multiplications we're going to perform, one per "1" binary digit
    // in exp, and the number of times we can divide exp by 2.
    let mut n = exp.unsigned_abs();
    // Note: 63 - n.leading_zeros() == n.ilog2, but that's only available in recent Rust versions.
    let muls = (n.count_ones() + (63 - n.leading_zeros()) - 1) as u64;
    // Note: div_ceil would be nice to use here, but only available in recent Rust versions.
    let margin_extra = (muls + MUL_PER_MARGIN_EXTRA / 2) / MUL_PER_MARGIN_EXTRA;
    let mut margin = margin_extra + MARGIN_PER_MUL * muls;

    let mut bd_y: BigDecimal = 1.into();
    let mut bd_x = if exp >= 0 {
        bd.clone()
    } else {
        bd.inverse_with_context(&ctx.with_precision(
            NonZeroU64::new(ctx.precision().get() + margin + MARGIN_PER_MUL).unwrap(),
        ))
    };

    while n > 1 {
        if n % 2 == 1 {
            bd_y = trim_precision(&bd_x * bd_y, ctx, margin);
            margin -= MARGIN_PER_MUL;
            n -= 1;
        }
        bd_x = trim_precision(bd_x.square(), ctx, margin);
        margin -= MARGIN_PER_MUL;
        n /= 2;
    }
    debug_assert_eq!(margin, margin_extra);

    trim_precision(bd_x * bd_y, ctx, 0)
}

#[cfg(test)]
mod test {
    use super::*;

    include!("pow.tests.rs");
}
