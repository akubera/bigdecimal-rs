//! pow implementation

use stdlib::num::NonZeroU64;

use crate::*;

use super::log10;
use super::multiplication::{
    multiply_decimals_with_context,
    multiply_slices_with_prec_into_p19_z,
};

use bigdigit::digitvec::{DigitVec, DigitSlice};
use bigdigit::radix::{RadixType, RadixPowerOfTen, RADIX_u64, RADIX_10p19_u64};
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
    powi_with_context(bd.into(), exp, ctx)
}

/// Calculate BigDecimalRef `bd` to power of signed integer, using context
/// to set precision
fn powi_with_context(
    bd: BigDecimalRef,
    exp: i64,
    ctx: &Context,
) -> BigDecimal {
    match exp.cmp(&0) {
        Ordering::Equal => BigDecimal::one(),
        Ordering::Greater => pow_u64_with_context(bd, exp as u64, ctx),
        Ordering::Less => {
            if exp == -1 {
                return bd.inverse_with_context(&ctx);
            }
            // create truncating "double wide" context for inverting
            let inv_ctx = Context::new_truncating(
                (ctx.precision().get() * 2)
                .max((bd.digits.bits() as f64 * LOG10_2 * 2.0).ceil() as u64)
                .max(38) // always at least 2 u64 'big-digits' wide
            );
            let inverted_bd = bd.inverse_with_context(&inv_ctx);
            // requested context when taking the power of inverted value
            pow_u64_with_context(inverted_bd.to_ref(), unsigned_abs(exp), &ctx)
        }
    }
}


/// Calculate BigDecimalRef `bd` to power of positive integer, using context
/// to set precision
///
/// The case where exp==0 (therefore result is 1) must be handled
/// before calling this pow impl
fn pow_u64_with_context(
    bd: BigDecimalRef,
    exp: u64,
    ctx: &Context,
) -> BigDecimal {
    type R = RADIX_10p19_u64;

    debug_assert_ne!(exp, 0);

    if exp == 1 {
        return ctx.round_decimal_ref(bd);
    }

    // bd^exp guaranteed to fit within precision: use roundless pow
    if (bd.digits.bits() as f64 * exp as f64) < (ctx.precision().get() as f64 * LOG2_10) {
        return pow_u64_no_context(bd, exp);
    }

    let mut tmp = Vec::new();
    let bd_as_base10p19 = DigitVec::from_biguint_using_tmp(bd.digits, &mut tmp);
    debug_assert_eq!(tmp.len(), 0);

    let mut prec = RunningPrecision::new(
        bd_as_base10p19.as_digit_slice(),
        NonZeroU64::new(exp).unwrap(),
        ctx.precision(),
    );

    // Count the number of multiplications we're going to perform, one per "1" binary digit
    // in exp, and the number of times we can divide exp by 2.
    let mut n = exp;

    // factor product into bdⁿ => bdˣ·bdʸ where x is largest
    // power of two which fits into 'n'
    let final_x_pow = 1 << (63 - n.leading_zeros() as u64);
    let final_y_pow = n - final_x_pow;

    // if final_y_pow == 0, then 'y' digits is never used and
    // we will use x*x as final multiplication, otherwise
    // final product is x*y
    let final_x_times_y = final_y_pow != 0;

    let mut y_vec = Vec::new();
    if final_x_times_y {
        y_vec.reserve(bd_as_base10p19.len());
        y_vec.push(1);
    } else {
        // no final multiplication by y, so decrease number of squarings
        // by one so we do (x/2 * x/2) rather than (x * 1)
        n >>= 1;
    }

    let mut digits_x = WithScale {
        value: bd_as_base10p19,
        scale: 0,
    };
    let mut digits_y = WithScale {
        value: DigitVec::from_vec(y_vec),
        scale: 0,
    };
    // temporary storage for results of multiplications
    let mut prod = WithScale {
        value: DigitVec::from_vec(tmp),
        scale: 0,
    };

    // tracks if skipped insignificant digits are zero for final rounding
    let mut trailing_zeros = true;

    while n > 1 {
        if n % 2 == 1 {
            // 'prod' is now product y * x, swap with 'y'
            let skipped_bigdigit_count = mul_scaled_slices_truncating_into(
                &mut prod,
                digits_y.as_digit_slice(),
                digits_x.as_digit_slice(),
                prec.next(),
            );

            trailing_zeros = trailing_zeros
                && {
                    let skipped = skipped_bigdigit_count.saturating_sub(digits_y.value.len() - 1);
                    digits_x.value.least_n_are_zero(skipped)
                }
                && {
                    let skipped = skipped_bigdigit_count.saturating_sub(digits_x.value.len() - 1);
                    digits_y.value.least_n_are_zero(skipped)
                };

            // now 'digits_y <- prod = digits_y * digits_x'
            stdlib::mem::swap(&mut prod, &mut digits_y);
        }
        // TODO: optimized algorithm for squaring a scaled digitslice to requested precision
        let skipped_bigdigits = mul_scaled_slices_truncating_into(
            &mut prod,
            digits_x.as_digit_slice(),
            digits_x.as_digit_slice(),
            prec.next(),
        );
        // detect if truncated digits were non-zero
        trailing_zeros = trailing_zeros
            && {
                let skipped = skipped_bigdigits.saturating_sub(digits_x.value.len() - 1);
                digits_x.value.least_n_are_zero(skipped)
            };

        // digits_x <- prod = digits_x * digits_x
        stdlib::mem::swap(&mut prod, &mut digits_x);

        // shift lowest bit out of multiplication counter
        n >>= 1;
    }

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

    let x_slice = digits_x.value.as_digit_slice();

    let y_slice = if final_x_times_y {
        digits_y.value.as_digit_slice()
    } else {
        // raised to a power-of-two: y-slice was never touched so
        // we reuse x-slice here for final multiplication
        debug_assert_eq!(digits_y.value.digits.capacity(), 0);
        digits_y.scale = digits_x.scale;
        x_slice
    };

    multiply_slices_with_prec_into_p19_z(
        &mut prod,
        x_slice,
        y_slice,
        ctx.precision(),
        rounding,
        trailing_zeros,
    );

    let mut scale = bd.scale * exp as i64 + prod.scale;
    scale += (digits_x.scale + digits_y.scale) * R::DIGITS as i64;

    let int_val = BigInt::from_biguint(sign, prod.value.into_biguint());

    BigDecimal::new(int_val, scale)
}

/// Simple implementation of exponentiation-by-squaring,
/// with no precision/rounding involved
fn pow_u64_no_context(bd: BigDecimalRef, exp: u64) -> BigDecimal {
    debug_assert_ne!(exp, 0);
    if exp == 1 {
        return bd.to_owned();
    }

    let mut x = bd.digits.clone();
    let mut y: BigUint = 1u8.into();

    let mut n = exp;
    while n > 1 {
        if n % 2 == 1 {
            y *= &x;
        }
        x = x.pow(2u8);
        n >>= 1;
    }

    // final product
    let p = x * y;

    let sign = if exp % 2 == 0 {
        Sign::Plus
    } else {
        bd.sign()
    };

    let scale = bd.scale * exp as i64;
    let int_val = BigInt::from_biguint(sign, p);

    BigDecimal::new(int_val, scale)
}

#[cfg(not(has_unsigned_abs))]
fn unsigned_abs(n: i64) -> u64 {
    if n != i64::MIN {
        n.abs() as u64
    } else {
        (i64::MIN as i128).abs() as u64
    }
}

#[cfg(has_unsigned_abs)]
#[allow(clippy::incompatible_msrv)]
fn unsigned_abs(n: i64) -> u64 {
    n.unsigned_abs()
}

/// Struct housing the 'margin' information for calculating the required
/// precision while doing sequential multiplications for pow
///
/// Currently uses a naive scheme: calculating the widest required
/// margin, and multiplying the number of multiplications by that width.
/// Then we linearly decrease the margin so we end up near the requested
/// precision by the time we get to the final product.
///
struct RunningPrecision {
    /// Minimum precision
    min: u64,
    /// Current margin
    margin: u64,
    /// number of digits to decrease each time `next()` is called
    margin_per_mul: u64,
}

impl RunningPrecision {
    /// Create from requiring 'prec' digits of precision of digits^exp
    fn new<'a, R: RadixPowerOfTen, E: Endianness>(
        digits: DigitSlice<'a, R, E>,
        exp: NonZeroU64,
        prec: NonZeroU64,
    ) -> Self {
        // number of big-digits required to fit requested precision, plus a few
        // extra for guaranteed rounding digits
        let prec_bigdigit_count = R::divceil_digit_count(prec.get() as usize + 3) as u64;

        // length of 'digits' in big digits (floating-point)
        let digit_count_f = digits.count_decimal_digits() as f64 ;

        let count_squarings = 63 - exp.get().leading_zeros();
        let count_non_squarings = exp.get().count_ones() - 1;
        // total number of multiplications
        let muls = (count_non_squarings + count_squarings) as u64;

        // aⁿ => aˣ·aʸ, n = x+y
        let max_partial_pow = {
            let x = 1 << count_squarings;
            let y = exp.get() - x;
            (x / 2).max(y)
        };

        // number of digits of multiplicand in the final product
        let max_width_digits_f = digit_count_f * max_partial_pow as f64;

        // length in digits of kmaximum sum of digits
        let diag_sum_digit_len = 2.0 * log10(R::max().to_f64().unwrap()) + log10(max_width_digits_f);
        let diag_sum_bigdigit_len = R::divceil_digit_count(diag_sum_digit_len.ceil() as usize) as u64;
        let margin_per_mul = diag_sum_bigdigit_len + 1;

        Self {
            min: prec_bigdigit_count,
            margin: (muls + 1) * margin_per_mul,
            margin_per_mul: margin_per_mul,
        }
    }

    /// update margin and return precision
    fn next(&mut self) -> u64 {
        self.margin = self.margin.saturating_sub(self.margin_per_mul);
        self.margin + self.min
    }
}

#[cfg(test)]
mod test {
    use super::*;

    include!("pow.tests.rs");
}
