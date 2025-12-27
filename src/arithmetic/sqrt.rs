//! square root implementation

use crate::*;


pub(crate) fn impl_sqrt(n: &BigUint, scale: i64, ctx: &Context) -> BigDecimal {
    // Calculate the number of digits and the difference compared to the scale
    let num_digits = count_decimal_digits_uint(n);
    let scale_diff = BigInt::from(num_digits) - scale;

    // Calculate the number of wanted digits and the exponent we need to raise the original value to
    // We want twice as many digits as the precision because sqrt halves the number of digits
    // We add an extra one for rounding purposes
    let prec = ctx.precision().get();
    let extra_rounding_digit_count = 5;
    let wanted_digits = 2 * (prec + extra_rounding_digit_count);
    let exponent = wanted_digits.saturating_sub(num_digits) + u64::from(scale_diff.is_odd());
    let sqrt_digits = (n * ten_to_the_uint(exponent)).sqrt();

    // Calculate the scale of the result
    let result_scale_digits = 2 * (2 * prec - scale_diff) - 1;
    let result_scale_decimal: BigDecimal = BigDecimal::new(result_scale_digits, 0) / 4.0;
    let mut result_scale = result_scale_decimal.with_scale_round(0, RoundingMode::HalfEven).int_val;

    // Round the value so it has the correct precision requested
    result_scale += count_decimal_digits_uint(&sqrt_digits).saturating_sub(prec);
    let unrounded_result = BigDecimal::new(sqrt_digits.into(), result_scale.to_i64().unwrap());
    unrounded_result.with_precision_round(ctx.precision(), ctx.rounding_mode())
}

#[cfg(test)]
mod test {
    use super::*;

    include!("sqrt.tests.rs");
}
