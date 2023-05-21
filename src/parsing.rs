//! Routines for parsing values into BigDecimals

use super::{BigDecimal, ParseBigDecimalError};

use num_bigint::{BigInt, BigUint, Sign};


/// Try creating bigdecimal from f32
///
/// Non "normal" values will return Error case
///
pub(crate) fn try_parse_from_f32(n: f32) -> Result<BigDecimal, ParseBigDecimalError> {
    use std::num::FpCategory::*;
    match n.classify() {
        Nan => Err(ParseBigDecimalError::Other("NAN".into())),
        Infinite => Err(ParseBigDecimalError::Other("Infinite".into())),
        Subnormal => Err(ParseBigDecimalError::Other("Subnormal".into())),
        Normal | Zero => Ok(parse_from_f32(n)),
    }
}


/// Create bigdecimal from f32
///
/// Non "normal" values is undefined behavior
///
pub(crate) fn parse_from_f32(n: f32) -> BigDecimal {
    use std::cmp::Ordering::*;

    let bits = n.to_bits();

    if bits == 0 {
        return BigDecimal {
            int_val: BigInt::new(Sign::NoSign, vec![0]),
            scale: 0,
        };
    }

    let frac = (bits & ((1 << 23) - 1)) + (1 << 23);
    let exp = (bits >> 23) & 0xFF;

    let pow = exp as i64 - 127 - 23;

    let sign_bit = bits & (1 << 31);
    let sign = if sign_bit == 0 {
        Sign::Plus
    } else {
        Sign::Minus
    };

    let result;
    let scale;
    match pow.cmp(&0) {
        Equal => {
            result = BigUint::from(frac);
            scale = 0;
        }
        Less => {
            let trailing_zeros = frac.trailing_zeros();
            let reduced_frac = frac >> trailing_zeros;

            let reduced_pow = pow + trailing_zeros as i64;
            let shift = BigUint::from(5u8).pow(reduced_pow.abs() as u32);

            result = reduced_frac * shift;
            scale = -reduced_pow;
        }
        Greater => {
            let shift = BigUint::from(2u8).pow(pow.abs() as u32);

            result = frac * shift;
            scale = 0;
        }
    }

    BigDecimal {
        int_val: BigInt::from_biguint(sign, result),
        scale: scale,
    }
}

#[cfg(test)]
#[allow(non_snake_case)]
mod test_parse_from_f32 {
    use super::*;

    include!("parsing.tests.parse_from_f32.rs");
}
