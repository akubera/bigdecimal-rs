//!
//! Support for `arbitrary` crate
//!
//! Implements the `Arbitrary` trait for `BigDecimal`, allowing it to be
//! used with fuzzing tools like `cargo-fuzz` and `libfuzzer`.
//!

use crate::BigDecimal;
use arbitrary::{Arbitrary, Unstructured, Result as ArbitraryResult};

/// Maximum absolute value of scale to generate
///
/// This limit prevents memory allocation failures that can occur when
/// generating BigDecimals with extremely large scales, which would
/// result in very long string representations.
const SCALE_LIMIT: i64 = 1_000_000;

impl<'a> Arbitrary<'a> for BigDecimal {
    fn arbitrary(u: &mut Unstructured<'a>) -> ArbitraryResult<Self> {
        let scale = i64::arbitrary(u)? % SCALE_LIMIT;
        let int_val = num_bigint::BigInt::arbitrary(u)?;
        Ok(BigDecimal::new(int_val, scale))
    }

    fn arbitrary_take_rest(mut u: Unstructured<'a>) -> ArbitraryResult<Self> {
        let scale = i64::arbitrary(&mut u)? % SCALE_LIMIT;
        let int_val = num_bigint::BigInt::arbitrary_take_rest(u)?;
        Ok(BigDecimal::new(int_val, scale))
    }

    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            i64::size_hint(depth),
            num_bigint::BigInt::size_hint(depth),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arbitrary_bigdecimal() {
        // Test that we can generate BigDecimals from arbitrary bytes
        let data: &[u8] = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        let mut u = Unstructured::new(data);
        let result = BigDecimal::arbitrary(&mut u);
        assert!(result.is_ok());
    }

    #[test]
    fn test_arbitrary_bigdecimal_scale_is_limited() {
        // Test both positive and negative out-of-range scales across both generation methods
        let pos_scale: i64 = 5_500_000;
        let neg_scale: i64 = -5_500_000;
        let bigint_payload: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];

        // 1. arbitrary() with positive out-of-range scale
        let mut pos_data = Vec::new();
        pos_data.extend_from_slice(&pos_scale.to_le_bytes());
        pos_data.extend_from_slice(&bigint_payload);
        let mut u_pos = Unstructured::new(&pos_data);
        let bd_pos = BigDecimal::arbitrary(&mut u_pos).unwrap();
        assert_eq!(bd_pos.fractional_digit_count(), pos_scale % SCALE_LIMIT);
        assert!(bd_pos.fractional_digit_count().abs() < SCALE_LIMIT);

        // 2. arbitrary() with negative out-of-range scale
        let mut neg_data = Vec::new();
        neg_data.extend_from_slice(&neg_scale.to_le_bytes());
        neg_data.extend_from_slice(&bigint_payload);
        let mut u_neg = Unstructured::new(&neg_data);
        let bd_neg = BigDecimal::arbitrary(&mut u_neg).unwrap();
        assert_eq!(bd_neg.fractional_digit_count(), neg_scale % SCALE_LIMIT);
        assert!(bd_neg.fractional_digit_count().abs() < SCALE_LIMIT);

        // 3. arbitrary_take_rest() with positive out-of-range scale
        let u_pos_rest = Unstructured::new(&pos_data);
        let bd_pos_rest = BigDecimal::arbitrary_take_rest(u_pos_rest).unwrap();
        assert_eq!(bd_pos_rest.fractional_digit_count(), pos_scale % SCALE_LIMIT);
        assert!(bd_pos_rest.fractional_digit_count().abs() < SCALE_LIMIT);

        // 4. arbitrary_take_rest() with negative out-of-range scale
        let u_neg_rest = Unstructured::new(&neg_data);
        let bd_neg_rest = BigDecimal::arbitrary_take_rest(u_neg_rest).unwrap();
        assert_eq!(bd_neg_rest.fractional_digit_count(), neg_scale % SCALE_LIMIT);
        assert!(bd_neg_rest.fractional_digit_count().abs() < SCALE_LIMIT);
    }

    #[test]
    fn test_arbitrary_take_rest() {
        let data: &[u8] = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20];
        let u = Unstructured::new(data);
        let result = BigDecimal::arbitrary_take_rest(u);
        assert!(result.is_ok());
    }

    #[test]
    fn test_arbitrary_empty_or_short_data() {
        // Empty buffer produces BigDecimal zero with scale 0
        let mut u = Unstructured::new(&[]);
        let bd = BigDecimal::arbitrary(&mut u).unwrap();
        assert_eq!(bd, BigDecimal::from(0));
        assert_eq!(bd.fractional_digit_count(), 0);

        let u_rest = Unstructured::new(&[]);
        let bd_rest = BigDecimal::arbitrary_take_rest(u_rest).unwrap();
        assert_eq!(bd_rest, BigDecimal::from(0));
        assert_eq!(bd_rest.fractional_digit_count(), 0);

        // Short buffer (less than 8 bytes) pads with zeros and succeeds
        let mut u_short = Unstructured::new(&[1, 2, 3, 4]);
        let bd_short = BigDecimal::arbitrary(&mut u_short).unwrap();
        assert!(bd_short.fractional_digit_count().abs() < SCALE_LIMIT);
    }

    #[test]
    fn test_arbitrary_extreme_scales() {
        let extreme_scales = [i64::MIN, i64::MAX, 0, SCALE_LIMIT, -SCALE_LIMIT];
        let bigint_payload: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];

        for &scale in &extreme_scales {
            let mut data = Vec::new();
            data.extend_from_slice(&scale.to_le_bytes());
            data.extend_from_slice(&bigint_payload);

            let mut u = Unstructured::new(&data);
            let bd = BigDecimal::arbitrary(&mut u).unwrap();
            assert_eq!(bd.fractional_digit_count(), scale % SCALE_LIMIT);
            assert!(bd.fractional_digit_count().abs() < SCALE_LIMIT);

            let u_rest = Unstructured::new(&data);
            let bd_rest = BigDecimal::arbitrary_take_rest(u_rest).unwrap();
            assert_eq!(bd_rest.fractional_digit_count(), scale % SCALE_LIMIT);
            assert!(bd_rest.fractional_digit_count().abs() < SCALE_LIMIT);
        }
    }

    #[test]
    fn test_size_hint() {
        let (min, max) = BigDecimal::size_hint(0);
        assert_eq!(min, 9);
        assert!(max.is_none());
    }
}
