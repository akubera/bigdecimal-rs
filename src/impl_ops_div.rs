//! Implement division

use super::*;

impl Div<BigDecimal> for BigDecimal {
    type Output = BigDecimal;
    #[inline]
    fn div(self, other: BigDecimal) -> BigDecimal {
        if other.is_zero() {
            panic!("Division by zero");
        }
        if self.is_zero() || other.is_one_quickcheck() == Some(true) {
            return self;
        }

        let scale = self.scale - other.scale;

        if self.int_val == other.int_val {
            return BigDecimal {
                int_val: 1.into(),
                scale: scale,
            };
        }

        let max_precision = DEFAULT_PRECISION;

        return impl_division(self.int_val, &other.int_val, scale, max_precision);
    }
}

impl<'a> Div<&'a BigDecimal> for BigDecimal {
    type Output = BigDecimal;
    #[inline]
    fn div(self, other: &'a BigDecimal) -> BigDecimal {
        if other.is_zero() {
            panic!("Division by zero");
        }
        if self.is_zero() || other.is_one_quickcheck() == Some(true) {
            return self;
        }

        let scale = self.scale - other.scale;

        if self.int_val == other.int_val {
            return BigDecimal {
                int_val: 1.into(),
                scale: scale,
            };
        }

        let max_precision = DEFAULT_PRECISION;

        return impl_division(self.int_val, &other.int_val, scale, max_precision);
    }
}

forward_ref_val_binop!(impl Div for BigDecimal, div);

impl Div<&BigDecimal> for &BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn div(self, other: &BigDecimal) -> BigDecimal {
        if other.is_zero() {
            panic!("Division by zero");
        }
        // TODO: Fix setting scale
        if self.is_zero() || other.is_one_quickcheck() == Some(true) {
            return self.clone();
        }

        let scale = self.scale - other.scale;

        let num_int = &self.int_val;
        let den_int = &other.int_val;

        if num_int == den_int {
            return BigDecimal {
                int_val: 1.into(),
                scale: scale,
            };
        }

        let max_precision = DEFAULT_PRECISION;

        return impl_division(num_int.clone(), den_int, scale, max_precision);
    }
}

// tests in lib.tests.ops.div.rs
