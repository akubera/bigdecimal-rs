//! Remainder implementations

use super::*;

impl Rem<BigDecimal> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn rem(self, other: BigDecimal) -> BigDecimal {
        let scale = cmp::max(self.scale, other.scale);

        let num = self.take_and_scale(scale).int_val;
        let den = other.take_and_scale(scale).int_val;

        BigDecimal::new(num % den, scale)
    }
}

impl<'a> Rem<&'a BigDecimal> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn rem(self, other: &BigDecimal) -> BigDecimal {
        let scale = cmp::max(self.scale, other.scale);
        let num = self.take_and_scale(scale).int_val;
        let den = &other.int_val;

        let result = if scale == other.scale {
            num % den
        } else {
            num % (den * ten_to_the((scale - other.scale) as u64))
        };
        BigDecimal::new(result, scale)
    }
}
impl<'a> Rem<BigDecimal> for &'a BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn rem(self, other: BigDecimal) -> BigDecimal {
        let scale = cmp::max(self.scale, other.scale);
        let num = &self.int_val;
        let den = other.take_and_scale(scale).int_val;

        let result = if scale == self.scale {
            num % den
        } else {
            let scaled_num = num * ten_to_the((scale - self.scale) as u64);
            scaled_num % den
        };

        BigDecimal::new(result, scale)
    }
}

impl<'a, 'b> Rem<&'b BigDecimal> for &'a BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn rem(self, other: &BigDecimal) -> BigDecimal {
        let scale = cmp::max(self.scale, other.scale);
        let num = &self.int_val;
        let den = &other.int_val;

        let result = match self.scale.cmp(&other.scale) {
            Ordering::Equal => num % den,
            Ordering::Less => {
                let scaled_num = num * ten_to_the((scale - self.scale) as u64);
                scaled_num % den
            }
            Ordering::Greater => {
                let scaled_den = den * ten_to_the((scale - other.scale) as u64);
                num % scaled_den
            }
        };
        BigDecimal::new(result, scale)
    }
}
