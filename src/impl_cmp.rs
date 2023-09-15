//! Implementation of comparsion operations
//!
//! Comparisons between decimals and decimal refs
//! are not directly supported as we lose some type
//! inference features at the savings of a single
//! '&' character.
//!
//! &BigDecimal and BigDecimalRef are comparible.
//!

use crate::{
    BigDecimal,
    BigDecimalRef,
    Sign,
};

use stdlib::cmp::Ordering;
use stdlib::iter;

impl PartialEq for BigDecimal
{
    fn eq(&self, rhs: &BigDecimal) -> bool {
        self.to_ref() == rhs.to_ref()
    }
}

impl<'rhs, T> PartialEq<T> for BigDecimalRef<'_>
where
    T: Into<BigDecimalRef<'rhs>> + Copy
{
    fn eq(&self, rhs: &T) -> bool {
        let rhs: BigDecimalRef<'rhs> = (*rhs).into();

        match (self.sign(), rhs.sign()) {
            // both zero
            (Sign::NoSign, Sign::NoSign) => return true,
            // signs are different
            (a, b) if a != b => return false,
            // signs are same, do nothing
            _ => {}
        }

        let unscaled_int;
        let scaled_int;
        let trailing_zero_count;
        match self.scale.cmp(&rhs.scale) {
            Ordering::Greater => {
                unscaled_int = self.digits;
                scaled_int = rhs.digits;
                trailing_zero_count = (self.scale - rhs.scale) as usize;
            }
            Ordering::Less => {
                unscaled_int = rhs.digits;
                scaled_int = self.digits;
                trailing_zero_count = (rhs.scale - self.scale) as usize;
            }
            Ordering::Equal => return self.digits == rhs.digits,
        }

        if trailing_zero_count < 20 {
            let scaled_int = scaled_int * crate::ten_to_the(trailing_zero_count as u64).magnitude();
            return &scaled_int == unscaled_int;
        }

        let unscaled_digits = unscaled_int.to_radix_le(10);
        let scaled_digits = scaled_int.to_radix_le(10);

        // different lengths with trailing zeros
        if unscaled_digits.len() != scaled_digits.len() + trailing_zero_count {
            return false;
        }

        // add leading zero digits to digits that need scaled
        let scaled = iter::repeat(&0u8).take(trailing_zero_count).chain(scaled_digits.iter());

        // return true if all digits are the same
        unscaled_digits.iter().zip(scaled).all(|(digit_a, digit_b)| { digit_a == digit_b })
    }
}


#[cfg(test)]
mod test_bigintref {
    use super::*;
    use stdlib::ops::Neg;

    #[test]
    fn test_borrow_neg_cmp() {
        let x: BigDecimal = "1514932018891593.916341142773".parse().unwrap();
        let y: BigDecimal = "1514932018891593916341142773e-12".parse().unwrap();

        assert_eq!(x, y);

        let x_ref = x.to_ref();
        assert_eq!(x_ref, &y);
        assert_ne!(x_ref.neg(), x_ref);
        assert_eq!(x_ref.neg().neg(), x_ref);
    }
}
