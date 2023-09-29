//! Multiplication operator trait implementation
//!

use super::*;
use crate::stdlib::mem::swap;


impl Mul<BigDecimal> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn mul(mut self, rhs: BigDecimal) -> BigDecimal {
        if self.is_one() {
            rhs
        } else if rhs.is_one() {
            self
        } else {
            self.scale += rhs.scale;
            self.int_val *= rhs.int_val;
            self
        }
    }
}

impl<'a> Mul<&'a BigDecimal> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn mul(mut self, rhs: &'a BigDecimal) -> BigDecimal {
        if self.is_one() {
            self.scale = rhs.scale;
            self.int_val.set_zero();
            self.int_val.add_assign(&rhs.int_val);
            self
        } else if rhs.is_one() {
            self
        } else {
            self.scale += rhs.scale;
            MulAssign::mul_assign(&mut self.int_val, &rhs.int_val);
            self
        }
    }
}

impl<'a> Mul<BigDecimal> for &'a BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn mul(self, rhs: BigDecimal) -> BigDecimal {
        rhs * self
    }
}

impl<'a, 'b> Mul<&'b BigDecimal> for &'a BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn mul(self, rhs: &BigDecimal) -> BigDecimal {
        if self.is_one() {
            rhs.normalized()
        } else if rhs.is_one() {
            self.normalized()
        } else {
            let scale = self.scale + rhs.scale;
            BigDecimal::new(&self.int_val * &rhs.int_val, scale)
        }
    }
}

impl Mul<BigInt> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn mul(mut self, rhs: BigInt) -> BigDecimal {
        self.int_val *= rhs;
        self
    }
}

impl<'a> Mul<&'a BigInt> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn mul(mut self, rhs: &BigInt) -> BigDecimal {
        self.int_val *= rhs;
        self
    }
}

impl<'a> Mul<BigInt> for &'a BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn mul(self, mut rhs: BigInt) -> BigDecimal {
        rhs *= &self.int_val;
        BigDecimal::new(rhs, self.scale)
    }
}

impl<'a, 'b> Mul<&'a BigInt> for &'b BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn mul(self, rhs: &BigInt) -> BigDecimal {
        if rhs.is_one() {
            self.normalized()
        } else if self.is_one() {
            BigDecimal::new(rhs.clone(), 0)
        } else {
            let value = &self.int_val * rhs;
            BigDecimal::new(value, self.scale)
        }
    }
}

impl Mul<BigDecimal> for BigInt {
    type Output = BigDecimal;

    #[inline]
    fn mul(mut self, mut rhs: BigDecimal) -> BigDecimal {
        if rhs.is_one() {
            rhs.scale = 0;
            swap(&mut rhs.int_val, &mut self);
        } else if !self.is_one() {
            rhs.int_val *= self;
        }
        rhs
    }
}

impl<'a> Mul<BigDecimal> for &'a BigInt {
    type Output = BigDecimal;

    #[inline]
    fn mul(self, mut rhs: BigDecimal) -> BigDecimal {
        if self.is_one() {
            rhs.normalized()
        } else if rhs.is_one() {
            rhs.int_val.set_zero();
            rhs.int_val += self;
            rhs.scale = 0;
            rhs
        } else {
            rhs.int_val *= self;
            rhs
        }
    }
}

impl<'a, 'b> Mul<&'a BigDecimal> for &'b BigInt {
    type Output = BigDecimal;

    #[inline]
    fn mul(self, rhs: &BigDecimal) -> BigDecimal {
        if self.is_one() {
            rhs.normalized()
        } else if rhs.is_one() {
            BigDecimal::new(self.clone(), 0)
        } else {
            let value = &rhs.int_val * self;
            BigDecimal::new(value, rhs.scale)
        }
    }
}

impl<'a> Mul<&'a BigDecimal> for BigInt {
    type Output = BigDecimal;

    #[inline]
    fn mul(mut self, rhs: &BigDecimal) -> BigDecimal {
        if self.is_one() {
            rhs.normalized()
        } else if rhs.is_one() {
            BigDecimal::new(self, 0)
        } else {
            self *= &rhs.int_val;
            BigDecimal::new(self, rhs.scale)
        }
    }
}

forward_val_assignop!(impl MulAssign for BigDecimal, mul_assign);

impl<'a> MulAssign<&'a BigDecimal> for BigDecimal {
    #[inline]
    fn mul_assign(&mut self, rhs: &BigDecimal) {
        if rhs.is_one() {
            return;
        }
        self.scale += rhs.scale;
        self.int_val = &self.int_val * &rhs.int_val;
    }
}

impl<'a> MulAssign<&'a BigInt> for BigDecimal {
    #[inline]
    fn mul_assign(&mut self, rhs: &BigInt) {
        if rhs.is_one() {
            return;
        }
        self.int_val *= rhs;
    }
}

impl MulAssign<BigInt> for BigDecimal {
    #[inline]
    fn mul_assign(&mut self, rhs: BigInt) {
        *self *= &rhs
    }
}


#[cfg(test)]
#[allow(non_snake_case)]
mod bigdecimal_tests {
    use crate::{stdlib, BigDecimal, ToString, FromStr, TryFrom};
    use num_traits::{ToPrimitive, FromPrimitive, Signed, Zero, One};
    use num_bigint;
    use paste::paste;

    /// Test multiplication of two bigdecimals
    #[test]
    fn test_mul() {

        let vals = vec![
            ("2", "1", "2"),
            ("12.34", "1.234", "15.22756"),
            ("2e1", "1", "20"),
            ("3", ".333333", "0.999999"),
            ("2389472934723", "209481029831", "500549251119075878721813"),
            ("1e-450", "1e500", ".1e51"),
            ("-995052931372975485719.533153137", "4.523087321", "-4500711297616988541501.836966993116075977"),
            ("995052931372975485719.533153137", "-4.523087321", "-4500711297616988541501.836966993116075977"),
            ("-8.37664968", "-1.9086963714056968482094712882596748", "15.988480848752691653730876239769592670324064"),
            ("-8.37664968", "0", "0"),
        ];

        for &(x, y, z) in vals.iter() {

            let mut a = BigDecimal::from_str(x).unwrap();
            let b = BigDecimal::from_str(y).unwrap();
            let c = BigDecimal::from_str(z).unwrap();

            assert_eq!(a.clone() * b.clone(), c);
            assert_eq!(a.clone() * &b, c);
            assert_eq!(&a * b.clone(), c);
            assert_eq!(&a * &b, c);

            a *= b;
            assert_eq!(a, c);
        }
    }

    /// Test multiplication between big decimal and big integer
    #[test]
    fn test_mul_bigint() {
        let vals = vec![
            ("2", "1", "2"),
            ("8.561", "10", "85.61"),
            ("1.0000", "638655273892892437", "638655273892892437"),
            ("10000", "638655273892892437", "6386552738928924370000"),
            (".0005", "368408638655273892892437473", "184204319327636946446218.7365"),
            ("9e-1", "368408638655273892892437473", "331567774789746503603193725.7"),
            ("-1.175470587012343730098", "577575785", "-678923347.038065234601180476930"),
            ("-1.175470587012343730098", "-76527768352678", "89956140788267.069799533723307502444"),
            ("-1.175470587012343730098", "0", "0"),
        ];

        for &(x, y, z) in vals.iter() {
            let a = BigDecimal::from_str(x).unwrap();
            let b = num_bigint::BigInt::from_str(y).unwrap();
            let c = BigDecimal::from_str(z).unwrap();

            assert_eq!(a.clone() * b.clone(), c);
            assert_eq!(b.clone() * a.clone(), c);
            assert_eq!(a.clone() * &b, c);
            assert_eq!(b.clone() * &a, c);
            assert_eq!(&a * b.clone(), c);
            assert_eq!(&b * a.clone(), c);
            assert_eq!(&a * &b, c);
            assert_eq!(&b * &a, c);
        }
    }
}
