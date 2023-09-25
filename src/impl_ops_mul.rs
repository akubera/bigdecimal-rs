//! Multiplication operator trait implementation
//!

use crate::{
    Sign,
    BigDecimal,
    BigDecimalRef,
};

use crate::stdlib::{
    mem::swap,
    ops::{Mul, MulAssign, AddAssign, Neg},
    cmp::Ordering,
};

use num_bigint::{BigInt, BigUint};
use num_traits::{Zero, One};
use crate::ten_to_the;

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
