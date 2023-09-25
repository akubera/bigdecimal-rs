//! Addition operator trait implementation
//!

use crate::{
    Sign,
    BigDecimal,
    BigDecimalRef,
};

use crate::stdlib::{
    ops::{Add, AddAssign, Neg},
    cmp::Ordering,
};

use num_bigint::{BigInt, BigUint};
use crate::ten_to_the;

impl Add<BigDecimal> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn add(self, rhs: BigDecimal) -> BigDecimal {
        let mut lhs = self;

        match lhs.scale.cmp(&rhs.scale) {
            Ordering::Equal => {
                lhs.int_val += rhs.int_val;
                lhs
            }
            Ordering::Less => lhs.take_and_scale(rhs.scale) + rhs,
            Ordering::Greater => rhs.take_and_scale(lhs.scale) + lhs,
        }
    }
}

impl<'a> Add<&'a BigDecimal> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn add(self, rhs: &'a BigDecimal) -> BigDecimal {
        let mut lhs = self;

        match lhs.scale.cmp(&rhs.scale) {
            Ordering::Equal => {
                lhs.int_val += &rhs.int_val;
                lhs
            }
            Ordering::Less => lhs.take_and_scale(rhs.scale) + rhs,
            Ordering::Greater => rhs.with_scale(lhs.scale) + lhs,
        }
    }
}

impl<'a> Add<BigDecimal> for &'a BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn add(self, rhs: BigDecimal) -> BigDecimal {
        rhs + self
    }
}

impl<'a, 'b> Add<&'b BigDecimal> for &'a BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn add(self, rhs: &BigDecimal) -> BigDecimal {
        let lhs = self;
        match self.scale.cmp(&rhs.scale) {
            Ordering::Less => lhs.with_scale(rhs.scale) + rhs,
            Ordering::Greater => rhs.with_scale(lhs.scale) + lhs,
            Ordering::Equal => BigDecimal::new(lhs.int_val.clone() + &rhs.int_val, lhs.scale),
        }
    }
}

impl Add<BigInt> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn add(self, rhs: BigInt) -> BigDecimal {
        let mut lhs = self;

        match lhs.scale.cmp(&0) {
            Ordering::Equal => {
                lhs.int_val += rhs;
                lhs
            }
            Ordering::Greater => {
                lhs.int_val += rhs * ten_to_the(lhs.scale as u64);
                lhs
            }
            Ordering::Less => lhs.take_and_scale(0) + rhs,
        }
    }
}

impl<'a> Add<&'a BigInt> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn add(self, rhs: &BigInt) -> BigDecimal {
        let mut lhs = self;

        match lhs.scale.cmp(&0) {
            Ordering::Equal => {
                lhs.int_val += rhs;
                lhs
            }
            Ordering::Greater => {
                lhs.int_val += rhs * ten_to_the(lhs.scale as u64);
                lhs
            }
            Ordering::Less => lhs.take_and_scale(0) + rhs,
        }
    }
}

impl<'a> Add<BigInt> for &'a BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn add(self, rhs: BigInt) -> BigDecimal {
        BigDecimal::new(rhs, 0) + self
    }
}

impl<'a, 'b> Add<&'a BigInt> for &'b BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn add(self, rhs: &BigInt) -> BigDecimal {
        self.with_scale(0) + rhs
    }
}

forward_val_assignop!(impl AddAssign for BigDecimal, add_assign);

impl<'a> AddAssign<&'a BigDecimal> for BigDecimal {
    #[inline]
    fn add_assign(&mut self, rhs: &BigDecimal) {
        match self.scale.cmp(&rhs.scale) {
            Ordering::Less => {
                let scaled = self.with_scale(rhs.scale);
                self.int_val = scaled.int_val + &rhs.int_val;
                self.scale = rhs.scale;
            }
            Ordering::Greater => {
                let scaled = rhs.with_scale(self.scale);
                self.int_val += scaled.int_val;
            }
            Ordering::Equal => {
                self.int_val += &rhs.int_val;
            }
        }
    }
}

impl AddAssign<BigInt> for BigDecimal {
    #[inline]
    fn add_assign(&mut self, rhs: BigInt) {
        *self += BigDecimal::new(rhs, 0)
    }
}

impl<'a> AddAssign<&'a BigInt> for BigDecimal {
    #[inline]
    fn add_assign(&mut self, rhs: &BigInt) {
        match self.scale.cmp(&0) {
            Ordering::Equal => self.int_val += rhs,
            Ordering::Greater => self.int_val += rhs * ten_to_the(self.scale as u64),
            Ordering::Less => {
                // *self += BigDecimal::new(rhs, 0)
                self.int_val *= ten_to_the((-self.scale) as u64);
                self.int_val += rhs;
                self.scale = 0;
            }
        }
    }
}
