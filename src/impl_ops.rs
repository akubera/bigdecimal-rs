//! Implement math operations: Add,Sub, etc

use crate::BigDecimal;
use crate::stdlib::ops::{
    Add, AddAssign,
};

macro_rules! impl_add_for_primitive {
    ($t:ty) => {
        impl_add_for_primitive!(IMPL:ADD $t);
        impl_add_for_primitive!(IMPL:ADD-ASSIGN $t);
        impl_add_for_primitive!(IMPL:ADD &$t);
        impl_add_for_primitive!(IMPL:ADD-ASSIGN &$t);
    };
    (IMPL:ADD $t:ty) => {
        impl Add<$t> for BigDecimal {
            type Output = BigDecimal;

            fn add(mut self, rhs: $t) -> BigDecimal {
                self += rhs;
                self
            }
        }

        impl Add<$t> for &BigDecimal {
            type Output = BigDecimal;

            fn add(self, rhs: $t) -> BigDecimal {
                BigDecimal::from(rhs) + self
            }
        }

        impl Add<BigDecimal> for $t {
            type Output = BigDecimal;

            fn add(self, rhs: BigDecimal) -> BigDecimal {
                rhs + self
            }
        }

        impl Add<&BigDecimal> for $t {
            type Output = BigDecimal;

            fn add(self, rhs: &BigDecimal) -> BigDecimal {
                rhs + self
            }
        }
    };
    (IMPL:ADD-ASSIGN &$t:ty) => {
        // special case for the ref types
        impl AddAssign<&$t> for BigDecimal {
            fn add_assign(&mut self, rhs: &$t) {
                *self += *rhs;
            }
        }
    };
    (IMPL:ADD-ASSIGN $t:ty) => {
        impl AddAssign<$t> for BigDecimal {
            fn add_assign(&mut self, rhs: $t) {
                if rhs == 0 {
                    // no-op
                } else if self.scale == 0 {
                    self.int_val += rhs;
                } else {
                    *self += BigDecimal::from(rhs);
                }
            }
        }
    };
}

impl_add_for_primitive!(u8);
impl_add_for_primitive!(u16);
impl_add_for_primitive!(u32);
impl_add_for_primitive!(u64);
impl_add_for_primitive!(u128);
impl_add_for_primitive!(i8);
impl_add_for_primitive!(i16);
impl_add_for_primitive!(i32);
impl_add_for_primitive!(i64);
impl_add_for_primitive!(i128);
