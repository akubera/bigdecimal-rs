//! Structs and traits describing radix-dependant bigdigits
//!
//! BigDigit is a component of BigInt or BigDecimal, representing a unit
//! of multi-bit or multi-digit.
//!
#![allow(dead_code)]

use super::stdlib;
use super::num_traits;

use num_traits::Zero;
use num_traits::{ToPrimitive, FromPrimitive};
use num_traits::CheckedAdd;


pub(crate) mod alignment;
pub(crate) mod endian;
pub(crate) mod radix;
pub(crate) mod digitvec;

use self::endian::{Endianness, BigEndian, LittleEndian};
use self::radix::RadixType;

pub(crate) struct BigDigit<R: RadixType>(R::Base);


impl<R: RadixType> stdlib::fmt::Debug for BigDigit<R>
where
    R::Base: stdlib::fmt::Display
{
    fn fmt(&self, f: &mut stdlib::fmt::Formatter) -> stdlib::fmt::Result {
        write!(f, "BigDigit({})", self.0)
    }
}


impl<R: RadixType> BigDigit<R> {
    pub fn from_literal_integer(n: i32) -> Self {
        debug_assert!(n >= 0);

        let x: R::Base = FromPrimitive::from_i32(n).unwrap();
        Self(x)
    }
}

impl<R: RadixType> Zero for BigDigit<R> {
    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }

    fn zero() -> Self {
        Self(Zero::zero())
    }
}

impl<R: RadixType> stdlib::ops::Add for BigDigit<R> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match self.0.checked_add(&rhs.0) {
            Some(sum)  => {
                if R::BaseDouble::from(sum) < R::RADIX {
                    Self(sum)
                } else {
                    panic!("sum overflow");
                }
            }
            None => {
                unreachable!()
            }
        }
    }
}
