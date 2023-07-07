//! Definitions of owned collections of digits
//!
//! The choice how to store the digits in a BigDecimal is a very
//! important one, and hard to maintain both flexibility and
//! efficiency.
//!
//! Some layouts may be optimized for math operations, others for
//! reading & writing. Most likely the most efficient ones are
//! those matching the source of the digits: strings of human
//! readable, or base-10000,
//!
//! This module contains them all.
//!
#![allow(non_camel_case_types)]
#![allow(dead_code)]

mod alignment;

use stdlib::marker::PhantomData;
use stdlib::u64;
use stdlib::vec::Vec;

/// Stateless endianess type to indicate BigEndian digit storage
pub struct BigEndian;

/// Stateless endianess type to indicate LittleEndian digit storage
pub struct LittleEndian;

/// Trait to allow genric parameterization of DigitBuffers endianess
pub trait Endianess {}

impl Endianess for BigEndian {}
impl Endianess for LittleEndian {}


/// Radix=*10* / storage=*u8*
pub struct RADIX_10_u8;

/// Radix=*10,000* storage=*i16*
pub struct RADIX_10E4_i16;

/// Radix=*1,000,000,000* storage=*u32*
pub struct Radix10p9U32;

pub struct Radix2e32;
pub struct Radix2e64;

/// All the information needed to specify a bigdecimal's radix
pub trait RadixType {
    type Base;
    type BaseDouble;

    const RADIX: Self::BaseDouble;
    const POWER_OF_TEN: Option<usize>;
    const IS_POW_OF_TEN: bool = Self::POWER_OF_TEN.is_none();
    // fn radix() -> Self::BaseDouble;
    // fn is_power_of_ten() -> bool { !Self::power_of_ten().is_none() }
    // fn power_of_ten() -> Option<usize>;
}

macro_rules! impl_radix_type {
    ($t:ty : base=$base:ty, base-double=$doublewide:ty, radix=$radix:expr $(,)?) => {
        impl_radix_type!($t : base=$base, base-double=$doublewide, radix=$radix, pow_of_ten=None);
    };
    ($t:ty : base=$base:ty, base-double=$doublewide:ty, radix=$radix:expr, pow_of_ten=$pow_of_ten:literal $(,)?) => {
        impl_radix_type!($t : base=$base, base-double=$doublewide, radix=$radix, pow_of_ten=Some($pow_of_ten));
    };
    ($t:ty : base=$base:ty, base-double=$doublewide:ty, radix=$radix:expr, pow_of_ten=$pow_of_ten:expr $(,)?) => {
        impl RadixType for $t {
            type Base = $base;
            type BaseDouble = $doublewide;

            const RADIX: Self::BaseDouble = $radix;
            const POWER_OF_TEN: Option<usize> = $pow_of_ten;
        }
    };
}

impl_radix_type!(
    Radix2e64:
        base = u64,
        base-double = u128,
        radix = u64::MAX as u128 + 1
);

impl_radix_type!(
    Radix2e32:
        base = u32,
        base-double = u64,
        radix = u32::MAX as u64 + 1
);

impl_radix_type!(
    RADIX_10E4_i16:
        base = i16,
        base-double = i32,
        radix = 10_000,
        pow_of_ten = 4,
);

impl_radix_type!(
    Radix10p9U32:
        base = u32,
        base-double = u64,
        radix = 1_000_000_000,
        pow_of_ten = 9
);

impl_radix_type!(
    RADIX_10_u8:
        base = u8,
        // u8 can fit 10**2, so it's appropriate for double-wide type
        base-double = u8,
        radix = 10,
        pow_of_ten = 1
);


/// Generic Digit Buffer
///
pub struct DigitBuf<E: Endianess, R: RadixType> {
    _data: Vec<R::Base>,
    _endianess: PhantomData<E>,
    _radix: PhantomData<R>,
}


/// Buffer of individual digits
pub type IndividualDigitBuf = DigitBuf<BigEndian, RADIX_10_u8>;

/// Buffer storing 9 decimal digits in a u32
// pub type StandardDigitBuf = DigitBuf<LittleEndian, Radix10p9U32>;

// pub type PostgresStyle = DigitBuf<LittleEndian, RADIX_10E4_i16>;


enum DigitBuffers {
    /// Individual digits
    Individual(IndividualDigitBuf),
    // ///
    // Standard(StandardDigitBuf),
    // /// Postgres style
    // Postgres(PostgresStyle),
}


pub struct DigitBufInfo {
    /// Any of the digit buffers
    data: DigitBuffers,
}

/// BigiDigit, properties based on a radix type
#[derive(Default,Clone,Copy,Eq,PartialEq,Ord,PartialOrd)]
pub struct BigDigit<R: RadixType>(R::Base);

impl<R:RadixType> std::fmt::Debug for BigDigit<R>
where
    R::Base: std::fmt::Display
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BigDigit({})", self.0)
    }
}

use num_traits::{ToPrimitive, FromPrimitive};


impl<R: RadixType> BigDigit<R>
where
    R::Base: 'static + Copy,
    R::Base: FromPrimitive,
    R::Base: ToPrimitive,
    R::Base: num_traits::Num,
    R::Base: num_integer::Integer,
    R::Base: Into<R::BaseDouble>,
    R::BaseDouble: num_traits::AsPrimitive<R::Base>,
    R::BaseDouble: num_traits::Num,
    R::BaseDouble: num_integer::Integer,
{
    const BIG_DIGIT_RADIX: R::BaseDouble = R::RADIX;

    pub(crate) fn from_raw_integer<N: Into<R::Base>>(n: N) -> Self {
        let v = n.into();
        debug_assert!(v.into() < Self::BIG_DIGIT_RADIX);
        BigDigit(v)
    }

    pub(crate) fn from_literal_integer(n: i32) -> Self {
        debug_assert!(n >= 0);
        // debug_assert!(n < Self::BIG_DIGIT_RADIX.as_());
        let x: R::Base = FromPrimitive::from_i32(n).unwrap();
        BigDigit(x)
    }

    /// Return value zero
    pub fn zero() -> Self {
        BigDigit(num_traits::Zero::zero())
    }

    /// Return value one
    pub fn one() -> Self {
        BigDigit(num_traits::One::one())
    }

    pub fn max() -> Self {
        use num_traits::One;
        use num_traits::AsPrimitive;

        let max_val: R::BaseDouble = Self::BIG_DIGIT_RADIX - One::one();
        BigDigit(max_val.as_())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn max() {
        type BigDigitX = BigDigit<Radix10p9U32>;

        let x = BigDigitX::max();
        assert_eq!(x, 999999999);
    }

    #[test]
    fn fromraw() {
        type BigDigitX = BigDigit<Radix10p9U32>;

        let y: u32 = 34;
        let x = BigDigitX::from_raw_integer(y);
        assert_eq!(x, 34);
    }
}

impl<R:'static+Copy+RadixType> num_traits::AsPrimitive<R::Base> for BigDigit<R>
where
    R::Base: 'static + Copy
{
    fn as_(self) -> R::Base {
        self.0
    }
}

impl<R:RadixType> std::cmp::PartialEq<u32> for BigDigit<R>
where
    R::Base: std::cmp::PartialEq<u32>
{
    #[inline]
    fn eq(&self, other: &u32) -> bool { self.0 == *other }
}

impl<R:RadixType> std::cmp::PartialEq<i32> for BigDigit<R>
where
    R::Base: std::cmp::PartialEq<i32>
{
    #[inline]
    fn eq(&self, other: &i32) -> bool { self.0 == *other }
}


// macro_rules! impl_partial_eq {
//     (BigDigit < $t:ty) => {
//         impl<R> std::cmp::PartialEq<$t> for BigDigit<R> {
//             #[inline]
//             fn eq(&self, other: &$t) -> bool { self.0 as $t == *other }
//         }
//         impl<R> std::cmp::PartialEq<BigDigit> for $t {
//             #[inline]
//             fn eq(&self, other: &BigDigit) -> bool { other.0 as $t == *self }
//         }
//         impl<R> std::cmp::PartialOrd<$t> for BigDigit<R> {
//             #[inline]
//             fn partial_cmp(&self, other: &$t) -> Option<std::cmp::Ordering> {
//                 <$t>::from(self.0).partial_cmp(other)
//             }
//         }
//     };
//     (BigDigit > $t:ty) => {
//         impl<R> std::cmp::PartialEq<$t> for BigDigit<R> {
//             type BigDigitBase = R::Base;
//             #[inline]
//             fn eq(&self, other: &$t) -> bool { self.0.eq(&BigDigitBase::from(*other)) }
//         }
//         impl<R> std::cmp::PartialEq<BigDigit<R>> for $t {
//             #[inline]
//             fn eq(&self, other: &BigDigit) -> bool { other.0.eq(&BigDigitBase::from(*self)) }
//         }
//         impl<R> std::cmp::PartialOrd<$t> for BigDigit<R> {
//             #[inline]
//             fn partial_cmp(&self, other: &$t) -> Option<std::cmp::Ordering> {
//                 self.0.partial_cmp(&BigDigitBase::from(*other))
//             }
//         }
//     };
//     (BigDigit <> $t:ty) => {
//         impl<R> std::cmp::PartialEq<$t> for BigDigit<R> {
//             #[inline]
//             fn eq(&self, other: &$t) -> bool { (self.0 as i64).eq(&(*other as i64)) }
//         }
//         impl<R> std::cmp::PartialEq<BigDigit<R>> for $t {
//             #[inline]
//             fn eq(&self, other: &BigDigit) -> bool { (other.0 as i64).eq(&(*self as i64)) }
//         }
//         impl<R> std::cmp::PartialOrd<$t> for BigDigit<R> {
//             #[inline]
//             fn partial_cmp(&self, other: &$t) -> Option<std::cmp::Ordering> {
//                 (self.0 as i64).partial_cmp(&i64::from(*other))
//             }
//         }
//     };
// }

// impl_partial_eq!(BigDigit > u8);
// impl_partial_eq!(BigDigit > u16);
// impl_partial_eq!(BigDigit > u32);
// impl_partial_eq!(BigDigit < u64);
// impl_partial_eq!(BigDigit < u128);
// impl_partial_eq!(BigDigit <> i8);
// impl_partial_eq!(BigDigit <> i16);
// impl_partial_eq!(BigDigit <> i32);
// impl_partial_eq!(BigDigit <> i64);
