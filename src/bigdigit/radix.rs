//! Radix definitions
//!
//! Empty structs used to make generic algorithms over kind of radix
//!
#![allow(dead_code)]
#![allow(non_camel_case_types)]

use crate::*;
use crate::stdlib::fmt;

use num_traits::{WrappingAdd, WrappingSub, AsPrimitive};


/// All the information needed to specify a bigdecimal's radix, and methods operating on integers
pub trait RadixType: Copy + Clone + Default + fmt::Debug {
    /// the inner type of values
    type Base
        : 'static
        + Copy
        + fmt::Debug
        + num_integer::Integer
        + num_traits::PrimInt
        + num_traits::FromPrimitive
        + num_traits::AsPrimitive<Self::BaseDouble>
        + num_traits::Zero
        + num_traits::One
        + num_traits::WrappingSub
        + num_traits::Pow<u8, Output = Self::Base>
        + AddAssign
        + From<bool>
        + From<u8>;

    /// double wide unsigned type (capable of storing product of two BigDigits)
    type BaseDouble
        : 'static
        + Copy
        + num_integer::Integer
        + num_traits::PrimInt
        + num_traits::FromPrimitive
        + num_traits::AsPrimitive<Self::Base>
        + num_traits::Zero
        + num_traits::One
        + num_traits::WrappingAdd
        + num_traits::WrappingSub
        + AddAssign
        + From<u8>
        + From<Self::Base>;

    /// signed version of base (used for diffs)
    type SignedBase
        : 'static
        + Copy
        + num_integer::Integer
        + num_traits::PrimInt
        + num_traits::FromPrimitive
        + num_traits::Zero
        + num_traits::One
        + num_traits::Signed;

    /// Value of the RADIX
    const RADIX: Self::BaseDouble;

    /// Check contents of iterable contains values less than the radix
    fn validate_digits<'a, I: IntoIterator<Item = &'a Self::Base>>(i: I) -> bool {
        i.into_iter().map(|&d| d.into()).all(|d| Self::BaseDouble::zero() <= d && d < Self::RADIX)
    }

    /// True if n is the maximum value for this radix (RADIX - 1)
    fn max() -> Self::Base {
        (Self::RADIX - One::one()).as_()
    }

    /// True if n is the maximum value for this radix (RADIX - 1)
    fn is_max(n: Self::Base) -> bool {
        n == Self::max()
    }

    /// Split single-width BigDigit base-type value into valid BigDigits for
    /// this Radix
    fn split_single(n: Self::Base) -> (Self::Base, Self::Base) {
        let (hi, lo) = num_integer::div_rem(n.as_(), Self::RADIX);
        return (hi.as_(), lo.as_());
    }

    /// Split double-wide value into valid BigDigit and overflow for this Radix
    fn split_doublewide(n: Self::BaseDouble) -> (Self::BaseDouble, Self::Base) {
        let (hi, lo) = num_integer::div_rem(n, Self::RADIX);
        return (hi, lo.as_());
    }

    /// Split double-wide bigdigit into high and low bigdigits.
    ///
    /// This assumes n will fit in two bigdigits, which is not guaranteed.
    /// Use split_doublewide.
    ///
    fn split_wide_digit(n: Self::BaseDouble) -> (Self::Base, Self::Base) {
        let (hi, lo) = num_integer::div_rem(n, Self::RADIX);
        debug_assert!(hi < Self::RADIX);
        return (hi.as_(), lo.as_());
    }

    /// Perform n + carry, returning sum and storing overflow back in carry
    fn add_carry(n: Self::Base, carry: &mut Self::Base) -> Self::Base {
        let (hi, lo) = Self::expanding_add(n, *carry);
        *carry = hi;
        lo
    }

    /// Perform n += carry, returning overflow in carry
    fn addassign_carry(n: &mut Self::Base, carry: &mut Self::Base) {
        let (hi, lo) = Self::expanding_add(*n, *carry);
        *carry = hi;
        *n = lo;
    }

    /// Perform n += a + carry, returning overflow in carry
    fn addassign_with_carry(n: &mut Self::Base, a: Self::Base, carry: &mut Self::Base) {
        let sum = n.as_() + a.as_() + carry.as_();
        let (hi, lo) = Self::split_wide_digit(sum);
        *carry = hi;
        *n = lo;
    }

    /// Perform a + b, returning tuple of (high, low) digits
    fn add_expand_doublewide(a: Self::Base, b: Self::BaseDouble) -> (Self::Base, Self::Base) {
        let a: Self::BaseDouble = a.into();
        Self::split_wide_digit(a + b)
    }

    /// Perform a + b, returning tuple of (high, low) digits
    fn expanding_add(a: Self::Base, b: Self::Base) -> (Self::Base, Self::Base) {
        let a: Self::BaseDouble = a.into();
        let b: Self::BaseDouble = b.into();
        Self::split_wide_digit(a + b)
    }

    /// Perform a * b, returning tuple of (high, low) digits
    fn expanding_mul(a: Self::Base, b: Self::Base) -> (Self::Base, Self::Base) {
        let a: Self::BaseDouble = a.into();
        let b: Self::BaseDouble = b.into();
        Self::split_wide_digit(a * b)
    }

    /// Perform a * b + c, returning tuple of (high, low) digits
    fn fused_mul_add(a: Self::Base, b: Self::Base, c: Self::Base) -> (Self::Base, Self::Base) {
        let a: Self::BaseDouble = a.into();
        let b: Self::BaseDouble = b.into();
        let c: Self::BaseDouble = c.into();
        Self::split_wide_digit(a * b + c)
    }

    /// Perform a * b + c + d, returning tuple of (high, low) digits
    fn carrying_mul_add(
        a: Self::Base,
        b: Self::Base,
        c: Self::Base,
        d: Self::Base,
    ) -> (Self::Base, Self::Base) {
        let a: Self::BaseDouble = a.into();
        let b: Self::BaseDouble = b.into();
        let c: Self::BaseDouble = c.into();
        let d: Self::BaseDouble = d.into();
        Self::split_wide_digit(a * b + c + d)
    }

    /// Perform c += a * b + carry, returning overflow in carry
    fn carrying_mul_add_inplace(
        a: Self::Base,
        b: Self::Base,
        c: &mut Self::Base,
        carry: &mut Self::Base,
    ) {
        let a: Self::BaseDouble = a.into();
        let b: Self::BaseDouble = b.into();
        let (hi, lo) = Self::split_wide_digit(a * b + (*c).into() + (*carry).into());
        *c = lo;
        *carry = hi;
    }

    /// Add c into little-endian slice of digits, storing overflow in c
    ///
    /// Starts adding at index 0.
    ///
    fn add_carry_into_slice(dest: &mut [Self::Base], c: &mut Self::Base) {
        Self::add_carry_into(dest.iter_mut(), c)
    }

    /// Iterate over digits in 'dest', adding the carry value until it becomes zero.
    ///
    /// If iterator runs out of digits while carry has a value (i.e. the sum overflows),
    /// the carry value will not be zero.
    ///
    fn add_carry_into<'a, I: Iterator<Item=&'a mut Self::Base>>(dest: I, c: &mut Self::Base) {
        for d in dest {
            if c.is_zero() {
                return;
            }

            let (overflow, sum) = Self::expanding_add(*c, *d);
            *d = sum;
            *c = overflow;
        }
    }

    /// a = a * b + c, storing
    fn mulassign_add_carry(
        a: &mut Self::Base,
        b: Self::Base,
        carry: &mut Self::Base,
    ) {
        let (hi, lo) = Self::expanding_mul(*a, b);
        *a = Self::add_carry(lo, carry);
        *carry += hi;
    }

    /// return value of (lhs - rhs + carry - borrow)
    fn sub_with_carry_borrow(
        lhs: Self::Base,
        rhs: Self::Base,
        carry: &mut Self::Base,
        borrow: &mut Self::Base,
    ) -> Self::Base {
        let mut result = Self::BaseDouble::from(lhs);
        result = result
                    .wrapping_sub(&Self::BaseDouble::from(rhs))
                    .wrapping_add(&(*carry).as_())
                    .wrapping_sub(&(*borrow).as_());

        *borrow = Self::Base::from(result >= (Self::RADIX << 1));
        result = result.wrapping_add(&(borrow.as_() * Self::RADIX));
        debug_assert!(result < (Self::RADIX << 1));

        *carry = Self::Base::from(result >= Self::RADIX);
        result = result - carry.as_() * Self::RADIX;

        return result.as_();
    }
}

/// Radix=*10* / storage=*u8*
#[derive(Copy, Clone, Debug, Default)]
pub struct RADIX_10_u8;

/// Radix=*10,000* storage=*i16*
#[derive(Copy, Clone, Debug, Default)]
pub struct RADIX_10p4_i16;

/// Radix=*1,000,000,000* storage=*u32*
#[derive(Copy, Clone, Debug, Default)]
pub struct RADIX_10p9_u32;

/// Radix=*10,000,000,000,000,000,000* storage=*u64*
#[derive(Copy, Clone, Debug, Default)]
pub struct RADIX_10p19_u64;

/// Radix = 2^<sup>32</sup>
#[derive(Copy, Clone, Debug, Default)]
pub struct RADIX_u32;

/// Radix = 2^<sup>64</sup>
#[derive(Copy, Clone, Debug, Default)]
pub struct RADIX_u64;


pub(crate) trait RadixPowerOfTen: RadixType {
    const DIGITS: usize;

    /// convert number of digits to number of big-digits
    fn divceil_digit_count(digit_count: usize) -> usize {
        use num_integer::Integer;
        Integer::div_ceil(&digit_count, &Self::DIGITS)
    }

    /// convert number of digits to number of big-digits
    fn divmod_digit_count(digit_count: usize) -> (usize, usize) {
        use num_integer::Integer;
        Integer::div_rem(&digit_count, &Self::DIGITS)
    }
}

impl RadixPowerOfTen for RADIX_10p19_u64 {
    const DIGITS: usize = 19;
}
impl RadixPowerOfTen for RADIX_10p9_u32 {
    const DIGITS: usize = 9;
}
impl RadixPowerOfTen for RADIX_10_u8 {
    const DIGITS: usize = 1;
}
impl RadixPowerOfTen for RADIX_10p4_i16 {
    const DIGITS: usize = 4;
}

impl RADIX_10p19_u64 {
    /// Divide double-wide u64 by radix, storing the quotient in the low u64,
    /// and returning the remainder
    pub(crate) fn rotating_div_u64_radix(hi: u64, lo: &mut u64) -> <Self as RadixType>::Base {
        use num_integer::div_rem;
        type BaseDouble = <RADIX_10p19_u64 as RadixType>::BaseDouble;

        let num = BaseDouble::from(*lo) + (BaseDouble::from(hi) << 64);
        let (q, r) = div_rem(num, Self::RADIX);
        *lo = q.as_();
        r.as_()
    }
}

#[cfg(test)]
mod test_validate {
    use super::*;

    macro_rules! impl_case {
        (valid $name:ident : $radix:ident ~ $values:expr) => {
            #[test]
            fn $name() {
                assert!($radix::validate_digits($values.iter()));
            }
        };
        (invalid $name:ident : $radix:ident ~ $values:expr) => {
            #[test]
            fn $name() {
                assert!(!$radix::validate_digits($values.iter()));
            }
        };
    }

    impl_case!(valid case_valid: RADIX_10p4_i16 ~ [1, 2, 3, 4, 5, 600]);
    impl_case!(invalid case_invalid_too_big: RADIX_10p4_i16 ~ [10000, 1, 2, 3, 4, 5, 600]);
    impl_case!(invalid case_invalid_negative: RADIX_10p4_i16 ~ [1, 2, -3, 4, 5, 600]);
    impl_case!(invalid case_invalid_leading_zeros: RADIX_10p4_i16 ~ [0, 1, 2, -3, 4, 5, 600]);
    impl_case!(invalid case_p9_toobig: RADIX_10p9_u32 ~ [3330199352]);
}

impl RadixType for RADIX_u32 {
    type Base = u32;
    type BaseDouble = u64;
    type SignedBase = i32;

    const RADIX: Self::BaseDouble = 1u64 << 32;

    // all u32 are valid in this radix
    fn validate_digits<'a, I: IntoIterator<Item = &'a Self::Base>>(_: I) -> bool {
        true
    }

    fn expanding_add(a: u32, b: u32) -> (u32, u32) {
        let (sum, overflow) = a.overflowing_add(b);
        (u32::from(overflow), sum)
    }
}

impl RadixType for RADIX_u64 {
    type Base = u64;
    type BaseDouble = u128;
    type SignedBase = i64;

    const RADIX: Self::BaseDouble = 1u128 << 64;

    // all u64 are valid in this radix
    fn validate_digits<'a, I: IntoIterator<Item = &'a Self::Base>>(_: I) -> bool {
        true
    }

    fn expanding_add(a: u64, b: u64) -> (u64, u64) {
        let (sum, overflow) = a.overflowing_add(b);
        (u64::from(overflow), sum)
    }
}

impl RadixType for RADIX_10p4_i16 {
    type Base = i16;
    type BaseDouble = i32;
    type SignedBase = i64;

    const RADIX: Self::BaseDouble = 10_000;
}

impl RadixType for RADIX_10p9_u32 {
    type Base = u32;
    type BaseDouble = u64;
    type SignedBase = i32;

    const RADIX: Self::BaseDouble = 1_000_000_000;
}

impl RadixType for RADIX_10p19_u64 {
    type Base = u64;
    type BaseDouble = u128;
    type SignedBase = i64;

    const RADIX: Self::BaseDouble = 10_000_000_000_000_000_000;
}

impl RadixType for RADIX_10_u8 {
    type Base = u8;
    type BaseDouble = u8;
    type SignedBase = i8;

    const RADIX: Self::BaseDouble = 10;
}

#[cfg(test)]
mod tests {
    use super::*;

    include!("radix.tests.rs");
}
