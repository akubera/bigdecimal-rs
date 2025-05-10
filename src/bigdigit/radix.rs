//! Radix definitions
//!
//! Empty structs used to make generic algorithms over kind of radix
//!
#![allow(non_camel_case_types)]

use crate::stdlib::fmt;


/// All the information needed to specify a bigdecimal's radix, and methods operating on integers
pub trait RadixType : Copy + Clone + Default + fmt::Debug {
    /// the inner type of values
    type Base
        : 'static
        + Copy
        + num_integer::Integer
        + num_traits::PrimInt
        + num_traits::FromPrimitive
        + num_traits::Zero
        + num_traits::One;

    /// double wide unsigned type (capable of storing product of two BigDigits)
    type BaseDouble
        : 'static
        + Copy
        + num_integer::Integer
        + num_traits::PrimInt
        + num_traits::FromPrimitive
        + num_traits::Zero
        + num_traits::One
        + num_traits::AsPrimitive<Self::Base>
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
    fn validate_digits<'a, I: IntoIterator<Item=&'a Self::Base>>(i: I) -> bool {
        use num_traits::Zero;
        i.into_iter().map(|&d| d.into()).all(|d| Self::BaseDouble::zero() <= d && d < Self::RADIX)
    }

    fn split_wide_digit(n: Self::BaseDouble) -> (Self::Base, Self::Base) {
        use num_traits::AsPrimitive;

        let (hi, lo) = num_integer::div_rem(n, Self::RADIX);
        return (hi.as_(), lo.as_());
    }

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

    fn add_expand_doublewide(a: Self::Base, b: Self::BaseDouble) -> (Self::Base, Self::Base) {
        let a: Self::BaseDouble = a.into();
        Self::split_wide_digit(a + b)
    }

    fn expanding_add(a: Self::Base, b: Self::Base) -> (Self::Base, Self::Base) {
        let a: Self::BaseDouble = a.into();
        let b: Self::BaseDouble = b.into();
        Self::split_wide_digit(a + b)
    }

    fn expanding_mul(a: Self::Base, b: Self::Base) -> (Self::Base, Self::Base) {
        let a: Self::BaseDouble = a.into();
        let b: Self::BaseDouble = b.into();
        Self::split_wide_digit(a * b)
    }

    fn fused_mul_add(a: Self::Base, b: Self::Base, c: Self::Base) -> (Self::Base, Self::Base) {
        let a: Self::BaseDouble = a.into();
        let b: Self::BaseDouble = b.into();
        let c: Self::BaseDouble = c.into();
        Self::split_wide_digit(a * b + c)
    }

    fn carrying_mul_add(a: Self::Base, b: Self::Base, c: Self::Base, d: Self::Base) -> (Self::Base, Self::Base) {
        let a: Self::BaseDouble = a.into();
        let b: Self::BaseDouble = b.into();
        let c: Self::BaseDouble = c.into();
        let d: Self::BaseDouble = d.into();
        Self::split_wide_digit(a * b + c + d)
    }

    /// Perform c += a * b + carry, returning overflow in carry
    fn carrying_mul_add_inplace(a: Self::Base, b: Self::Base, c: &mut Self::Base, carry: &mut Self::Base) {
        let a: Self::BaseDouble = a.into();
        let b: Self::BaseDouble = b.into();
        let (hi, lo) = Self::split_wide_digit(a * b + (*c).into() + (*carry).into());
        *c = lo;
        *carry = hi;
    }

    fn add_carry_into_slice(dest: &mut [Self::Base], c: &mut Self::Base) {
        use num_traits::Zero;

        for d in dest.iter_mut() {
            if c.is_zero() {
                return;
            }

            let (overflow, sum) = Self::expanding_add(*c, *d);
            *d = sum;
            *c = overflow;
        }
    }
}

/// Radix=*10* / storage=*u8*
#[derive(Copy,Clone,Debug,Default)]
pub struct RADIX_10_u8;

/// Radix=*10,000* storage=*i16*
#[derive(Copy,Clone,Debug,Default)]
pub struct RADIX_10p4_i16;

/// Radix=*1,000,000,000* storage=*u32*
#[derive(Copy,Clone,Debug,Default)]
pub struct RADIX_10p9_u32;

/// Radix=*10,000,000,000,000,000,000* storage=*u64*
#[derive(Copy,Clone,Debug,Default)]
pub struct RADIX_10p19_u64;

/// Radix = 2^<sup>32</sup>
#[derive(Copy,Clone,Debug,Default)]
pub struct RADIX_u32;

/// Radix = 2^<sup>64</sup>
#[derive(Copy,Clone,Debug,Default)]
pub struct RADIX_u64;


pub(crate) trait RadixPowerOfTen : RadixType {
    const DIGITS: usize;
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
    fn validate_digits<'a, I: IntoIterator<Item=&'a Self::Base>>(_: I) -> bool {
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
    fn validate_digits<'a, I: IntoIterator<Item=&'a Self::Base>>(_: I) -> bool {
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

    mod radix_10p19_u64 {
        use super::*;
        use super::RADIX_10p19_u64 as Radix;

        #[test]
        fn split_wide_digit_10e19_0() {
            let (hi, lo) = Radix::split_wide_digit(0);
            assert_eq!(hi, 0);
            assert_eq!(lo, 0);
        }

        #[test]
        fn split_wide_digit_10e19_sqrd() {
            let (hi, lo) = Radix::split_wide_digit(99999999999999999980000000000000000001);
            assert_eq!(hi, 9999999999999999998);
            assert_eq!(lo, 1);
        }

        #[test]
        fn split_wide_digit_5060270152244608514849739578370464703() {
            let (hi, lo) = Radix::split_wide_digit(5060270152244608514849739578370464703);
            assert_eq!(hi, 506027015224460851);
            assert_eq!(lo, 4849739578370464703);
        }

        #[test]
        fn add_with_carry() {
            let mut carry = 20;
            let sum = Radix::add_carry(222292843123382, &mut carry);
            assert_eq!(sum, 222292843123402);
            assert_eq!(carry, 0);
        }

        #[test]
        fn add_with_carry_overflow_18446744073709551600_55() {
            let mut carry = 55;
            let sum = Radix::add_carry(18446744073709551600, &mut carry);
            assert_eq!(sum, 8446744073709551655);
            assert_eq!(carry, 1);
        }

        #[test]
        fn add_with_carry_overflow_2() {
            let result = &mut [0, 1, 2];
            let mut carry = 40;
            Radix::add_carry_into_slice(result, &mut carry);
            assert_eq!(result, &[40, 1, 2]);
            assert_eq!(carry, 0);
        }
    }

    mod radix_u64 {
        use super::*;
        use super::RADIX_u64 as Radix;

        #[test]
        fn add_with_carry_overflow_1() {
            let mut carry = 55;
            let sum = Radix::add_carry(18446744073709551600, &mut carry);
            assert_eq!(sum, 39);
            assert_eq!(carry, 1);
        }

        #[test]
        fn add_with_carry_overflow_2() {
            let result = &mut [0, 1, 2];
            let mut carry = 40;
            Radix::add_carry_into_slice(result, &mut carry);
            assert_eq!(result, &[40, 1, 2]);
            assert_eq!(carry, 0);
        }

        #[test]
        fn add_with_carry_overflow_3() {
            let result = &mut [3533561901698977160, 18446744073709551615, 15318957246294243357];
            let mut carry = 17004058994074047095;
            Radix::add_carry_into_slice(result, &mut carry);
            assert_eq!(result, &[2090876822063472639, 0, 15318957246294243358]);
            assert_eq!(carry, 0);
        }
    }
}
