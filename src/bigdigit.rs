//! BigDigit types
//!
//! Constants and structures defining the BigDigit used by BigDecimal.
//!
//! These are distinct from the BigDigits in BigIntger
//!

use std::mem::swap;
use std::ops::RangeFrom;
use std::marker::PhantomData;
use num_integer::{div_rem, Integer};
use crate::Sign;

use crate::arithmetic::{
    addition::add_digit_slices_into,
    multiplication::multiply_digit_slices_into,
};

use crate::context::{RoundingMode, DEFAULT_PRECISION};


/// The "base type" of the big digit
///
/// This should be the smallest unsigned integer
/// which may hold the radix
pub type BigDigitBase = u32;

/// Integer double the size of BigDigitBase
///
/// Must be able to hold the product of two BigDigitBase objects
pub type BigDigitBaseDouble = u64;

/// Signed version of the double-size BigDigit
pub type BigDigitBaseSignedDouble = i64;

/// Radix (base) of the big digits
pub const BIG_DIGIT_RADIX: BigDigitBaseDouble = 1000000000;

/// Sometimes a i64 is useful
pub(crate) const BIG_DIGIT_RADIX_I64: i64 = BIG_DIGIT_RADIX as i64;

/// Maximum number of decimal-digits stored in each bigdigit
pub const MAX_DIGITS_PER_BIGDIGIT: usize = 9;

/// Maximum value of the BigigitBaseDouble integer type
pub(crate) const MAX_BIG_DIGIT_BASE_DOUBLE: u128 = std::u64::MAX as u128 + 1;

/// Number of bits in one BigDigit
pub const BIG_DIGIT_BITS: usize = std::mem::size_of::<BigDigitBase>() * 8;

/// True if radix is a power of ten
///
/// Many algorithms assume this is true, but when originally
/// written, both powers of 2 and 10 were tried.
///
pub(crate) const RADIX_IS_POWER_OF_TEN: bool = is_power_of_ten(BIG_DIGIT_RADIX);

/// The power of ten in the radix
///
/// should be MAX_DIGITS_PER_BIGDIGIT.
///
pub(crate) const RADIX_POWER_OF_TEN: Option<usize> = power_of_ten(BIG_DIGIT_RADIX);


/// BigDigit type
///
/// A "tuple-struct" type so we may write impls
///
#[derive(Default,Clone,Copy,Eq,PartialEq,Ord,PartialOrd)]
pub struct BigDigit(BigDigitBase);

/// type distinguising which parameter is overflow
pub type BigDigitOverflow = BigDigit;

type BigDigitVecBase = Vec<BigDigit>;


impl BigDigit {
    /// Helper constructor for functions in this crate that dont have access
    /// to the private '.0' field
    ///
    pub(crate) fn from_raw_integer<N: Into<BigDigitBase>>(n: N) -> BigDigit {
        let v = n.into();
        debug_assert!((v as BigDigitBaseDouble) < BIG_DIGIT_RADIX);
        BigDigit(v)
    }

    /// Useful for Rust's default of i32 for integer literals
    /// when building via macros
    ///
    pub(crate) fn from_literal_integer(n: i32) -> BigDigit {
        debug_assert!(n >= 0);
        debug_assert!((n as BigDigitBaseDouble) < BIG_DIGIT_RADIX);
        BigDigit(n as BigDigitBase)
    }

    /// Return value zero
    pub fn zero() -> BigDigit {
        BigDigit(0)
    }

    /// Return value one
    pub fn one() -> BigDigit {
        BigDigit(1)
    }

    /// Return maximum value of a single bigdigit (i.e. RADIX - 1)
    ///
    ///      BIG_DIGIT_RADIX = 1000000000
    ///     max ten-to-power =  999999999
    ///
    #[inline]
    pub fn max() -> BigDigit {
        BigDigit((BIG_DIGIT_RADIX - 1) as BigDigitBase)
    }

    /// Return maximum power of ten a bigdigit may hold
    ///
    ///      BIG_DIGIT_RADIX = 1000000000
    ///     max ten-to-power =  100000000
    ///
    #[inline]
    pub fn max_power_of_ten() -> BigDigit {
        BigDigit((BIG_DIGIT_RADIX / 10) as BigDigitBase)
    }

    /// Create BigDigit as an integer power of ten: 10^p
    #[inline]
    pub(crate) fn ten_to_the(p: BigDigitBase) -> BigDigit {
        debug_assert!((p as usize) < MAX_DIGITS_PER_BIGDIGIT);
        BigDigit(to_power_of_ten(p))
    }

    /// True if big digit is zero
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.0 == 0
    }

    /// True if bigdigit is one
    #[inline]
    pub fn is_one(&self) -> bool {
        self.0 == 1
    }

    /// True if bigdigit is maximum allowed value
    #[inline]
    pub fn is_max(&self) -> bool {
        self.0 as BigDigitBaseDouble == (BIG_DIGIT_RADIX - 1)
    }

    /// True if BigDigit is ten to the given power
    #[inline]
    pub(crate) fn is_ten_to_power(&self, pow: u8) -> bool {
        self.0 == match pow {
            0 => 1,
            1 => 10,
            2 => 100,
            3 => 1000,
            4 => 10000,
            5 => 100000,
            6 => 1000000,
            7 => 10000000,
            8 => 100000000,
            9 => 1000000000,
            _ => { return false; }
        }
    }

    /// True if BigDigit is ten to any power (within RADIX)
    #[inline]
    pub(crate) fn is_power_of_ten(&self) -> bool {
        [1,
         10,
         100,
         1000,
         10000,
         100000 ,
         1000000 ,
         10000000 ,
         100000000 ,
         1000000000 ].binary_search(&self.0).is_ok()
    }

    /// Return the lowest digit and number of zeros preceding it
    ///
    /// (1230000).get_lowest_non_zero_digit() == (3, 4)
    /// (0909090).get_lowest_non_zero_digit() == (9, 1)
    /// (0000008).get_lowest_non_zero_digit() == (8, 0)
    /// (000000).get_lowest_non_zero_digit() == (0, 0)
    ///
    #[inline]
    pub(crate) fn get_lowest_non_zero_digit(&self) -> (u8, usize) {
        // compare implementations: https://rust.godbolt.org/z/4s7MWr4z7
        debug_assert_ne!(self.0, 0);
        if self.0 == 0 {
            return (0, 0);
        }
        /*
        fn recurisve_impl(x: BigDigitBase, n: usize) -> (u8, usize) {
            let y = x % 10;
            if y != 0 {
                (y, n)
            } else {
                recurisve_impl(x / 10, n + 1)
            }
        }
        return recurisve_impl(self.0, 0);
        */
        /*
        macro_rules! impl_condition {
            ($t:literal : $idx:literal) => {
                if self.0 % $t != 0 {
                    let shifted = self.0 / ($t / 10);
                    return ((shifted % 10) as u8, 1);
                }
            }
        }
        impl_condition!(10 : 0);
        impl_condition!(100 : 1);
        impl_condition!(1000 : 2);
        impl_condition!(10000 : 3);
        impl_condition!(100000 : 4);
        impl_condition!(1000000 : 5);
        impl_condition!(10000000 : 6);
        impl_condition!(100000000 : 7);
        impl_condition!(1000000000 : 8);
        unreachable!()
        */
        let mut n = self.0;
        for i in 0.. {
            let y = n % 10;
            if y != 0 {
                return (y as u8, i);
            }
            n /= 10;
        }
        unreachable!();
    }

    /// Count number of digits, ignoring the leading zeros
    ///
    #[inline]
    pub fn significant_digit_count(&self) -> usize {
        if self.0 >= 100000000 {
            9
        } else if self.0 >= 10000000 {
            8
        } else if self.0 >= 1000000 {
            7
        } else if self.0 >= 100000 {
            6
        } else if self.0 >= 10000 {
            5
        } else if self.0 >= 1000 {
            4
        } else if self.0 >= 100 {
            3
        } else if self.0 >= 10 {
            2
        } else {
            1
        }
    }

    /// Return inner 'as' a u8
    pub(crate) fn as_u8(&self) -> u8 {
        self.0 as u8
    }

    /// Return inner 'as' a u32
    pub(crate) fn as_u32(&self) -> u32 {
        self.0 as u32
    }

    /// Return inner 'as' a u64
    pub(crate) fn as_u64(&self) -> u64 {
        self.0 as u64
    }

    /// Return inner 'as' a BigDigitBaseDouble
    pub(crate) fn as_digit_base(&self) -> BigDigitBase {
        self.0
    }

    /// Return inner 'as' a BigDigitBaseDouble
    pub(crate) fn as_digit_base_double(&self) -> BigDigitBaseDouble {
        self.0 as BigDigitBaseDouble
    }

    /// Return inner 'as' a usize
    pub(crate) fn as_usize(&self) -> usize {
        self.0 as usize
    }

    /// Return the lowest digit in bigdigit
    #[inline]
    pub(crate) fn lowest_digit(&self) -> u8 {
        (self.0 % 10) as u8
    }

    /// Return pair of lowest two digits
    #[inline]
    pub fn split_lowest_digits(&self) -> (u8, u8)
    {
        div_rem((self.0 % 100) as u8, 10)
    }

    /// Return the highest digit and remaining big
    #[inline]
    pub(crate) fn split_highest_digit(&self) -> (u8, BigDigitBase) {
        let (hi, rest) = div_rem(self.0, BigDigit::max_power_of_ten().0);
        (hi as u8, rest)
    }

    /// Return the highest digit and non-zero digit
    #[inline]
    pub(crate) fn split_highest_non_zero_digit(&self) -> (u8, BigDigitBase) {
        let (hi, lo) = if self.0 >= 100000000 {
            div_rem(self.0, 100000000)
        } else if self.0 >= 10000000 {
            div_rem(self.0, 10000000)
        } else if self.0 >= 1000000 {
            div_rem(self.0, 1000000)
        } else if self.0 >= 100000 {
            div_rem(self.0, 100000)
        } else if self.0 >= 10000 {
            div_rem(self.0, 10000)
        } else if self.0 >= 1000 {
            div_rem(self.0, 1000)
        } else if self.0 >= 100 {
            div_rem(self.0, 100)
        } else if self.0 >= 10 {
            div_rem(self.0, 10)
        } else {
            (self.0, 0)
        };
        return (hi as u8, lo);
    }

    /// Split the big digit into masked and shifted non-masked parts
    ///
    /// Mask and shift should be factors of BIGDIGIT_RADIX
    ///
    /// 123456.split_and_shift(100, 10000) -> (1234, 560000)
    ///
    #[inline]
    pub fn split_and_shift(self, mask: BigDigitBase, shift: BigDigitBase)
        -> (BigDigit, BigDigit)
    {
        let (hi, lo) = div_rem(self.0, mask);
        (BigDigit(hi), BigDigit(lo * shift))
    }

    /// Add this and another bigdigit into a vector
    #[inline]
    pub fn add_into(&self, rhs: &BigDigit, v: &mut BigDigitVec) {
        let sum = self.0 + rhs.0;
        if (sum as BigDigitBaseDouble) < BIG_DIGIT_RADIX {
            v.push_raw_integer(sum);
        } else {
            let reduced_sum = sum as BigDigitBaseDouble - BIG_DIGIT_RADIX;
            v.push_raw_integer(reduced_sum as BigDigitBase);
            v.push_raw_integer(1u8);
        }
    }

    /// Calculate (self * y) + z
    #[inline]
    pub fn fused_multiply_add(&self, y: &BigDigit, z: &BigDigit)
        -> (BigDigit, BigDigit)
    {
        let product = self.0 as BigDigitBaseDouble
                       * y.0 as BigDigitBaseDouble
                       + z.0 as BigDigitBaseDouble;

        let (hi, lo) = div_rem(product, BIG_DIGIT_RADIX);
        debug_assert!(hi < BIG_DIGIT_RADIX);
        (BigDigit(hi as BigDigitBase), BigDigit(lo as BigDigitBase))
    }

    /// Calculate z += (self * y), returning the carry value
    #[inline]
    pub fn fused_multiply_add_into(&self, y: &BigDigit, z: &mut BigDigit)
        -> BigDigit
    {
        let product = (self.0 as BigDigitBaseDouble
                        * y.0 as BigDigitBaseDouble)
                        + z.0 as BigDigitBaseDouble;

        let (hi, lo) = div_rem(product, BIG_DIGIT_RADIX);
        debug_assert!(hi < BIG_DIGIT_RADIX);
        z.0 = lo as BigDigitBase;
        BigDigit(hi as BigDigitBase)
    }

    /// calculate self += (a * b), returning the carry value
    ///
    /// Alternate form of fused_multiply_add_into with "conventional" naming
    ///
    #[inline]
    pub fn add_assign_product(&mut self, a: &BigDigit, b: &BigDigit)
        -> BigDigit
    {
        a.fused_multiply_add_into(b, self)
    }

    /// Store sum of self plus rhs in self
    ///
    /// Overflow is not checked, use with caution.
    ///
    #[inline]
    pub(crate) fn add_assign(&mut self, rhs: BigDigit) {
        let sum = self.0 as BigDigitBaseDouble + rhs.0 as BigDigitBaseDouble;
        debug_assert!(sum < BIG_DIGIT_RADIX);
        self.0 = sum as BigDigitBase;
    }

    /// Store sum of self plus carry in self and, store new overflow value in carry
    #[inline]
    pub fn add_assign_carry(&mut self, carry: &mut BigDigit) {
        let tmp = self.0 as BigDigitBaseDouble + carry.0 as BigDigitBaseDouble;
        let (overflow, sum) = div_rem(tmp, BIG_DIGIT_RADIX);
        debug_assert!(overflow < BIG_DIGIT_RADIX);
        self.0 = sum as BigDigitBase;
        carry.0 = overflow as BigDigitBase;
    }

    /// Return the value of self plus carry, store overflow value (0 or 1) in carry
    #[inline]
    pub(crate) fn add_carry(&self, carry: &mut BigDigit) -> BigDigit {
        let tmp = self.0 as BigDigitBaseDouble + carry.0 as BigDigitBaseDouble;
        let (overflow, sum) = div_rem(tmp, BIG_DIGIT_RADIX);
        debug_assert!(overflow < BIG_DIGIT_RADIX);
        carry.0 = overflow as BigDigitBase;
        return BigDigit(sum as BigDigitBase);
    }

    /// Return the value of (self + other + carry), store overflow value (0 or 1) in carry
    #[inline]
    pub(crate) fn add_with_carry<N>(&self, other: N, carry: &mut BigDigit) -> BigDigit
    where N: Into<BigDigitBase>
    {
        let tmp = self.0 as BigDigitBaseDouble
                + other.into() as BigDigitBaseDouble
                + carry.0 as BigDigitBaseDouble;
        let (overflow, sum) = div_rem(tmp, BIG_DIGIT_RADIX);
        debug_assert!(overflow < BIG_DIGIT_RADIX);
        carry.0 = overflow as BigDigitBase;
        return BigDigit(sum as BigDigitBase);
    }

    /// Store the value of (self + other + carry) in self, store overflow value (0 or 1) in carry
    #[inline]
    pub fn add_assign_with_carry<N>(&mut self, other: N, carry: &mut BigDigit)
    where N: Into<BigDigitBase>
    {
        let tmp =  self.0 as BigDigitBaseDouble
                 + other.into() as BigDigitBaseDouble
                 + carry.0 as BigDigitBaseDouble;
        let (overflow, sum) = div_rem(tmp, BIG_DIGIT_RADIX);
        debug_assert!(overflow < BIG_DIGIT_RADIX);
        self.0 = sum as BigDigitBase;
        carry.0 = overflow as BigDigitBase;
    }

    /// Store the value of self + other in self, ignore overflow value (0 or 1) in carry
    #[inline]
    pub(crate) fn add_unchecked<N>(&self, other: N) -> BigDigit
    where N: Into<BigDigitBase>
    {
        let rhs = other.into();
        let sum = self.0 + rhs;
        debug_assert!(
            (sum as BigDigitBaseDouble) < BIG_DIGIT_RADIX,
            "{} + {} = {} >= RADIX={}", self.0, rhs, sum, BIG_DIGIT_RADIX
        );
        BigDigit(sum)
    }

    /// Add one to this bigdigit
    ///
    /// Must not be max
    ///
    #[inline]
    pub(crate) fn incremented(&self) -> BigDigit {
        debug_assert_ne!(self.0 as BigDigitBaseDouble, (BIG_DIGIT_RADIX - 1));
        BigDigit(self.0 + 1)
    }

    /// Return the value of self minus borrow, store overflow value (0 or 1) in borrow
    #[inline]
    pub(crate) fn sub_borrow(&self, borrow: &mut BigDigit) -> BigDigit {
        if self.0 < borrow.0 {
            let diff = BIG_DIGIT_RADIX - borrow.0 as BigDigitBaseDouble;
            borrow.0 = 1;
            BigDigit(diff as BigDigitBase)
        } else {
            let diff = self.0 - borrow.0;
            borrow.0 = 0;
            BigDigit(diff)
        }
    }

    /// Return the value of self minus borrow, store overflow value in borrow
    #[inline]
    pub(crate) fn sub_with_borrow<N>(&self, other: N, borrow: &mut BigDigit) -> BigDigit
    where N: Into<BigDigit>
    {
        let mut diff = self.0 as BigDigitBaseSignedDouble
                      - other.into().0 as BigDigitBaseSignedDouble
                      - borrow.0 as BigDigitBaseSignedDouble;

        borrow.0 = 0;
        while diff < 0 {
            borrow.0 += 1;
            diff += BIG_DIGIT_RADIX_I64;
        }
        debug_assert!(diff < BIG_DIGIT_RADIX_I64);
        BigDigit(diff as BigDigitBase)
    }

    /// Store the value of (self - other + carry) in self, store overflow value (0 or 1) in carry
    /// will panic if underflows
    #[inline]
    pub(crate) fn sub_with_carry<N: Into<BigDigit>>(&self, other: N, carry: &mut BigDigit) -> BigDigit {
        let sum = self.0 as BigDigitBaseSignedDouble
                 - other.into().0 as BigDigitBaseSignedDouble
                 + carry.0 as BigDigitBaseSignedDouble;
        debug_assert!(sum >= 0);

        if (sum as BigDigitBaseDouble) < BIG_DIGIT_RADIX {
            carry.0 = 0;
            BigDigit(sum as BigDigitBase)
        } else {
            let (overflow, sum) = div_rem(sum as BigDigitBaseDouble, BIG_DIGIT_RADIX);
            debug_assert!(overflow < BIG_DIGIT_RADIX);
            carry.0 = overflow as BigDigitBase;
            BigDigit(sum as BigDigitBase)
        }
    }

    /// Subtract n from self, returning None if underflow occurs
    #[inline]
    pub(crate) fn checked_sub<N: Into<BigDigitBase>>(&self, n: N) -> Option<BigDigit> {
        self.0.checked_sub(n.into()).map(|diff| BigDigit(diff))
    }

    /// Unchecked sub
    #[inline]
    pub(crate) fn unchecked_sub<N: Into<BigDigitBase>>(&self, n: N) -> BigDigit {
        let rhs = n.into();
        debug_assert!(self.0 >= rhs);
        BigDigit(self.0 - rhs)
    }

    /// Calculate quotient and remainder of bigdigit with argument
    ///
    #[inline]
    pub fn div_rem(self, n: BigDigitBase) -> (BigDigit, BigDigit) {
        let (hi, lo) = div_rem(self.0, n);
        (BigDigit(hi), BigDigit(lo))
    }

    /// Push individual decimal digits in dest
    ///
    /// smallest digit first
    ///
    fn extend_digits_into(&self, dest: &mut Vec<u8>) {
        let mut a = [0u8; MAX_DIGITS_PER_BIGDIGIT];
        let mut d = self.0;
        for i in 1..=MAX_DIGITS_PER_BIGDIGIT {
            a[MAX_DIGITS_PER_BIGDIGIT - i] = (d % 10) as u8;
            d /= 10;
        }
        dest.extend_from_slice(&a[..]);
    }

    /// Push individual decimal digits in dest, ignoring leading zeros
    ///
    /// smallest digit first
    ///
    fn extend_significant_digits_into(&self, dest: &mut Vec<u8>) {
        if self.0 == 0 {
            dest.push(0);
            return;
        }
        let mut a = [0u8; MAX_DIGITS_PER_BIGDIGIT];
        let mut d = self.0;
        for i in 1..=MAX_DIGITS_PER_BIGDIGIT {
            a[MAX_DIGITS_PER_BIGDIGIT - i] = (d % 10) as u8;
            d /= 10;
        }
        let fnz_index = a.iter().position(|&x| x != 0).unwrap();
        dest.extend_from_slice(&a[fnz_index..]);
    }
}

#[cfg(test)]
mod test_impl_bigdigit {
    use super::*;

    mod add_with_carry {
        use super::*;

        macro_rules! impl_case {
            ($name:ident: $x:literal + $y:literal + $carry:literal = $expected:literal, $ecarry:literal) => {
                #[test]
                pub fn $name() {
                    let (x, y) = (BigDigit($x), BigDigit($y));
                    let mut carry = BigDigit($carry);
                    let z = x.add_with_carry(y, &mut carry);
                    let (expected, expected_carry) = (BigDigit($expected), BigDigit($ecarry));
                    assert_eq!(z, expected);
                    assert_eq!(carry, expected_carry);
                }
            }
        }

        impl_case!(case_small: 10 + 9 + 11 = 30, 0);
        impl_case!(case_add_random: 144316306 + 6 + 7 = 144316319, 0);
        impl_case!(case_add_overflow: 999999999 + 9 + 10 = 18, 1);
        impl_case!(case_add_big_overflow: 999999999 + 999999999 + 1 = 999999999, 1);
        impl_case!(case_add_max: 999999999 + 999999999 + 999999999 = 999999997, 2);
    }

    mod sub_with_carry {
        use super::*;

        macro_rules! impl_case {
            ($name:ident: $x:literal - $y:literal + $carry:literal = $expected:literal, $ecarry:literal) => {
                #[test]
                pub fn $name() {
                    let (x, y) = (BigDigit($x), BigDigit($y));
                    let mut carry = BigDigit($carry);
                    let z = x.sub_with_carry(y, &mut carry);
                    let (expected, expected_carry) = (BigDigit($expected), BigDigit($ecarry));
                    assert_eq!(z, expected);
                    assert_eq!(carry, expected_carry);
                }
            }
        }

        impl_case!(case_small: 10 - 9 + 11 = 12, 0);
        impl_case!(case_remove_9: 999999999 - 9 + 10 = 0, 1);
        impl_case!(case_remove_random: 144316306 - 6 + 7 = 144316307, 0);
    }
}

impl std::fmt::Debug for BigDigit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BigDigit({})", self.0)
    }
}

macro_rules! impl_partial_eq {
    (BigDigit < $t:ty) => {
        impl std::cmp::PartialEq<$t> for BigDigit {
            #[inline]
            fn eq(&self, other: &$t) -> bool { self.0 as $t == *other }
        }
        impl std::cmp::PartialEq<BigDigit> for $t {
            #[inline]
            fn eq(&self, other: &BigDigit) -> bool { other.0 as $t == *self }
        }
        impl std::cmp::PartialOrd<$t> for BigDigit {
            #[inline]
            fn partial_cmp(&self, other: &$t) -> Option<std::cmp::Ordering> {
                <$t>::from(self.0).partial_cmp(other)
            }
        }
    };
    (BigDigit > $t:ty) => {
        impl std::cmp::PartialEq<$t> for BigDigit {
            #[inline]
            fn eq(&self, other: &$t) -> bool { self.0.eq(&BigDigitBase::from(*other)) }
        }
        impl std::cmp::PartialEq<BigDigit> for $t {
            #[inline]
            fn eq(&self, other: &BigDigit) -> bool { other.0.eq(&BigDigitBase::from(*self)) }
        }
        impl std::cmp::PartialOrd<$t> for BigDigit {
            #[inline]
            fn partial_cmp(&self, other: &$t) -> Option<std::cmp::Ordering> {
                self.0.partial_cmp(&BigDigitBase::from(*other))
            }
        }
    };
    (BigDigit <> $t:ty) => {
        impl std::cmp::PartialEq<$t> for BigDigit {
            #[inline]
            fn eq(&self, other: &$t) -> bool { (self.0 as i64).eq(&(*other as i64)) }
        }
        impl std::cmp::PartialEq<BigDigit> for $t {
            #[inline]
            fn eq(&self, other: &BigDigit) -> bool { (other.0 as i64).eq(&(*self as i64)) }
        }
        impl std::cmp::PartialOrd<$t> for BigDigit {
            #[inline]
            fn partial_cmp(&self, other: &$t) -> Option<std::cmp::Ordering> {
                (self.0 as i64).partial_cmp(&i64::from(*other))
            }
        }
    };
}

impl_partial_eq!(BigDigit > u8);
impl_partial_eq!(BigDigit > u16);
impl_partial_eq!(BigDigit > u32);
impl_partial_eq!(BigDigit < u64);
impl_partial_eq!(BigDigit < u128);
impl_partial_eq!(BigDigit <> i8);
impl_partial_eq!(BigDigit <> i16);
impl_partial_eq!(BigDigit <> i32);
impl_partial_eq!(BigDigit <> i64);


macro_rules! impl_op {
    ($p:ident; $func:ident; into BigDigitBase => BigDigit) => {
        impl<N: Into<BigDigitBase>> std::ops::$p<N> for BigDigit {
            type Output = BigDigit;
            fn $func(self, rhs: N) -> Self::Output {
                let result = self.0.$func(rhs.into());
                debug_assert!((result as BigDigitBaseDouble) < BIG_DIGIT_RADIX);
                BigDigit(result)
            }
        }
        impl<N: Into<BigDigitBase>> std::ops::$p<N> for &BigDigit {
            type Output = BigDigit;
            fn $func(self, rhs: N) -> Self::Output {
                let result = self.0.$func(rhs.into());
                debug_assert!((result as BigDigitBaseDouble) < BIG_DIGIT_RADIX);
                BigDigit(result)
            }
        }
    };
    ($p:ident; $func:ident; into BigDigitBase => mut BigDigit) => {
        impl<N: Into<BigDigitBase>> std::ops::$p<N> for BigDigit {
            fn $func(&mut self, rhs: N) {
                self.0.$func(rhs.into())
            }
        }
    };
}

impl_op!(Div; div; into BigDigitBase => BigDigit);
impl_op!(DivAssign; div_assign; into BigDigitBase => mut BigDigit);

impl_op!(Rem; rem; into BigDigitBase => BigDigit);
impl_op!(RemAssign; rem_assign; into BigDigitBase => mut BigDigit);


/// Vector of BigDigits
///
/// This is aliased to make it easier to replace with alternative Vec
/// implementations (i.e. smallvec) in the future.
///
// #[derive(Debug,Clone)]
#[derive(Default,Clone,Eq,PartialEq)]
pub struct BigDigitVec(BigDigitVecBase);

impl BigDigitVec {

    /// Make a new BigDigitVec with a new Vec
    pub fn new() -> BigDigitVec {
        BigDigitVec(BigDigitVecBase::new())
    }

    /// Make a new BigDigitVec of a Vec with given capacity
    pub fn with_capacity(capacity: usize) -> BigDigitVec {
        BigDigitVec(BigDigitVecBase::with_capacity(capacity))
    }

    /// Create from slice of primitive integers in little endian order
    ///
    /// Note: These are not validated and should not be used
    ///       outside of building a BigDigitVec from literals
    ///
    pub(crate) fn from_literal_slice(a: &[u32]) -> BigDigitVec {
        use std::iter::Extend;
        let mut v = BigDigitVec::new();
        v.0.extend(a.iter().map(|&d| BigDigit(d)));
        v
    }

    /// True if vector contains value zero
    pub(crate) fn is_zero(&self) -> bool {
        self.0.len() == 1 && self.0[0].is_zero()
    }

    /// Push bigdigit into vector
    pub fn push(&mut self, digit: BigDigit) {
        self.0.push(digit);
    }

    /// Push a single integer into the vector
    ///
    /// Integer MUST be smaller than BIG_DIGIT_RADIX
    ///
    pub(crate) fn push_raw_integer<N: Into<BigDigitBase>>(&mut self, num: N) {
        let value = num.into();
        debug_assert!((value as BigDigitBaseDouble) < BIG_DIGIT_RADIX);
        self.push(BigDigit(value));
    }

    /// Push fully expanded integer into the vector
    ///
    /// To replace the contents of vector with a fully expanded integer, use the
    /// `replace_with` method.
    ///
    #[inline]
    pub fn push_integer<N: Into<u128>>(&mut self, num: N) {
        let a = num.into();
        if a < BIG_DIGIT_RADIX as u128 {
            self.push_raw_integer(a as BigDigitBase);
            return;
        }

        let mut carry = a;
        loop {
            let (hi, lo) = div_rem(carry, BIG_DIGIT_RADIX as u128);
            self.push_raw_integer(lo as BigDigitBase);
            if hi == 0 {
                break;
            }
            carry = hi;
        }
    }

    /// Copy values from the slice into the vec
    ///
    /// Note: zeroes will not be truncated
    ///
    pub fn extend_from_slice(&mut self, slice: &[BigDigit]) {
        self.0.extend_from_slice(slice)
    }

    /// Resize internal vector, filling new entries with copy
    /// of value
    pub fn resize(&mut self, new_len: usize, value: BigDigit) {
        self.0.resize(new_len, value)
    }

    /// Call resize_with
    pub fn resize_with<F>(&mut self, new_len: usize, f: F)
    where
        F: FnMut() -> BigDigit
    {
        self.0.resize_with(new_len, f)
    }

    /// Shorten the length of internal vector to new length
    ///
    /// If current length is shorter, no action is taken
    ///
    pub fn truncate(&mut self, new_len: usize)
    {
        self.0.truncate(new_len)
    }

    /// Clear internal vector
    pub fn clear(&mut self) {
        self.0.clear()
    }

    /// Clear and reserve
    pub fn clear_and_reserve(&mut self, new_size: usize) {
        self.0.clear();
        if self.0.capacity() < new_size {
            self.0.reserve(new_size - self.0.capacity());
        }
    }

    /// Reserve enough space in vector to contain given precision
    #[inline]
    pub fn reserve_precision(&mut self, precision: std::num::NonZeroUsize) {
        let bigdigit_count = precision.get() / (MAX_DIGITS_PER_BIGDIGIT as usize) + 1;
        let additional = bigdigit_count.checked_sub(self.0.capacity()).unwrap_or(0);
        self.0.reserve(additional)
    }

    /// Return index and value of first bigdigit satisfying given predicate
    #[inline]
    pub fn argwhere<P>(&self, predicate: P) -> Option<(usize, &BigDigit)>
    where
        P: Fn(&BigDigit) -> bool
    {
        self.0.iter().position(predicate).map(|idx| (idx, &self.0[idx]))
    }

    /// Search for first bigdigit satisfying given predicate
    ///
    /// This forwards the `std::Vec::find` method
    ///
    #[inline]
    pub fn find<P>(&self, predicate: P) -> Option<&BigDigit>
    where
        P: Fn(&&BigDigit) -> bool
    {
        self.0.iter().find(predicate)
    }

    /// Return position of first bigdigit satisfying given predicate
    ///
    /// This forwards the `std::Vec::position` method
    ///
    #[inline]
    pub fn position<P>(&self, predicate: P) -> Option<usize>
    where
        P: Fn(&BigDigit) -> bool
    {
        self.0.iter().position(predicate)
    }

    /// Return position of first bigdigit less than maximum BigDigit value
    #[inline]
    pub fn position_non_max<P>(&self) -> Option<usize>
    {
        self.0.iter().position(|&d| d != BigDigit::max())
    }

    /// Replace contents with bigdigits of num
    pub fn replace_with<N>(&mut self, num: N)
    where
        N: Into<u128>
    {
        self.0.clear();
        self.push_integer(num);
    }

    /// As slice
    pub fn as_slice(&self) -> &[BigDigit] {
        self.0.as_slice()
    }

    /// Capacity
    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    /// Reserve additional space
    pub fn reserve(&mut self, additional: usize) {
        self.0.reserve(additional)
    }

    /// Remove trailing zeros using Vec::truncate
    pub fn truncate_zeros(&mut self) {
        let nonzero_index = self.0.iter().rposition(|&d| d != 0).unwrap_or(0);
        self.0.truncate(nonzero_index + 1);
    }

    /// Return mutable iterator
    #[inline]
    pub(crate) fn iter_mut(&mut self) -> std::slice::IterMut<BigDigit> {
        self.0.iter_mut()
    }

    /// Return mutable reference to last value in vector
    #[inline]
    pub fn last_mut(&mut self) -> Option<&mut BigDigit> {
        self.0.last_mut()
    }

    /// Helper method for extening vector with digits, potentially adding carry
    ///
    #[inline]
    pub(crate) fn extend_with_carried_sum<I>(&mut self, mut digits: I, mut carry: BigDigit)
    where
        I: Iterator<Item=BigDigit>
    {
        while !carry.is_zero() {
            match digits.next() {
                None => {
                    self.push(carry);
                    carry.0 = 0;  // should we do this?
                    return;
                }
                Some(digit) => {
                    self.push(digit.add_carry(&mut carry));
                }
            }
        }
        self.extend(digits);
    }

    /// Count the number of significant digits in this bigdigit
    #[inline]
    pub(crate) fn count_digits(&self) -> usize {
        count_digits(&self.0)
    }

    /// Shift all digits right by given amount
    ///
    /// This drops the lowest n digits
    ///
    #[inline]
    pub(crate) fn shift_digits_right_by(&mut self, n: usize) {
        if n == 0 {
            return;
        }
        let (skip, offset) = div_rem(n as usize, MAX_DIGITS_PER_BIGDIGIT);
        let new_len = self.0.len() - skip;
        let digits = &mut self.0[0..];

        if offset == 0 {
            for i in 0..new_len {
                digits[i] = digits[skip + i];
            }
            self.0.truncate(new_len);
            return;
        }

        let shifter = ShiftAndMask::mask_low(offset);
        digits[0] = digits[skip] / shifter.mask;
        for i in 1..new_len {
            let (hi, lo) = shifter.split_and_shift(&digits[skip + i]);
            digits[i-1].add_assign(lo);
            digits[i] = hi;
        }

        self.0.truncate(if self.0[new_len - 1].0 == 0 { new_len - 1 } else { new_len });
    }

    /// Return left & right digits and whether all trailing digits
    /// are zero
    ///
    #[inline]
    pub(crate) fn get_rounding_info(&self, idx: usize) -> ((u8, u8), bool) {
        use std::cmp::Ordering::*;

        if idx == 0 {
            let d0 = self.0[0].0 % 10;
            return ((d0 as u8, 0), true);
        }
        else if idx == 1 {
            let d10 = self.0[0].0 % 100;
            let pair = div_rem(d10 as u8, 10);
            return (pair, true);
        }

        // get bigdigit index & offset of digit idx
        let (index, offset) = div_rem(idx, MAX_DIGITS_PER_BIGDIGIT);

        match (index.cmp(&self.0.len()), offset) {
            (Equal, 0) => {
                let (hi_bigdigit, rest) = self.0.split_last().unwrap();
                let (lo_digit, lower_digits) = hi_bigdigit.split_highest_digit();
                let pair = (0, lo_digit as u8);
                let all_trailing_zeros = lower_digits == 0 && rest.iter().all(BigDigit::is_zero);
                (pair, all_trailing_zeros)
            }
            // idx are beyond all our digits
            (Equal, _) | (Greater, _) => {
                let all_trailing_zeros = self.0.iter().all(BigDigit::is_zero);
                ((0, 0), all_trailing_zeros)
            }
            (Less, 1) => {
                let d0 = (self.0[index].0 % 100) as u8;
                let all_trailing_zeros = self.0[..index].iter().all(BigDigit::is_zero);
                (div_rem(d0, 10), all_trailing_zeros)
            }
            (Less, 0) => {
                let mask = to_power_of_ten(MAX_DIGITS_PER_BIGDIGIT as u32 - 1);
                let l = self.0[index].0 % 10;
                let (r, sub) = div_rem(self.0[index - 1].0, mask as u32);
                let all_trailing_zeros = sub == 0 && self.0[..index].iter().all(BigDigit::is_zero);
                ((l as u8, r as u8), all_trailing_zeros)
            }
            _ => {
                let mask = to_power_of_ten(offset as u32 - 1);
                let (d, sub) = div_rem(self.0[index].0, mask);
                let pair = div_rem((d % 100) as u8, 10);
                let all_trailing_zeros = sub == 0 && self.0[..index].iter().all(BigDigit::is_zero);
                (pair, all_trailing_zeros)
            }
        }
    }

    /// Round at digit-index
    #[inline]
    pub(crate) fn round_at(
        &self, round: RoundingMode, sign: Sign, idx: usize
    ) -> BigDigit {
        let (rounding_pair, trailing_digits) = self.get_rounding_info(idx);
        let result = round.round(sign, rounding_pair, trailing_digits);
        BigDigit(result as BigDigitBase)
    }

    /// Remove the rightmost n digits and replace n+1'th digit with new_digit
    ///
    /// Replacement is done via addition, so if new_digit >= 10,
    /// add-with-carry may occur
    ///
    #[inline]
    pub(crate) fn shift_right_and_replace_digit(&mut self, n: usize, new_digit: BigDigitBase) {
        self.shift_digits_right_by(n);
        let old_digit = self.0[0].0 % 10;
        let new_d0 = self.0[0].0 as BigDigitBaseDouble
                   - old_digit as BigDigitBaseDouble
                   + new_digit as BigDigitBaseDouble;

        if new_d0 < BIG_DIGIT_RADIX {
            self.0[0].0 = new_d0 as BigDigitBase;
            return;
        }

        self.0[0].0 = (new_d0 - BIG_DIGIT_RADIX) as BigDigitBase;

        match self.0.iter().skip(1).position(|d| !BigDigit::is_max(d)) {
            // They are all max
            None => {
                self.0[1..].fill_with(BigDigit::zero);
                self.0.push(BigDigit::one());
            }
            // last_max_index is location of last max bigdigit (999999)
            Some(last_max_index) => {
                self.0[1..=last_max_index].fill_with(BigDigit::zero);
                self.0[last_max_index + 1].0 += 1;
            }
        }
    }

    /// Replace contents of self with given digits, rounded at location
    pub(crate) fn fill_with_rounded_digits(
        &mut self, digits: &BigDigitVec, position: usize, sign: Sign, mode: RoundingMode
    ) {
        let (rounding_pair, trailing_zeros) = digits.get_rounding_info(position);
        let rounded_digit = mode.round(sign, rounding_pair, trailing_zeros);
        digits.shift_right_and_replace_digit_into(
            position, rounded_digit.into(), self
        );
    }

    /// Copies digits to the left of the given index into dest, replacing
    /// first digit with new_digit.
    ///
    /// Used for rounding digits to precision
    ///
    #[inline]
    pub(crate) fn shift_right_and_replace_digit_into(&self, n: usize, new_digit: BigDigitBase, dest: &mut BigDigitVec) {
        dest.0.clear();
        dest.0.extend_from_slice(&self.0);
        dest.shift_right_and_replace_digit(n, new_digit);
    }

    /// Get index and digit-offset of digit-index
    #[inline]
    pub fn digit_position_to_bigdigit_index_offset(n: usize) -> (usize, usize) {
        div_rem(n, MAX_DIGITS_PER_BIGDIGIT)
    }
}


impl std::fmt::Debug for BigDigitVec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BigDigitVec([")?;
        if self.0.len() == 0 {
            write!(f, "])")
        } else {
            write!(f, "{}", self.0[0].0)?;
            for big_digit in self.0.iter().skip(1) {
                write!(f, ", {}", big_digit.0)?;
            }
            write!(f, "])")
        }
    }
}

impl From<bool> for BigDigit {
    fn from(val: bool) -> BigDigit { BigDigit::from(val as u8) }
}

impl From<BigDigit> for BigDigitBase {
    fn from(big_digit: BigDigit) -> BigDigitBase { big_digit.0 }
}

impl From<&BigDigit> for BigDigitBase {
    fn from(big_digit: &BigDigit) -> BigDigitBase { big_digit.0 }
}

impl From<BigDigit> for BigDigitBaseDouble {
    fn from(big_digit: BigDigit) -> BigDigitBaseDouble { big_digit.0 as BigDigitBaseDouble }
}

impl From<&BigDigit> for BigDigitBaseDouble {
    fn from(big_digit: &BigDigit) -> BigDigitBaseDouble { big_digit.0 as BigDigitBaseDouble }
}

impl std::borrow::Borrow<[BigDigit]> for BigDigitVec {
    fn borrow(&self) -> &[BigDigit] { self.0.as_ref() }
}

impl AsRef<[BigDigit]> for BigDigitVec {
    fn as_ref(&self) -> &[BigDigit] { self.0.as_ref() }
}

impl AsMut<[BigDigit]> for BigDigitVec {
    fn as_mut(&mut self) -> &mut [BigDigit] { self.0.as_mut() }
}

impl std::ops::Deref for BigDigitVec {
    type Target = [BigDigit];
    fn deref(&self) -> &Self::Target {
        self.0.deref()
    }
}

impl std::ops::Index<usize> for BigDigitVec {
    type Output = BigDigit;
    fn index(&self, index: usize) -> &Self::Output {
        self.0.index(index)
    }
}

impl std::ops::IndexMut<usize> for BigDigitVec {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.0.index_mut(index)
    }
}

impl std::ops::Index<std::ops::RangeTo<usize>> for BigDigitVec {
    type Output = [BigDigit];

    #[inline]
    fn index(&self, index: std::ops::RangeTo<usize>) -> &Self::Output {
        self.0.index(index)
    }
}

impl std::ops::Index<std::ops::RangeFrom<usize>> for BigDigitVec {
    type Output = [BigDigit];

    #[inline]
    fn index(&self, index: std::ops::RangeFrom<usize>) -> &Self::Output {
        self.0.index(index)
    }
}


impl std::iter::Extend<BigDigit> for BigDigitVec {
    /// Extend this vector with values from iterator
    #[inline]
    fn extend<T: IntoIterator<Item=BigDigit>>(&mut self, iter: T) {
        self.0.extend(iter)
    }
}


/// Custom wrapper for easily building BigDigitVec objects
macro_rules! bigdigitbase_vec {
    [ capacity = $capacity:expr ] => {
        BigDigitVecBase::with_capacity($capacity as usize)
    };
    [ $($e:tt)* ] => {
        vec![ $($e)* ]
    };
}

macro_rules! bigdigit_vec {
    [ capacity = $capacity:expr ] => {
        BigDigitVec::with_capacity($capacity as usize)
    };
    [ $($e:expr),* ] => {
        BigDigitVec( bigdigitbase_vec![ $(BigDigit($e)),* ] )
    };
}

macro_rules! bigdigit_array {
    [ $($e:expr),* ] => {
        [ $(BigDigit($e)),* ]
    };
}

macro_rules! impl_from_primitive {
    // special case for NonZero types
    ($target:ty, std::num::$t:ident) => {
        impl From<std::num::$t> for $target {
            fn from(num: std::num::$t) -> Self {
                <$target>::from(num.get())
            }
        }
    };
    (BigDigit, $t:ty) => {
        impl From<$t> for BigDigit {
            fn from(num: $t) -> Self {
                debug_assert!((num as BigDigitBaseDouble) < BIG_DIGIT_RADIX);
                BigDigit(num as BigDigitBase)
            }
        }
    };
    (BigDigitVec, $t:ty) => {
        impl From<$t> for BigDigitVec {
            fn from(mut num: $t) -> Self {
                // cast is optimized away: https://rust.godbolt.org/z/rKjhEqbhf
                if (num as u128) < (BIG_DIGIT_RADIX as u128) {
                    return bigdigit_vec![num as BigDigitBase];
                }
                let mut result = bigdigit_vec![capacity = 3];
                while num as u128 >= BIG_DIGIT_RADIX as u128 {
                    let (hi, lo) = div_rem(num, BIG_DIGIT_RADIX as $t);
                    result.push_raw_integer(lo as BigDigitBase);
                    num = hi;
                }

                if (num != 0) {
                    result.push_raw_integer(num as BigDigitBase);
                }
                return result;
            }
        }
    };
}

impl_from_primitive!(BigDigit, u8);
impl_from_primitive!(BigDigit, u16);
impl_from_primitive!(BigDigit, std::num::NonZeroU8);
impl_from_primitive!(BigDigit, std::num::NonZeroU16);

impl_from_primitive!(BigDigitVec, u8);
impl_from_primitive!(BigDigitVec, u16);
impl_from_primitive!(BigDigitVec, u32);
impl_from_primitive!(BigDigitVec, u64);
impl_from_primitive!(BigDigitVec, u128);
impl_from_primitive!(BigDigitVec, std::num::NonZeroU8);
impl_from_primitive!(BigDigitVec, std::num::NonZeroU16);
impl_from_primitive!(BigDigitVec, std::num::NonZeroU32);
impl_from_primitive!(BigDigitVec, std::num::NonZeroU64);
impl_from_primitive!(BigDigitVec, std::num::NonZeroU128);


impl From<BigDigit> for BigDigitVec {
    fn from(big_digit: BigDigit) -> BigDigitVec {
        BigDigitVec(bigdigitbase_vec![big_digit])
    }
}

/// Build from num-bigint
impl From<num_bigint::BigInt> for BigDigitVec {
    fn from(num: num_bigint::BigInt) -> Self {
        use std::iter::FromIterator;

        let digits = num.iter_u64_digits();
        BigDigitVec::from_iter(digits)
    }
}


macro_rules! from_iter_radix_impl {
    ($ty:ident, $val:ident, $radix:expr) => {{
        let mut digits = $val.into_iter().peekable();
        let digit0 = digits.next().unwrap_or(0);
        if digits.peek() == None {
            return BigDigitVec::from(digit0);
        }

        let capacity = 12;

        // the contents of these vectors will be swapped, so we
        // should initialize all with the same assumed capacity
        let mut result = BigDigitVec::with_capacity(capacity);
        let mut radix_shift_vec = BigDigitVec::with_capacity(capacity);
        let mut digit_vec = BigDigitVec::with_capacity(capacity);
        let mut tmp = BigDigitVec::with_capacity(capacity);

        result.push_integer(digit0);
        radix_shift_vec.push(BigDigit::one());

        let radix_factor = $radix;

        for digit in digits {
            multiply_digit_slices_into(&radix_shift_vec, &radix_factor, &mut tmp);
            swap(&mut radix_shift_vec, &mut tmp);

            // expand next digit into our base by multiplying by radix_shift
            digit_vec.replace_with(digit);
            multiply_digit_slices_into(&digit_vec, &radix_shift_vec, &mut tmp);
            swap(&mut digit_vec, &mut tmp);

            // add_digit_slices_into
            add_digit_slices_into(&result, &digit_vec, &mut tmp);
            swap(&mut result, &mut tmp);
        }

        return result;
    }};
}

/// Build from an iterator of little endian ordered u8 (base 256)
impl std::iter::FromIterator<u8> for BigDigitVec {
    fn from_iter<T: IntoIterator<Item=u8>>(iter: T) -> Self {
        from_iter_radix_impl!(u8, iter, bigdigit_array![256])
    }
}

/// Build from an iterator of little endian ordered u16 (base 2**16)
impl std::iter::FromIterator<u16> for BigDigitVec {
    fn from_iter<T: IntoIterator<Item=u16>>(iter: T) -> Self {
        from_iter_radix_impl!(u16, iter, bigdigit_array![65536])
    }
}

/// Build from an iterator of little endian ordered u32 (base 2**32)
impl std::iter::FromIterator<u32> for BigDigitVec {
    fn from_iter<T: IntoIterator<Item=u32>>(iter: T) -> Self {
        from_iter_radix_impl!(u32, iter, bigdigit_array![294967296, 4])
    }
}

/// Build from an iterator of little endian ordered u64 (base 2**64)
impl std::iter::FromIterator<u64> for BigDigitVec {
    fn from_iter<T: IntoIterator<Item=u64>>(iter: T) -> Self {
        from_iter_radix_impl!(u64, iter, bigdigit_array![709551616, 446744073, 18]) // (u64::MAX as u128) + 1)
    }
}

impl std::iter::FromIterator<u128> for BigDigitVec {
    fn from_iter<T: IntoIterator<Item=u128>>(iter: T) -> Self {
        from_iter_radix_impl!(u128, iter, bigdigit_array![768211456, 374607431, 938463463, 282366920, 340])
    }
}

#[cfg(test)]
mod test_from_iterator {
    use super::*;
    use std::iter::FromIterator;

    include!("test_macros.rs");

    macro_rules! test_impl {
        ($t:ty: [ $($a:literal),* ] -> [ $($r:literal),+ ]) => {{
            let digits = [$($a as $t),*];
            let v = BigDigitVec::from_iter(digits);
            assert_bigdecvec_eq!(v, [$($r),*]);
        }}
    }

    #[test]
    fn case_u8_11() {
        test_impl!(u8: [11] -> [11]);
    }

    #[test]
    fn case_u8_0_11() {
        test_impl!(u8: [0, 11] -> [2816]);
    }

    #[test]
    fn case_u8_20_0_90() {
        test_impl!(u8: [20, 0, 90] -> [5898260]);
    }

    #[test]
    fn case_u8_33_1_0_200() {
        test_impl!(u8: [33, 1, 0, 200] -> [355443489, 3]);
    }

    #[test]
    fn case_u64_19348() {
        test_impl!(u64:[19348] -> [19348]);
    }

    #[test]
    fn case_u64_30064771072() {
        test_impl!(u64:[30064771072] -> [064771072, 30]);
    }


    #[test]
    fn case_u64_292168128485179184529527303802857584559() {
        test_impl!(u64:[10437139363181492143, 15838465981732763176] -> [857584559, 527303802, 179184529, 168128485, 292]);
    }

    #[test]
    fn case_u64_33_1_0_7() {
        test_impl!(u64:[33, 1, 0, 7] -> [951141921, 934855321, 664912734, 525962453, 765346850, 712147706, 43939]);
    }

    #[test]
    fn case_u64_214312396452670092584246748532518639826000000000() {
        test_impl!(u64: [5956997386804507648, 6516318922729427074, 629807528] ->[0, 518639826, 246748532, 670092584, 312396452, 214]);
    }

    #[test]
    fn case_u64_31200072108630795005561881570000000000355287053() {
        test_impl!(u64: [6732661218595913741, 5024132863428368696, 91688771] ->[355287053, 0, 561881570, 630795005, 200072108, 31]);
    }

    #[test]
    fn case_u128_7820187036182534517127554804841109227374071() {
        test_impl!(u128: [157961972447688275742951451643959903735, 22981]
            -> [227374071, 804841109, 517127554, 36182534, 7820187]);
    }

}


/// returns true if number is a power of ten (10^x)
#[cfg(rustc_1_46)]
const fn is_power_of_ten(n: BigDigitBaseDouble) -> bool {
    match n % 10 {
        1 => n == 1,
        0 => is_power_of_ten(n / 10),
        _ => false,
    }
}

/// Assume true for older versions of rust, this should ONLY
/// be used in definition of RADIX_IS_POWER_OF_TEN
#[cfg(not(rustc_1_46))]
const fn is_power_of_ten(n: BigDigitBaseDouble) -> bool {
    match n {
        1 | 10 | 100 | 1000 | 10000 | 100000 | 1000000 |
        10000000 | 100000000 | 1000000000 => { true },
        _ => { false }
    }
}


/// Calculate log10(n)
#[cfg(rustc_1_46)]
const fn power_of_ten(n: BigDigitBaseDouble) -> Option<usize> {
    match n {
        1 => Some(0),
        0..=9 => None,
        _ if n % 10 != 0 => None,
        _ => match power_of_ten(n / 10) {
            None => None,
            Some(p) => Some(1 + p),
        },
    }
}


/// Can not calculate earlier than Rust 1.46 - should ONLY
/// be used in definition of RADIX_POWER_OF_TEN
#[cfg(not(rustc_1_46))]
const fn power_of_ten(n: BigDigitBaseDouble) -> Option<usize> {
    match n {
        100 => Some(2),
        1000000000 => Some(9),
        _ => unimplemented!()
    }
}


#[cfg(rustc_1_46)]
#[cfg(test)]
mod test_power_of_ten {
    use super::*;

    macro_rules! impl_case {
        ($n:literal, $expected:expr) => {
            paste! {
                #[test]
                fn [< case_ $n >]() {
                    assert_eq!(power_of_ten($n), $expected);
                }
            }
        };
    }

    impl_case!(1, Some(0));
    impl_case!(100, Some(2));
    impl_case!(10000, Some(4));

    impl_case!(101, None);
    impl_case!(200, None);
}


/// Calculate 10^n
///
#[inline]
pub(crate) fn to_power_of_ten(n: u32) -> BigDigitBase {
    match n {
        0 => 1,
        1 => 10,
        2 => 100,
        3 => 1000,
        4 => 10000,
        5 => 100000,
        6 => 1000000,
        7 => 10000000,
        8 => 100000000,
        9 => 1000000000,
        _ => unreachable!()
    }
}

/// Count the number of digits, in slice of bigdigits
///
/// Assumes little endian notation base $10^9$ bigdigits
///
#[inline]
pub(crate) fn count_digits(v: &[BigDigit]) -> usize
{
    MAX_DIGITS_PER_BIGDIGIT * (v.len() - 1) + v[v.len() - 1].significant_digit_count()
}

#[cfg(test)]
mod test_count_digits {
    use super::*;

    macro_rules! test_case {
        ( $n:literal; $expected:literal ) => {
            test_case!((NAME = $n); [$n]; $expected);
        };
        ( [$($n:literal),*] ; $expected:literal ) => {
            test_case!( (NAME $($n)* = ); [$($n),*]; $expected );
        };
        ( (NAME $head:literal $($rest:literal)* = $($name:literal)*); [$($n:literal),*]; $expected:literal ) => {
            test_case!( (NAME $($rest)* = $head $($name)*); [$($n),*]; $expected );
        };
        ( (NAME = $($name:literal)*); [$($n:literal),*]; $expected:literal ) => {
            paste! {
                #[test]
                fn [< case_ $($name)* >]() {{
                    let count = count_digits(&[$(BigDigit($n)),*]);
                    assert_eq!(count, $expected);
                }}
            }
        };
    }

    test_case!(0; 1);
    test_case!(1; 1);
    test_case!(2; 1);
    test_case!(9; 1);
    test_case!(10; 2);
    test_case!(99; 2);
    test_case!(199; 3);
    test_case!(301548653; 9);
    test_case!([384309465, 765728666, 201]; 21);
    test_case!(
        [70592446, 177162782, 274783218, 24352950, 191976889,
            216917990, 28818228, 5216000]; 70);
}



#[cfg(test)]
mod test_bigdigitvec {
    use super::*;

    macro_rules! rev_bigdigit_vec {
        ( $a0:literal $($ar:literal)* ) => {
            rev_bigdigit_vec!(REV $($ar)*; $a0)
        };
        ( REV ; $($a:literal)+ ) => {
            bigdigit_vec![ $($a),* ]
        };
        ( REV $a0:literal $($ar:literal)* ; $($a:literal)* ) => {
            rev_bigdigit_vec!(REV $($ar)*; $a0 $($a)*)
        };
    }

    mod shift_right_and_replace_digit {
        use super::*;

        macro_rules! impl_test {
            ( $idx:literal, $d:literal => $($expected:literal)+ ) => {
                paste! {
                    #[test]
                    fn [< at_ $idx _digit_ $d >] () {
                        let mut v = case_input!();
                        let expected = rev_bigdigit_vec!( $($expected)* );
                        v.shift_right_and_replace_digit($idx, $d);
                        assert_eq!(v, expected);
                    }
                }
            }
        }

        mod case_103_438312901 {
            use super::*;

            macro_rules! case_input {
                () => { rev_bigdigit_vec!(103 438312901) }
            }
            impl_test!(0, 5 => 103 438312905);
            impl_test!(0, 10 => 103 438312910);

            impl_test!(1, 9 => 10 343831299);
            impl_test!(9, 9 => 109);
            impl_test!(9, 900 => 1000);
            impl_test!(9, 99999999 => 100000099);
            impl_test!(9, 999999999 => 1 000000099);
        }

        mod case_734999999999 {
            use super::*;

            macro_rules! case_input {
                () => { rev_bigdigit_vec!(734 999999999) }
            }
            // impl_test!(3, 5 => 734 999999001);

            impl_test!(0, 0 => 734 999999990);
            impl_test!(0, 10 => 735 000000000);

            impl_test!(1, 10 => 73 500000000);

            impl_test!(1, 13 => 73 500000003);
        }

        mod case_2901999999999999999991 {
            use super::*;

            macro_rules! case_input {
                () => { rev_bigdigit_vec!(2901 999999999 999999991) }
            }

            impl_test!(0, 10 => 2902 000000000 000000000);
            impl_test!(1, 19 => 290 200000000 000000009);
            impl_test!(1, 100 => 290 200000000 000000090);
            // impl_test!(1, 1 => 2901999999999999999991);

            impl_test!(7, 1 => 290199 999999991);
            impl_test!(14, 1 => 29019991);
        }

        mod case_999999999999999999999999992 {
            use super::*;

            macro_rules! case_input {
                () => { rev_bigdigit_vec!(999999999 999999999 999999992) }
            }

            impl_test!(0, 13 => 1 000000000 000000000 000000003);
            impl_test!(1, 18 => 100000000 000000000 000000008);

            impl_test!(1, 1 => 99999999 999999999 999999991);

            impl_test!(9, 2 => 999999999 999999992);
            impl_test!(9, 12 => 1 000000000 000000002);

            impl_test!(12, 12 => 1000000 000000002);
        }

        mod case_6150000001382230669832999999999999999999999999999999999992 {
            use super::*;

            macro_rules! case_input {
                () => { rev_bigdigit_vec!(6150 000001382 230669832 999999999 999999999 999999999 999999992) }
            }

            impl_test!(0, 15 => 6150 000001382 230669833 000000000 000000000 000000000 000000005);
            impl_test!(1, 16 =>  615  00000138 223066983 300000000 000000000 000000000 000000006);

            // impl_test!(1, 1 => 2901999999999999999991);

            impl_test!(9, 4 => 6150 1382 230669832 999999999 999999999 999999994);
            impl_test!(9, 24 => 6150 1382 230669833 000000000 000000000 000000014);
            impl_test!(12, 12 => 6 150000001 382230669 833000000 000000000 000000002 );
        }

        mod case_123008747439 {
            use super::*;

            macro_rules! case_input {
                () => { rev_bigdigit_vec!(123 008747439) }
            }

            impl_test!(0, 0 => 123 8747430);
            impl_test!(1, 9 => 12 300874749);
        }

        mod case_8747439123 {
            use super::*;

            macro_rules! case_input {
                () => { rev_bigdigit_vec!(8747439 123) }
            }

            impl_test!(1, 9 => 874743 900000019);
        }
    }
}

/// Object used to shift and mask decimal digits
///
/// Uses div and rem to "mask" decimals using powers of 10.
///
/// 987654321 % 10000  => 000004321
/// 987654321 / 10000  => 000098765 ('shifted' => 987600000)
///
/// ShiftAndMask(4).split_and_shift(98765321) -> (98760000, 000005321)
/// ShiftAndMask(1).split_and_shift(98765321) -> (98760000, 000005321)
///
struct ShiftAndMask {
    shift: BigDigitBase,
    mask: BigDigitBase,
}

impl ShiftAndMask {

    /// Build such that (X % mask) 'keeps' n digits of X
    fn mask_low(n: usize) -> Self {
        debug_assert!(n < MAX_DIGITS_PER_BIGDIGIT);
        let mask = to_power_of_ten(n as u32);
        let shift = to_power_of_ten((MAX_DIGITS_PER_BIGDIGIT - n) as u32);
        Self { shift, mask }
    }

    /// Build such that (X / mask) 'keeps' n digits of X
    fn mask_high(n: usize) -> Self {
        Self::mask_low(MAX_DIGITS_PER_BIGDIGIT - n as usize)
    }

    /// Split bigdigit into high and low digits
    ///
    /// ShiftAndMask::mask_high(3).split(987654321) => (987000000, 000654321)
    /// ShiftAndMask::mask_low(3).split(987654321)  => (987654000, 000000321)
    ///
    #[inline]
    fn split(&self, n: &BigDigit) -> (BigDigit, BigDigit) {
        let (hi, lo) = div_rem(n.0, self.mask);
        (BigDigit(hi * self.mask), BigDigit(lo))
    }

    /// Split and shift such that the n "high" bits are on low
    /// side of digit and low bits are at the high end
    ///
    /// ShiftAndMask::mask_high(3).split_and_shift(987654321) => (000000987, 654321000)
    /// ShiftAndMask::mask_low(3).split_and_shift(987654321)  => (000987654, 321000000)
    ///
    #[inline]
    fn split_and_shift(&self, n: &BigDigit) -> (BigDigit, BigDigit) {
        n.split_and_shift(self.mask, self.shift)
    }
}


#[cfg(test)]
mod test_shift_and_mask {
    use super::*;

    macro_rules! impl_test_cases {
        ($num:literal => split split-and-shift
            $( $mask_func:ident @ $n:literal = ($s1:literal, $s2:literal) ($r1:literal, $r2:literal) )*
        ) => {
            $(
                paste!{
                    #[test]
                    fn [< test_ $mask_func _ $n _ split _ $num >]() {
                        let x = BigDigit($num);
                        let s = ShiftAndMask::$mask_func($n);
                        assert_eq!(s.split(&x), (BigDigit($s1), BigDigit($s2)));
                    }

                    #[test]
                    fn [< test_ $mask_func _ $n _ split_and_shift _ $num >]() {
                        let x = BigDigit($num);
                        let s = ShiftAndMask::$mask_func($n);
                        assert_eq!(s.split_and_shift(&x), (BigDigit($r1), BigDigit($r2)));
                    }
                }
            )*
        }
    }

    impl_test_cases!{
        987654321 =>    split                    split-and-shift
         mask_low @ 1 = (987654320, 000000001)   (098765432, 100000000)
         mask_low @ 2 = (987654300, 000000021)   (009876543, 210000000)
         mask_low @ 4 = (987650000, 000004321)   (000098765, 432100000)
        mask_high @ 2 = (980000000, 007654321)   (000000098, 765432100)
        mask_high @ 4 = (987600000, 000054321)   (000009876, 543210000)
        mask_high @ 8 = (987654320, 000000001)   (098765432, 100000000)
    }

    #[test]
    fn complimentary_values() {
        for (i, j) in (1..MAX_DIGITS_PER_BIGDIGIT).zip(MAX_DIGITS_PER_BIGDIGIT-1..0) {
            let lo = ShiftAndMask::mask_low(i);
            let hi = ShiftAndMask::mask_high(j);
            assert_eq!(lo.mask, hi.mask);
            assert_eq!(lo.shift, hi.shift);
        }
    }
}


/// Wrap shift-and-mask type with special-case for zero shift
///
enum ShiftState {
    Zero,
    Shifted { mask: ShiftAndMask, prev: BigDigit },
}


impl ShiftState {

    /// Start with the lower n digits of the first bigdigit, shifted up
    ///
    /// 987654321, 3 => [32100000, xxx987654]
    ///
    #[inline]
    fn starting_with_bottom(n: usize) -> Self {
        if n == 0 {
            Self::Zero
        } else {
            Self::Shifted {
                mask: ShiftAndMask::mask_low(n),
                prev: BigDigit::zero(),
            }
        }
    }

    /// Start with the lower digits of the first bigdigit, shifted up by n
    ///
    /// 987654321, 3 => [654321000, xxxxxx987]
    ///
    #[inline]
    fn shifting_left_by(n: usize) -> Self {
        if n == 0 {
            Self::Zero
        } else {
            Self::Shifted {
                mask: ShiftAndMask::mask_high(n),
                prev: BigDigit::zero(),
            }
        }
    }

    /// Start with the high digits of the first bigdigit, shifted down by n
    ///
    /// 987654321, 3 => [xxx987654]
    ///
    #[inline]
    fn shifting_right_by<'a, I>(n: usize, digits: &mut I) -> Self
    where
        I: Iterator<Item=&'a BigDigit>
    {
        if n == 0 {
            Self::Zero
        } else {
            let mask = ShiftAndMask::mask_low(n as usize);
            let first_digit = digits.next().map(|&d| d.0 / mask.mask).unwrap_or(0);
            Self::Shifted {
                mask: mask,
                prev: BigDigit(first_digit),
            }
        }
    }

    /// Start with high n digits of the first bigdigit
    ///
    /// 987654321, 3 => [xxxxxx987]
    ///
    #[inline]
    fn starting_with_top<'a, I>(n: usize, digits: &mut I) -> Self
    where
        I: Iterator<Item=&'a BigDigit>
    {
        if n == 0 {
            Self::Zero
        } else {
            let mask = ShiftAndMask::mask_high(n as usize);
            let first_digit = digits.next().map(|&d| d.0 / mask.mask).unwrap_or(0);
            Self::Shifted {
                mask: mask,
                prev: BigDigit(first_digit),
            }
        }
    }
}

/// Object for iterating big-digits which have been split for realignment
///
pub(crate) struct BigDigitSplitterIter<'a, I>
{
    shift: ShiftState,
    digits: I,
    phantom: std::marker::PhantomData<&'a ()>,
}


impl<'a> BigDigitSplitterIter<'a, std::slice::Iter<'a, BigDigit>>
{
    /// Build without shifting digits
    #[inline]
    pub(crate) fn from_slice(slice: &'a [BigDigit]) -> Self {
        Self {
            shift: ShiftState::Zero,
            digits: slice.iter(),
            phantom: std::marker::PhantomData,
        }
    }

    /// Stream will behave as if adding n zeros to beginning of digits
    ///
    /// 987654321 : n=3 => 654321000
    ///
    #[inline]
    pub(crate) fn from_slice_shifting_left(slice: &'a [BigDigit], n: usize) -> Self {
        Self {
            shift: ShiftState::shifting_left_by(n),
            digits: slice.iter(),
            phantom: std::marker::PhantomData,
        }
    }

    /// Stream will behave as if removing n digits from the stream
    ///
    /// 987654321 : n=3 => xxx987654
    ///
    /// This is the second digit of `from_slice_starting_bottom`
    ///
    #[inline]
    pub(crate) fn from_slice_shifting_right(slice: &'a [BigDigit], n: usize) -> Self {
        let mut digits = slice.iter();
        Self {
            shift: ShiftState::shifting_right_by(n, &mut digits),
            digits: digits,
            phantom: std::marker::PhantomData,
        }
    }

    /// First digit will be the bottom n digits shifted to top
    ///
    /// 987654321 : n=3 => 321000000
    ///
    #[inline]
    pub(crate) fn from_slice_starting_bottom(slice: &'a [BigDigit], n: usize) -> Self {
        Self {
            shift: ShiftState::starting_with_bottom(n),
            digits: slice.iter(),
            phantom: std::marker::PhantomData,
        }
    }

    /// First digit will be the top n digits shifted to bottom
    ///
    /// 987654321 : n=3 => xxxxxx987
    ///
    /// This is the second digit of `from_slice_shifting_left`
    ///
    #[inline]
    pub(crate) fn from_slice_starting_top(slice: &'a [BigDigit], n: usize) -> Self {
        let mut digits = slice.iter();
        Self {
            shift: ShiftState::starting_with_top(n, &mut digits),
            digits: digits,
            phantom: std::marker::PhantomData,
        }
    }

    /// Copy all remaining digits into destination vector
    pub fn extend_vector(self, dest: &mut BigDigitVec) {
        if let Self { shift: ShiftState::Zero, ref digits, .. } = self {
            dest.extend_from_slice(digits.as_slice());
        } else {
            dest.extend(self);
        }
    }

    /// Return the internal 'mask' value
    pub(crate) fn mask(&self) -> BigDigitBase {
        return match self.shift {
            ShiftState::Zero => { 0 },
            ShiftState::Shifted { mask: ref shift_and_mask, .. } => { shift_and_mask.mask }
        }
    }

    /// Returns the value of the 'shift' with one subtracted
    ///
    /// Useful for adding nines to first result of `from_slice_starting_bottom`
    ///
    pub fn shift_minus_one(&self) -> BigDigitBase {
        match self {
            BigDigitSplitterIter { shift: ShiftState::Zero, .. } => {
                (BIG_DIGIT_RADIX - 1) as BigDigitBase
            },
            BigDigitSplitterIter { shift: ShiftState::Shifted { mask, .. }, .. } => {
                mask.shift - 1
            }
        }
    }
}

// impl<'a> Iterator for BigDigitSplitterIter<'a, std::slice::Iter<'a, BigDigit>>
impl<'a, I> Iterator for BigDigitSplitterIter<'a, I>
where
    I: Iterator<Item=&'a BigDigit>
{
    type Item = BigDigit;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            BigDigitSplitterIter {
                shift: ShiftState::Zero,
                ref mut digits,
                ..
            } => {
                digits.next().copied()
            },
            BigDigitSplitterIter {
                shift: ShiftState::Shifted { mask: shifter, ref mut prev },
                ref mut digits,
                ..
            } => match digits.next() {
                Some(next_digit) => {
                    let (hi, lo) = shifter.split_and_shift(next_digit);
                    let carry = std::mem::replace(prev, hi);
                    Some(BigDigit(lo.0 + carry.0))
                }
                None if !prev.is_zero() => {
                    let last_digit = std::mem::replace(prev, BigDigit::zero());
                    Some(last_digit)
                }
                None => None,
            },
        }
    }

    /// Used for optimization
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.digits.size_hint()
    }
}


impl<'a, I> std::iter::ExactSizeIterator for BigDigitSplitterIter<'a, I>
where
    I: std::iter::ExactSizeIterator<Item=&'a BigDigit>
{
    /// Used for optimization
    fn len(&self) -> usize {
        self.digits.len()
    }
}

#[cfg(test)]
mod test_big_digit_splitter_iter {
    use super::*;

    // Test the _from_slice methods
    //
    // enforces: from_slice_shifting_right(n)[1..] == from_slice_starting_bottom(n)
    //             from_slice_starting_top(n)[1..] == from_slice_shifting_left(n)
    //
    macro_rules! impl_test {
        (from_slice_starting_bottom([$($input:literal),+], $n:literal) == [$($expected:literal),+]) => {
            impl_test!(from_slice_starting_bottom; $($input)*; $n; $($expected)*; false);
            impl_test!(from_slice_shifting_right; $($input)*; $n; $($expected)*; $n != 0);
        };
        (from_slice_shifting_left([$($input:literal),+], $n:literal) == [$($expected:literal),+]) => {
            impl_test!(from_slice_shifting_left; $($input)*; $n; $($expected)*; false);
            impl_test!(from_slice_starting_top; $($input)*; $n; $($expected)*; $n != 0);
        };
        ($func:ident([$($input:literal),+], $n:literal) == [$($expected:literal),+]) => {
            impl_test!($func; $($input)*; $n; $($expected)*; false);
        };
        ($func:ident; $($input:literal)+; $n:literal; $($expected:literal)+; $skip:expr) => {
            paste! {
                #[test]
                fn [< test_ $func $(_ $input)* _ $n >]() {
                    let digits = bigdigit_vec![$($input),*];
                    let iter = BigDigitSplitterIter::$func(&digits, $n);
                    let output = iter.map(u32::from).collect::<Vec<u32>>();
                    let expected = [$($expected),*];
                    let skip = if $skip { 1 } else { 0 };
                    assert_eq!(&output, &expected[skip..]);
                }
            }
        }
    }

    // these include from_slice_starting_top tests
    impl_test!(from_slice_shifting_left([1], 2) == [100]);
    impl_test!(from_slice_shifting_left([806938958], 0) == [806938958]);
    impl_test!(from_slice_shifting_left([806938958], 1) == [069389580, 8]);
    impl_test!(from_slice_shifting_left([806938958], 3) == [938958000, 806]);

    impl_test!(from_slice_shifting_left([861590398, 169326016], 0) == [861590398, 169326016]);
    impl_test!(from_slice_shifting_left([861590398, 169326016], 3) == [590398000, 326016861, 169]);

    // these include from_slice_shifting_right tests
    impl_test!(from_slice_starting_bottom([806938958], 0) == [806938958]);
    impl_test!(from_slice_starting_bottom([806938958], 1) == [800000000, 80693895]);
    impl_test!(from_slice_starting_bottom([806938958], 2) == [580000000, 8069389]);

    impl_test!(from_slice_starting_bottom([127887266, 554762514, 7488], 0) == [127887266, 554762514, 7488]);
    impl_test!(from_slice_starting_bottom([127887266, 554762514, 7488], 5) == [872660000, 625141278, 74885547]);
    impl_test!(from_slice_starting_bottom([127887266, 554762514, 7488], 8) == [278872660, 547625141, 74885]);

    impl_test!(from_slice_starting_bottom([861590398, 169326016], 3) == [398000000, 016861590, 169326]);


    #[test]
    fn case_shift_minus_one() {
        let digits = [BigDigit(987654321)];
        let mut iter = BigDigitSplitterIter::from_slice_starting_bottom(&digits, 3);
        let first_digit = iter.next().unwrap();
        let nines = iter.shift_minus_one();

        assert_eq!(first_digit.0 + nines, 321999999);
        assert_eq!(iter.next().unwrap().0, 987654);
        assert_eq!(iter.next(), None);
    }
}


/// Digit info
///
#[derive(Debug,Eq,PartialEq)]
pub(crate) struct DigitInfo {
    /// digits
    pub(crate) digits: BigDigitVec,
    /// scale
    pub(crate) scale: i64,
    /// Signed
    pub(crate) sign: Sign,
}

impl DigitInfo {
    /// Count number of digits stored in digit vec
    pub fn count_digits(&self) -> usize {
        count_digits(&self.digits)
    }

    /// Return pair of numbers to be added
    pub fn rounding_pair(&self, digit_position: usize) -> (u8, u8) {
        if digit_position == 0 {
            return ((self.digits[0].0 % 10) as u8, 0);
        }
        let (idx, offset) = div_rem(digit_position, MAX_DIGITS_PER_BIGDIGIT);
        if offset == 0 {
            let left = self.digits[idx].0 % 10;
            let right = self.digits[idx-1].0 / 100000000;
            (left as u8, right as u8)
        }
        else if offset == 1 {
            let low_two = self.digits[idx].0 % 100;
            div_rem(low_two as u8, 10)
        } else {
            let shifter = to_power_of_ten(offset as BigDigitBase - 1);
            let shifted = self.digits[idx].0 / shifter;
            let low_two = shifted % 100;
            div_rem(low_two as u8, 10)
        }
    }

    /// Return as a vector of individual decimal digits in little endian order
    pub fn as_decimal_digits(&self) -> Vec<u8> {
        let mut result = Vec::with_capacity(MAX_DIGITS_PER_BIGDIGIT * self.digits.0.len());
        if let Some((last, rest)) = self.digits.0.split_last() {
            last.extend_significant_digits_into(&mut result);
            for d in rest.iter().rev() {
                d.extend_digits_into(&mut result);
            }
        } else {
            result.push(0);
        }
        result
    }

    /// Copy other DigitInfo into this object, respecting given precision and rounding
    pub fn copy_with_precision(
        &mut self,
        other: &DigitInfo,
        precision: std::num::NonZeroUsize,
        rounding_mode: RoundingMode
    ) {
        self.sign = other.sign;
        self.digits.reserve_precision(precision);
        let digit_count = self.count_digits();
        match digit_count.checked_sub(precision.get()) {
            // Not enough digits means we don't need to round
            Some(0) | None => {
                self.scale = other.scale;
                self.digits.extend_from_slice(other.digits.as_slice());
            }
            // We need to round to lower precision
            Some(digit_position) => {
                self.digits.fill_with_rounded_digits(
                    &other.digits, digit_position, other.sign, rounding_mode
                );
                self.scale = other.scale + digit_position as i64;
            }
        }
    }
}


impl Default for DigitInfo {
    fn default() -> DigitInfo {
        DigitInfo {
            scale: 0,
            digits: BigDigitVec::default(),
            sign: Sign::NoSign,
        }
    }
}
