//! BigDigit types
//!
//! Constants and structures defining the BigDigit used by BigDecimal.
//!
//! These are distinct from the BigDigits in BigIntger
//!

use std::mem::swap;
use num_integer::div_rem;
use num_bigint::Sign;

use crate::arithmetic::{
    addition::add_digit_slices_into,
    multiplication::multiply_digit_slices_into,
};

use crate::context::DEFAULT_PRECISION;


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
    pub fn max() -> BigDigit {
        let max_big_digit = BIG_DIGIT_RADIX - 1;
        BigDigit(max_big_digit as BigDigitBase)
    }

    /// True if big digit is zero
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.0 == 0
    }

    #[inline]
    pub fn is_one(&self) -> bool {
        self.0 == 1
    }

    /// True if BigDigit is ten to the given power
    #[inline]
    pub(crate) fn is_ten_to_power(&self, pow: u8) -> bool {
        if pow == 0 && self.0 == 1 {
            return true;
        }
        if pow % 10 != 0 {
            return false;
        }
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
    pub fn add_carry(&self, carry: &mut BigDigit) -> BigDigit {
        let tmp = self.0 as BigDigitBaseDouble + carry.0 as BigDigitBaseDouble;
        let (overflow, sum) = div_rem(tmp, BIG_DIGIT_RADIX);
        debug_assert!(overflow < BIG_DIGIT_RADIX);
        carry.0 = overflow as BigDigitBase;
        return BigDigit(sum as BigDigitBase);
    }

    /// Return the value of (self + other + carry), store overflow value (0 or 1) in carry
    #[inline]
    pub fn add_with_carry(&self, other: &BigDigit, carry: &mut BigDigit) -> BigDigit {
        let tmp = self.0 as BigDigitBaseDouble + other.0 as BigDigitBaseDouble + carry.0 as BigDigitBaseDouble;
        let (overflow, sum) = div_rem(tmp, BIG_DIGIT_RADIX);
        debug_assert!(overflow < BIG_DIGIT_RADIX);
        carry.0 = overflow as BigDigitBase;
        return BigDigit(sum as BigDigitBase);
    }

    /// Store the value of (self + other + carry) in self, store overflow value (0 or 1) in carry
    #[inline]
    pub fn add_assign_with_carry(&mut self, other: &BigDigit, carry: &mut BigDigit) {
        let tmp = other.0 as BigDigitBaseDouble
                 + self.0 as BigDigitBaseDouble
                 + carry.0 as BigDigitBaseDouble;
        let (overflow, sum) = div_rem(tmp, BIG_DIGIT_RADIX);
        debug_assert!(overflow < BIG_DIGIT_RADIX);
        self.0 = sum as BigDigitBase;
        carry.0 = overflow as BigDigitBase;
    }

    /// Calculate quotient and remainder of bigdigit with argument
    ///
    #[inline]
    pub fn div_rem(self, n: BigDigitBase) -> (BigDigit, BigDigit) {
        let (hi, lo) = div_rem(self.0, n);
        (BigDigit(hi), BigDigit(lo))
    }
}

impl std::fmt::Debug for BigDigit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BigDigit({})", self.0)
    }
}


impl std::ops::Add for BigDigit {
    type Output = (BigDigit, bool);

    fn add(self, rhs: BigDigit) -> Self::Output {
        let sum = self.0 as BigDigitBaseDouble + rhs.0 as BigDigitBaseDouble;
        if sum < BIG_DIGIT_RADIX {
            (BigDigit(sum as BigDigitBase), false)
        } else {
            (BigDigit((sum - BIG_DIGIT_RADIX) as BigDigitBase), true)
        }
    }
}

/// Vector of BigDigits
///
/// This is aliased to make it easier to replace with alternative Vec
/// implementations (i.e. smallvec) in the future.
///
// #[derive(Debug,Clone)]
#[derive(Debug,Default,Clone,Eq,PartialEq)]
// #[derive(Debug,Default,Clone,Copy,Eq,PartialEq,Ord,PartialOrd)]
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

    /// Helper method for extening vector with digits, potentially adding carry
    ///
    pub(crate) fn extend_with_carried_sum<I>(&mut self, digits: I, mut carry: BigDigit)
    where
        I: Iterator<Item=BigDigit>
    {
        if carry.is_zero() {
            for digit in digits {
                self.push(digit);
            }
            return;
        }

        for digit in digits {
            self.push(digit.add_carry(&mut carry));
        }

        if !carry.is_zero() {
            self.push(carry);
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

impl std::cmp::PartialEq<u32> for BigDigit {
    fn eq(&self, other: &u32) -> bool { self.0 == *other }
}

// impl std::cmp::PartialEq<u32> for &BigDigit {
//     fn eq(&self, other: &u32) -> bool { self.0 == *other }
// }

impl std::cmp::PartialEq<BigDigit> for u32 {
    fn eq(&self, other: &BigDigit) -> bool { &other.0 == self }
}

// impl std::cmp::PartialEq<BigDigitVec> for BigDigitVec {
//     fn eq(&self, other: &BigDigitVec) -> bool { &self.0 == &other.0 }
// }

// impl<T: Sized + std::ops::Deref<Target=[BigDigit]>> std::cmp::PartialEq<T> for BigDigitVec {
//     fn eq(&self, other: &T) -> bool { &self.0 == other.deref() }
// }

// impl<T: std::ops::Deref<Target=[BigDigit]>> std::cmp::PartialEq<T> for BigDigitVec {
//     fn eq(&self, other: &T) -> bool { &self.0 == other.deref() }
// }


impl std::cmp::PartialOrd<u32> for BigDigit {
    #[inline]
    fn partial_cmp(&self, other: &u32) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(other)
    }
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
    (10 as BigDigitBase).pow(n)
}

/// Count the number of digits, in slice of bigdigits
///
/// Assumes little endian notation base $10^9$ bigdigits
///
pub(crate) fn count_digits(v: &[BigDigit]) -> usize
{
    debug_assert!(v.len() > 0);
    let digits_in_int = |n: BigDigitBase| {
        if n < 10 {
            1
        } else if n < 100 {
            2
        } else if n < 1000 {
            3
        } else if n < 10000 {
            4
        } else if n < 100000 {
            5
        } else if n < 1000000 {
            6
        } else if n < 10000000 {
            7
        } else if n < 100000000 {
            8
        } else if n < 1000000000 {
            9
        } else {
            unreachable!()
        }
    };

    MAX_DIGITS_PER_BIGDIGIT * (v.len() - 1) + digits_in_int(v[v.len() - 1].0)
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


/// Iterator which splits a stream of BigDigits into hi and low parts
///
/// To be used to align digits
///
pub(crate) struct BigDigitSplitterIter<'a, I>
where
    I: Iterator<Item=&'a BigDigit>
{
    mask: BigDigitBase,
    shift: BigDigitBase,
    prev: BigDigit,
    iter: I,
}

impl<'a, I> BigDigitSplitterIter<'a, I>
where
    I: Iterator<Item=&'a BigDigit>
{
    pub fn new(offset: u32, iter: I) -> Self {
        BigDigitSplitterIter {
            mask: to_power_of_ten(MAX_DIGITS_PER_BIGDIGIT as u32 - offset),
            shift: to_power_of_ten(offset),
            prev: BigDigit::zero(),
            iter: iter,
        }
    }
}

impl<'a, I> Iterator for BigDigitSplitterIter<'a, I>
where
    I: Iterator<Item=&'a BigDigit>
{
    type Item = BigDigit;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(digit) = self.iter.next() {
            let (hi, lo) = digit.split_and_shift(self.mask, self.shift);
            let result = BigDigit(lo.0 + self.prev.0);
            self.prev = hi;
            Some(result)
        } else if self.prev != 0 {
            let last = self.prev;
            self.prev.0 = 0;
            Some(last)
        } else {
            None
        }
    }
}


/// Digit info
///
#[derive(Debug)]
pub(crate) struct DigitInfo {
    /// digits
    pub(crate) digits: BigDigitVec,
    /// scale
    scale: i64,
    /// precision
    precision: std::num::NonZeroI64,
    /// Signed
    sign: Sign,
}

impl Default for DigitInfo {
    fn default() -> DigitInfo {
        DigitInfo {
            precision: std::num::NonZeroI64::new(DEFAULT_PRECISION as i64).unwrap(),
            scale: 0,
            digits: BigDigitVec::default(),
            sign: Sign::NoSign,
        }
    }
}
