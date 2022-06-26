//! BigDigit types
//!
//! Constants and structures defining the BigDigit used by BigDecimal.
//!
//! These are distinct from the BigDigits in BigIntger
//!

use num_integer::div_rem;

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
#[derive(Debug,Default,Clone,Copy,Eq,PartialEq,Ord,PartialOrd)]
pub struct BigDigit(BigDigitBase);

/// type distinguising which parameter is overflow
pub type BigDigitOverflow = BigDigit;

type BigDigitVecBase = Vec<BigDigit>;


impl BigDigit {
    /// Return value zero
    pub fn zero() -> BigDigit {
        BigDigit(0)
    }

    /// Return value one
    pub fn one() -> BigDigit {
        BigDigit(1)
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

    pub fn push_integer<N: Into<u128>>(&mut self, num: N) {
        let a = num.into();
        if a < BIG_DIGIT_RADIX as u128 {
            self.push_raw_integer(a as BigDigitBase);
            return;
        }

        loop {
            let (a, lo) = div_rem(a, BIG_DIGIT_RADIX as u128);
            self.push_raw_integer(lo as BigDigitBase);
            if a == 0 {
                break;
            }
        }
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

pub(crate) fn build_big_digit(x: u32) -> BigDigit {
    BigDigit(x)
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
                if (num as usize) < (BIG_DIGIT_RADIX as usize) {
                    return bigdigit_vec![num as BigDigitBase];
                }
                let mut result = bigdigit_vec![capacity = 3];
                while num as u128 >= BIG_DIGIT_RADIX as u128 {
                    let (hi, lo) = div_rem(num, BIG_DIGIT_RADIX as $t);
                    result.push_raw_integer(lo as BigDigitBase);
                    num = hi;
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
    return n == 1000000000 || n == 100;
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
pub fn to_power_of_ten(n: u32) -> BigDigitBase {
    (10 as BigDigitBase).pow(n)
}

/// Count the number of digits, in slice of bigdigits
///
/// Assumes little endian notation base $10^9$ bigdigits
///
pub(crate) fn count_digits(v: &[BigDigitBase]) -> usize
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

    MAX_DIGITS_PER_BIGDIGIT * (v.len() - 1) + digits_in_int(v[v.len() - 1])
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
                    let count = count_digits(&[$($n),*]);
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
