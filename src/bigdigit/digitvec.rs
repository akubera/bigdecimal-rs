//! Digit vectors (and slices) of arbitrary radix and endianness

use stdlib::{
    Vec,
    marker::PhantomData,
};

use num_traits::Zero;

use super::radix::*;
use super::endian::*;


/// Vector of integers, interpreted as bigdigits in an integer
///
/// Value of the integer is defined by the radix and endianness
/// type parameters.
///
#[derive(Debug)]
pub(crate) struct DigitVec<R: RadixType, E: Endianness> {
    pub digits: Vec<R::Base>,
    _radix: PhantomData<R>,
    _endian: PhantomData<E>,
}

impl<R: RadixType, E: Endianness> DigitVec<R, E> {
    /// Number of bigdigits in the vector
    pub fn len(&self) -> usize {
        self.digits.len()
    }

    /// Remove all bigdigits
    pub fn clear(&mut self) {
        self.digits.clear()
    }

    pub fn resize(&mut self, n: usize) {
        self.digits.resize(n, Zero::zero())
    }

    pub fn truncate(&mut self, n: usize) {
        self.digits.truncate(n);
    }

    fn as_digit_slice(&self) -> DigitSlice<'_, R, E> {
        DigitSlice {
            digits: self.digits.as_slice(),
            _radix: self._radix,
            _endian: self._endian,
        }
    }

    // construct from vector of digits
    fn from_vec(v: Vec<R::Base>) -> Self {
        debug_assert!(R::validate_digits(v.iter()));
        Self {
            digits: v,
            _radix: PhantomData {},
            _endian: PhantomData {},
        }
    }

    /// Convert to inner vector
    fn into_vec(self) -> Vec<R::Base> {
        self.digits
    }

    /// allocate with n bigdigits and fill with zeros
    pub fn from_zero_count(n: usize) -> Self {
        Self::from_vec(vec![Zero::zero(); n])
    }
}

impl<R: RadixType> DigitVec<R, LittleEndian> {
    /// allocate with n bigdigits and fill with zeros
    pub fn remove_significant_digits(&mut self) {
        if let Some(idx) = self.digits.iter().rposition(|d| !d.is_zero()) {
            self.digits.truncate(idx);
        }
    }
}


#[allow(dead_code)]
impl<R: RadixType> DigitVec<R, BigEndian> {
    pub fn remove_significant_digits(&mut self) {
        if let Some(idx) = self.digits.iter().position(|d| !d.is_zero()) {
            self.digits.copy_within(idx.., 0);
            self.digits.truncate(self.len() - idx);
        }
    }
}

impl DigitVec<RADIX_u64, LittleEndian> {
    pub fn from_biguint(n: &num_bigint::BigUint) -> Self {
        Self::from_vec(n.iter_u64_digits().collect())
    }

    // construct from trusted vector
    pub fn from_bigint(n: &num_bigint::BigInt) -> Self {
        Self::from_biguint(n.magnitude())
    }

}

/// Immutable slice of digits
///
/// Operations on the bigdigit values are defined by the
/// radix and endianness traits.
///
#[derive(Clone,Copy,Debug)]
pub(crate) struct DigitSlice<'a, R: RadixType, E: Endianness> {
    pub digits: &'a [R::Base],
    _radix: PhantomData<R>,
    _endian: PhantomData<E>,
}

impl<'a, R: RadixType, E: Endianness> DigitSlice<'a, R, E> {
    pub fn len(&self) -> usize {
        self.digits.len()
    }

    pub fn from_slice(d: &'a[R::Base]) -> Self {
        Self {
            digits: d,
            _radix: PhantomData {},
            _endian: PhantomData {},
        }
    }

    pub fn trim_from(&self, n: usize) -> Self {
        Self::from_slice(&self.digits[n..])
    }
}

impl<R: RadixType> DigitSlice<'_, R, LittleEndian> {
    pub fn find_least_significant_nonzero(&self) -> Option<usize> {
        self.digits.iter().position(|&d| !d.is_zero())
    }
}


/// Mutable slice of bigdigit values
#[derive(Debug)]
pub(crate) struct DigitSliceMut<'a, R: RadixType, E: Endianness> {
    pub digits: &'a mut [R::Base],
    _radix: PhantomData<R>,
    _endian: PhantomData<E>,
}

impl<'a, R: RadixType, E: Endianness> DigitSliceMut<'a, R, E> {
    fn from_slice(v: &'a mut [R::Base]) -> Self {
        Self {
            digits: v,
            _radix: PhantomData {},
            _endian: PhantomData {},
        }
    }

    pub fn from_vec_offset(v: &'a mut DigitVec<R, E>, offset: usize) -> Self {
        Self::from_slice(&mut v.digits[offset..])
    }
}
