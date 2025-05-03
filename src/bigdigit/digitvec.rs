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
#[derive(Debug, Default)]
pub(crate) struct DigitVec<R: RadixType, E: Endianness> {
    pub digits: Vec<R::Base>,
    _radix: PhantomData<R>,
    _endian: PhantomData<E>,
}

impl<R: RadixType, E: Endianness> DigitVec<R, E> {
    /// Create new vector
    pub fn new() -> Self {
        Self::from_vec(Vec::new())
    }

    /// Create new vector with capacity
    pub fn with_capacity(n: usize) -> Self {
        Self::from_vec(Vec::with_capacity(n))
    }

    /// construct from vector of digits
    pub fn from_vec(v: Vec<R::Base>) -> Self {
        debug_assert!(R::validate_digits(v.iter()));
        Self {
            digits: v,
            _radix: PhantomData {},
            _endian: PhantomData {},
        }
    }

    /// allocate with n bigdigits and fill with zeros
    pub fn from_zero_count(n: usize) -> Self {
        Self::from_vec(vec![Zero::zero(); n])
    }

    /// Number of bigdigits in the vector
    pub fn len(&self) -> usize {
        self.digits.len()
    }

    /// Remove all bigdigits
    pub fn clear(&mut self) {
        self.digits.clear()
    }

    /// Resize inner vector, filling new values with zero
    pub fn resize(&mut self, n: usize) {
        self.digits.resize(n, Zero::zero())
    }

    /// Shrink inner vectory to new size
    pub fn truncate(&mut self, n: usize) {
        self.digits.truncate(n);
    }

    /// Borrow inner vectory as immutable digit-slice
    pub fn as_digit_slice(&self) -> DigitSlice<'_, R, E> {
        DigitSlice {
            digits: self.digits.as_slice(),
            _radix: self._radix,
            _endian: self._endian,
        }
    }

    /// Borrow inner vectory as mutable digit-slice
    pub fn as_digit_slice_mut(&mut self) -> DigitSliceMut<'_, R, E> {
        DigitSliceMut {
            digits: &mut self.digits,
            _radix: self._radix,
            _endian: self._endian,
        }
    }

    /// Convert to inner vector
    pub fn into_vec(self) -> Vec<R::Base> {
        self.digits
    }

    /// Add bigdigit into this vector, starting from index of least significance
    ///
    /// Any "overflow" is pushed to most significant end of the vector
    ///
    pub fn add_value(&mut self, n: R::Base) {
        self.add_value_at(0, n);
    }

    /// Add bigdigit into this vector (idexing from least-significant digit)
    ///
    /// TODO: Should vector resize if index is larger than size of vector?
    ///
    pub fn add_value_at(&mut self, idx: usize, n: R::Base) {
        debug_assert!(idx <= self.digits.len());

        if n.is_zero() {
            return;
        }

        let overflow = self.as_digit_slice_mut().add_value_at(0, n);
        if !overflow.is_zero() {
            E::push_significant_digit(&mut self.digits, overflow);
        }
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

impl From<&num_bigint::BigUint> for DigitVec<RADIX_u64, LittleEndian> {
    fn from(n: &num_bigint::BigUint) -> Self {
        Self::from_vec(n.iter_u64_digits().collect())
    }
}

impl From<DigitVec<RADIX_u64, LittleEndian>> for num_bigint::BigUint {
    fn from(v: DigitVec<RADIX_u64, LittleEndian>) -> Self {
        // TODO: Can we do this conversion in place?
        let mut digits = Vec::with_capacity(v.len() * 2);
        for d in v.digits.into_iter() {
            digits.push(d as u32);
            digits.push((d >> 32) as u32);
        }
        Self::new(digits)
    }
}

impl From<&DigitVec<RADIX_u64, LittleEndian>> for num_bigint::BigUint {
    fn from(v: &DigitVec<RADIX_u64, LittleEndian>) -> Self {
        let mut digits = Vec::with_capacity(v.len() * 2);
        for &d in v.digits.iter() {
            digits.push(d as u32);
            digits.push((d >> 32) as u32);
        }
        Self::new(digits)
    }
}


/// Immutable slice of digits
///
/// Operations on the bigdigit values are defined by the
/// radix and endianness traits.
///
#[derive(Clone, Copy, Debug)]
pub(crate) struct DigitSlice<'a, R: RadixType, E: Endianness> {
    pub digits: &'a [R::Base],
    _radix: PhantomData<R>,
    _endian: PhantomData<E>,
}

impl<'a, R: RadixType, E: Endianness> DigitSlice<'a, R, E> {
    /// Wrap slice of numbers as a slice of big-digits with given radix
    /// and endianness
    ///
    /// This does no validation, so the digits may be outside the bounds
    /// of the radix and may have leading significant zeros.
    ///
    pub fn from_slice(d: &'a [R::Base]) -> Self {
        Self {
            digits: d,
            _radix: PhantomData {},
            _endian: PhantomData {},
        }
    }

    /// Wrap slice of numbers, ignoring significant zeros
    pub fn from_sig_slice(d: &'a [R::Base]) -> Self {
        let (nonzero, _) = E::split_significant_zeros(d);
        Self::from_slice(nonzero)
    }

    /// Number of bigdigits in slice
    pub fn len(&self) -> usize {
        self.digits.len()
    }
}

impl<R: RadixType> DigitSlice<'_, R, LittleEndian> {
    /// Return subslice of digits with the 'n' least significant bigdigits removed
    pub fn trim_insignificant(&self, n: usize) -> Self {
        Self::from_slice(&self.digits[n..])
    }

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
    /// Construct from mutable slice of numbers
    pub fn from_slice(v: &'a mut [R::Base]) -> Self {
        Self {
            digits: v,
            _radix: PhantomData {},
            _endian: PhantomData {},
        }
    }

    /// Number of bigdigits in slice
    pub fn len(&self) -> usize {
        self.digits.len()
    }

    pub fn from_vec_offset(v: &'a mut DigitVec<R, E>, offset: usize) -> Self {
        Self::from_slice(&mut v.digits[offset..])
    }

    /// Add bigdigit 'n' into this slice, if the
    pub fn add_value_at(&mut self, idx: usize, mut n: R::Base) -> R::Base {
        if n.is_zero() {
            return n;
        }
        for dest in E::iter_slice_mut(self.digits).skip(idx) {
            R::addassign_carry(dest, &mut n);
            if n.is_zero() {
                return n;
            }
        }
        n
    }
}
