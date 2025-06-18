//! Digit vectors (and slices) of arbitrary radix and endianness

use crate::*;

use stdlib::marker::PhantomData;

use super::radix::*;
use super::endian::*;

use crate::rounding::NonDigitRoundingData;


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

    pub fn as_digit_slice(&self) -> DigitSlice<'_, R, E> {
        DigitSlice {
            digits: self.digits.as_slice(),
            _radix: self._radix,
            _endian: self._endian,
        }
    }

    pub fn as_digit_slice_at(&self, n: usize) -> DigitSlice<'_, R, E> {
        DigitSlice {
            digits: &self.digits[n..],
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

    /// add value into this vector, overflowing into
    pub fn add_value(&mut self, n: R::Base) {
        self.add_value_at(0, n);
    }

    /// add value into this vector, starting at given index
    pub fn add_value_at(&mut self, idx: usize, mut n: R::Base) {
        debug_assert!(idx <= self.digits.len());
        if n.is_zero() {
            return;
        }

        for dest in E::iter_slice_mut(&mut self.digits).skip(idx) {
            R::addassign_carry(dest, &mut n);
            if n.is_zero() {
                return;
            }
        }

        E::push_significant_digit(&mut self.digits, n);
    }
}

impl<'a, R: RadixPowerOfTen, E: Endianness> DigitVec<R, E> {
    pub fn count_decimal_digits(&self) -> usize {
        self.as_digit_slice().count_decimal_digits()
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
    /// Convert to signed big integer
    pub fn into_bigint(self, sign: Sign) -> BigInt {
        BigInt::from_biguint(sign, self.into())
    }
}

impl From<&num_bigint::BigUint> for DigitVec<RADIX_u64, LittleEndian> {
    fn from(n: &num_bigint::BigUint) -> Self {
        Self::from_vec(n.iter_u64_digits().collect())
    }
}

impl From<DigitVec<RADIX_u64, LittleEndian>> for num_bigint::BigUint {
    fn from(v: DigitVec<RADIX_u64, LittleEndian>) -> Self {
        let digits = v.digits
                        .into_iter()
                        .map(|d| [d as u32, (d >> 32) as u32])
                        .flatten()
                        .collect();
        Self::new(digits)
    }
}

impl From<&DigitVec<RADIX_u64, LittleEndian>> for num_bigint::BigUint {
    fn from(v: &DigitVec<RADIX_u64, LittleEndian>) -> Self {
        let digits = v.digits
                        .iter()
                        .map(|&d| [d as u32, (d >> 32) as u32])
                        .flatten().collect();
        Self::new(digits)
    }
}


/// Vector of base-10 digits
impl DigitVec<RADIX_10_u8, LittleEndian> {

    /// Round the digits in this vec, returning slice of the digits
    ///
    /// Note: this changes the value of 'self', and should be considered as
    /// just a buffer of bytes after rounding in place.
    ///
    pub fn round_at_prec_inplace(
        &mut self, prec: stdlib::num::NonZeroU64, rounding: NonDigitRoundingData
    ) -> (DigitSlice<RADIX_10_u8, LittleEndian>, usize) {
        // count number of insignificant digits to remove
        let mut trimmed = self.digits.len().saturating_sub(prec.get() as usize);
        if trimmed == 0 {
            return (DigitSlice::from_slice(&self.digits), 0);
        }

        let (insig_digits, sig_digits) = self.digits.split_at_mut(trimmed);
        debug_assert_eq!(trimmed, insig_digits.len());

        let (&insig_digit, insig_digits) = insig_digits.split_last().unwrap_or((&0, &[]));
        let trailing_zeros = insig_digits.iter().all(|&d| d == 0);
        let round = rounding.round_pair((sig_digits[0], insig_digit), trailing_zeros);

        if round != 10 {
            sig_digits[0] = round;
        } else {
            match sig_digits.iter().position(|&d| d != 9) {
                Some(idx) => {
                    sig_digits[idx] += 1;
                    sig_digits[..idx].fill(0);
                }
                None => {
                    sig_digits.fill(0);
                    *sig_digits.last_mut().unwrap() = 1;
                    trimmed += 1;
                }
            }
        }

        debug_assert_eq!(prec.get() as usize, sig_digits.len());
        return (DigitSlice::from_slice(sig_digits), trimmed);
    }
}

/// Convert BigUint to base-10 digits
impl From<&num_bigint::BigUint> for DigitVec<RADIX_10_u8, LittleEndian> {
    fn from(n: &num_bigint::BigUint) -> Self {
        Self::from_vec(n.to_radix_le(10))
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
    pub fn len(&self) -> usize {
        self.digits.len()
    }

    pub fn from_slice(d: &'a [R::Base]) -> Self {
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

    /// Cast to immutable slice
    fn as_digit_slice(&'a self) -> DigitSlice<'a, R, E> {
        DigitSlice::from_slice(self.digits)
    }
}

impl<'a, R: RadixPowerOfTen, E: Endianness> DigitSliceMut<'a, R, E> {
    pub fn count_decimal_digits(&self) -> usize {
        self.as_digit_slice().count_decimal_digits()
    }
}

impl<'a, R: RadixType, E: Endianness> From<&'a mut Vec<R::Base>> for DigitSliceMut<'a, R, E> {
    fn from(digits: &'a mut Vec<R::Base>) -> Self {
        Self::from_slice(&mut digits[..])
    }
}


impl<'a, R: RadixPowerOfTen, E: Endianness> DigitSlice<'a, R, E> {
    pub fn count_decimal_digits(&self) -> usize {
        use crate::arithmetic::decimal::count_digits_u64;

        let (top_digit, trailing) = E::split_most_significant_digit(self.digits);
        R::DIGITS * trailing.len()
            + count_digits_u64(top_digit.to_u64().unwrap())
    }
}

impl<'a> DigitSlice<'a, RADIX_10_u8, LittleEndian> {
    pub fn fill_vec_u64(&self, dest: &mut DigitVec<RADIX_u64, LittleEndian>) {
        let n = BigUint::from_radix_le(self.digits, 10).unwrap();
        *dest = (&n).into();
    }
}

impl<'a, E: Endianness> From<&'a DigitVec<RADIX_u64, E>> for DigitSlice<'a, RADIX_u64, E> {
    fn from(v: &'a DigitVec<RADIX_u64, E>) -> Self {
        v.as_digit_slice()
    }
}
