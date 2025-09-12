//! Digit vectors (and slices) of arbitrary radix and endianness

use crate::*;

use stdlib::marker::PhantomData;

use super::radix::*;
use super::endian::*;


/// Vector of integers, interpreted as bigdigits in an integer
///
/// Value of the integer is defined by the radix and endianness
/// type parameters.
///
#[derive(Clone, Debug, Default)]
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
            self.push_significant_digit(overflow);
        }
    }

    /// Add bigdigit to the significant end of the vec
    pub fn push_significant_digit(&mut self, n: R::Base) {
        E::push_significant_digit(&mut self.digits, n);
    }

    /// remove significant zeros
    pub fn remove_leading_zeros(&mut self) {
        E::strip_significant_zeros(&mut self.digits)
    }

    #[cfg(rustc_1_75)]
    pub fn iter_le(&self) -> impl LeBigDigitIterator<'_, &R::Base> {
        E::iter_slice(&self.digits[..])
    }

    #[cfg(not(rustc_1_75))]
    pub fn iter_le(&self) -> LittleEndianBigDigitIter<'_, &R::Base> {
        E::iter_slice(&self.digits[..])
    }

    #[cfg(rustc_1_75)]
    pub fn iter_le_mut(&mut self) -> impl LeBigDigitIterator<'_, &mut R::Base> {
        E::iter_slice_mut(&mut self.digits[..])
    }

    #[cfg(not(rustc_1_75))]
    pub fn iter_le_mut(&mut self) -> LittleEndianBigDigitIter<'_, &mut R::Base> {
        E::iter_slice_mut(&mut self.digits[..])
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

impl DigitVec<RADIX_10p19_u64, LittleEndian> {
    pub(crate) fn from_biguint_using_tmp(
        n: &num_bigint::BigUint,
        tmp: &mut Vec<u64>,
    ) -> Self {
        tmp.clear();
        tmp.extend(n.iter_u64_digits());
        Self::from_2p64le_vec(tmp)
    }

    fn from_2p64le_vec(src: &mut Vec<u64>) -> Self {
        type R = RADIX_10p19_u64;

        let mut result: Vec<u64>;
        match src.split_last() {
            None => {
                return Self::default();
            }
            Some((&top_digit, &[])) => {
                let result = if top_digit < R::RADIX as u64 {
                    vec![top_digit]
                } else {
                    let (hi, lo) = top_digit.div_rem(&(R::RADIX as u64));
                    vec![lo, hi]
                };
                return Self::from_vec(result);
            }
            Some((&top_digit, digits)) => {
                let bit_count = (64 * digits.len()) + (64 - top_digit.leading_zeros() as usize);
                let base2p64_bigdigit_count = (bit_count as f64) / (LOG2_10 * R::DIGITS as f64);
                result = Vec::with_capacity(base2p64_bigdigit_count.ceil() as usize);
            }
        }
        while let Some(pos) = src.iter().rposition(|&d| d != 0) {
            src.truncate(pos + 1);
            let rem: u64 = src.iter_mut().rev().fold(0, |acc, d| {
                R::rotating_div_u64_radix(acc, d)
            });
            result.push(rem);
        }
        Self::from_vec(result)
    }

    pub fn into_bigint(self, sign: Sign) -> BigInt {
        let mut tmp = Vec::new();
        self.into_bigint_tmp(sign, &mut tmp)
    }

    pub fn into_bigint_tmp(self, sign: Sign, tmp: &mut Vec<u64>) -> BigInt {
        let uint = self.into_biguint_tmp(tmp);
        BigInt::from_biguint(sign, uint)
    }

    pub fn into_biguint_tmp(self, _tmp: &mut Vec<u64>) -> BigUint {
        use num_integer::div_rem;
        let radix = <RADIX_10p19_u64 as RadixType>::RADIX;

        let mut digits = self.digits.into_iter();
        let d0 = digits.next().unwrap_or(0);
        let mut result = BigUint::from(d0);

        let n = match digits.next() {
            None => {
                return result;
            }
            Some(n) => n,
        };

        let mut scale = BigUint::from(radix);
        result += n * &scale;

        for digit in digits {
            scale *= radix;
            match digit {
                0 => {},
                1 => {
                    result += &scale;
                }
                n => {
                    result += n * &scale;
                }
            }
        }
        return result;
    }
}

impl From<DigitVec<RADIX_u32, LittleEndian>> for num_bigint::BigUint {
    fn from(v: DigitVec<RADIX_u32, LittleEndian>) -> Self {
        Self::new(v.digits)
    }
}

impl From<DigitVec<RADIX_10p19_u64, LittleEndian>> for num_bigint::BigUint {
    fn from(v: DigitVec<RADIX_10p19_u64, LittleEndian>) -> Self {
        type R = RADIX_10p19_u64;
        let radix = R::RADIX as u64;
        match v.digits.as_slice() {
            &[] => {
                Self::zero()
            }
            &[d] => {
                Self::from(d)
            }
            &[d0, d1] => {
                let mut result = Self::from(d1);
                result *= radix;
                result += d0;
                return result;
            }
            _ => {
                let mut shifter = Self::one();
                let mut digits = v.digits.iter().rev();

                let mut result: Self = digits.next().unwrap().clone().into();

                for &d in digits {
                    shifter *= radix;
                    result *= &shifter;
                    result += d;
                }
                result
            }
        }
    }
}

impl From<DigitSlice<'_, RADIX_u64, LittleEndian>> for DigitVec<RADIX_10p19_u64, LittleEndian> {
    fn from(v: DigitSlice<'_, RADIX_u64, LittleEndian>) -> Self {
        let mut src = Vec::from(v.digits);
        Self::from_2p64le_vec(&mut src)
    }
}

impl From<DigitVec<RADIX_10p19_u64, LittleEndian>> for DigitVec<RADIX_u64, LittleEndian> {
    fn from(mut src: DigitVec<RADIX_10p19_u64, LittleEndian>) -> Self {
        type R2p64 = RADIX_u64;

        let radix = RADIX_10p19_u64::RADIX as u64;

        match src.digits.len() {
            0 | 1 => {
                Self::from_vec(src.digits)
            }
            2 => {
                let (hi, lo) = R2p64::expanding_mul(src.digits[1], radix);
                let (sum, overflow) = src.digits[0].overflowing_add(lo);
                src.digits[0] = sum;
                src.digits[1] = hi + u64::from(overflow);
                Self::from_vec(src.digits)
            }
            _ => {
                let mut result = vec![0; src.len()];
                result[0] = src.digits[0];

                let mut scaler = BigInt::from(radix);
                let mut base10_digits = src.digits.iter().skip(1);
                let mut base10_digit = base10_digits.next().copied().unwrap_or(0);
                loop {
                    for (i, base2_digit) in scaler.iter_u64_digits().enumerate() {
                        let (hi, lo) = R2p64::expanding_mul(base10_digit, base2_digit);
                        let (sum, overflow) = result[i].overflowing_add(lo);
                        result[i] = sum;
                        let mut j = i + 1;
                        let (sum, overflow) = result[j].overflowing_add(hi + u64::from(overflow));
                        result[j] = sum;
                        let mut carry = u64::from(overflow);
                        while carry != 0 {
                            j += 1;
                            let (sum, overflow) = result[j].overflowing_add(carry);
                            result[j] = sum;
                            carry = u64::from(overflow);
                        }
                    }

                    match base10_digits.next() {
                        None => break,
                        Some(&d) => { base10_digit = d }
                    }
                    scaler *= radix;
                }
                Self::from_vec(result)
            }
        }
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

    /// Return self, ignoring any significant zeros
    pub fn without_leading_zeros(&self) -> Self {
        let (digits, _) = E::split_significant_zeros(self.digits);
        Self::from_slice(digits)
    }

    #[cfg(rustc_1_75)]
    pub fn iter_le(&self) -> impl LeBigDigitIterator<'_, &R::Base> {
        E::iter_slice(self.digits)
    }

    #[cfg(not(rustc_1_75))]
    pub fn iter_le(&self) -> LittleEndianBigDigitIter<'_, &R::Base> {
        E::iter_slice(self.digits)
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

impl<'a, E: Endianness> From<&'a DigitVec<RADIX_u64, E>> for DigitSlice<'a, RADIX_u64, E> {
    fn from(v: &'a DigitVec<RADIX_u64, E>) -> Self {
        v.as_digit_slice()
    }
}

impl DigitSlice<'_, RADIX_10_u8, LittleEndian> {
    /// fill digitvec with value contained in this digit-slice
    pub fn fill_vec_u64(&self, dest: &mut DigitVec<RADIX_u64, LittleEndian>) {
        let n = num_bigint::BigUint::from_radix_le(self.digits, 10).unwrap();
        *dest = (&n).into();
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

    /// From digitvec, offset from the true index (independent of endianness)
    pub fn from_vec_offset(v: &'a mut DigitVec<R, E>, offset: usize) -> Self {
        Self::from_slice(&mut v.digits[offset..])
    }

    /// Cast to immutable slice
    pub fn as_digit_slice(&'a self) -> DigitSlice<'a, R, E> {
        DigitSlice::from_slice(self.digits)
    }

    /// Add bigdigit 'n' into this slice, returning overflow
    pub fn add_value_at(&mut self, idx: usize, mut n: R::Base) -> R::Base {
        if n.is_zero() {
            return n;
        }
        E::addassign_carry_into_slice_at::<R>(self.digits, &mut n, idx);
        n
    }

    /// Add bigdigit into vector, storing overflow back in c
    pub fn addassign_carry(&mut self, c: &mut R::Base) {
        E::addassign_carry_into_slice_at::<R>(self.digits, c, 0);
    }

    #[cfg(rustc_1_75)]
    pub fn iter_le(&self) -> impl LeBigDigitIterator<'_, &R::Base> {
        E::iter_slice(self.digits)
    }

    #[cfg(not(rustc_1_75))]
    pub fn iter_le(&self) -> LittleEndianBigDigitIter<'_, &R::Base> {
        E::iter_slice(self.digits)
    }

    #[cfg(rustc_1_75)]
    pub fn iter_le_mut(&mut self) -> impl LeBigDigitIterator<'_, &mut R::Base> {
        E::iter_slice_mut(self.digits)
    }

    #[cfg(not(rustc_1_75))]
    pub fn iter_le_mut(&mut self) -> LittleEndianBigDigitIter<'_, &mut R::Base> {
        E::iter_slice_mut(self.digits)
    }
}

impl<'a, R: RadixType, E: Endianness> From<&'a mut Vec<R::Base>> for DigitSliceMut<'a, R, E> {
    fn from(digits: &'a mut Vec<R::Base>) -> Self {
        Self::from_slice(&mut digits[..])
    }
}
