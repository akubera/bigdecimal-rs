//! Digit vectors (and slices) of arbitrary radix and endianness

use crate::*;

use stdlib::marker::PhantomData;
use stdlib::num::NonZeroU64;

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

    /// Create digit vector with capacity
    #[allow(dead_code)]
    pub fn with_capacity(n: usize) -> Self {
        Self::from_vec(Vec::with_capacity(n))
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

    #[allow(dead_code)]
    pub fn as_digit_slice_mut(&mut self) -> DigitSliceMut<'_, R, E> {
        DigitSliceMut {
            digits: &mut self.digits[..],
            _radix: self._radix,
            _endian: self._endian,
        }
    }

    // construct from vector of digits
    pub(crate) fn from_vec(v: Vec<R::Base>) -> Self {
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

        E::addassign_carry_into_slice_at::<R>(&mut self.digits, &mut n, idx);
        self.push_significant_digit(n);
    }

    /// Add bigdigit to the significant end of the vec
    pub fn push_significant_digit(&mut self, n: R::Base) {
        E::push_significant_digit(&mut self.digits, n);
    }
}

impl<'a, R: RadixPowerOfTen, E: Endianness> DigitVec<R, E> {
    pub fn count_decimal_digits(&self) -> usize {
        self.as_digit_slice().count_decimal_digits()
    }

    /// remove significant zeros
    pub fn remove_leading_zeros(&mut self) {
        E::strip_significant_zeros(&mut self.digits)
    }
}


impl DigitVec<RADIX_u64, LittleEndian> {
    /// Convert to signed big integer
    pub fn into_bigint(self, sign: Sign) -> BigInt {
        BigInt::from_biguint(sign, self.into())
    }

    /// Construct vector from iterator of base-10^{19} bigdigits
    #[allow(dead_code)]
    pub fn from_10p19_digits<I: Iterator<Item=u64>>(mut digits: I) -> Self {
        type R2p64 = RADIX_u64;
        type R10p19 = RADIX_10p19_u64;

        let mut v = vec![digits.next().unwrap_or(0)];

        if let Some(d) = digits.next() {
            let mut carry = 0;
            R2p64::carrying_mul_add_inplace(
                d, R10p19::RADIX as u64, &mut v[0], &mut carry
            );
            if carry != 0 {
                v.push(carry);
            }
        }

        let mut d = match digits.next() {
            Some(d) => d,
            None => {
                return Self::from_vec(v);
            }
        };

        let mut shifter = BigUint::from(R10p19::RADIX * R10p19::RADIX);

        loop {
            v.push(0);

            if d != 0 {
                let mut carry = 0;
                let mut dest_digits = v.iter_mut();
                let mut shifter_digits = shifter.iter_u64_digits();

                loop {
                    match (dest_digits.next(), shifter_digits.next()) {
                        (Some(p), Some(s)) => {
                            R2p64::carrying_mul_add_inplace(d, s, p, &mut carry);
                        }
                        (None, Some(mut s)) => {
                            loop {
                                let (hi, lo) = R2p64::fused_mul_add(s, d, carry);
                                v.push(lo);
                                carry = hi;
                                s = match shifter_digits.next() {
                                    None => break,
                                    Some(x) => x,
                                };
                            }
                            break;
                        }
                        (Some(p), None) if carry != 0 => {
                            R2p64::addassign_carry(p, &mut carry);
                        }
                        _ => {
                            break;
                        }
                    }
                }
                if !carry.is_zero() {
                    v.push(carry);
                }
            }

            d = match digits.next() {
                Some(d) => d,
                None => {
                    let zero_idx = v.iter().rposition(|&d| d != 0).unwrap_or(0);
                    v.truncate(zero_idx + 1);
                    return Self::from_vec(v);
                }
            };

            shifter *= R10p19::RADIX as u64;
        }
    }
}

impl From<&num_bigint::BigUint> for DigitVec<RADIX_u64, LittleEndian> {
    fn from(n: &num_bigint::BigUint) -> Self {
        Self::from_vec(n.iter_u64_digits().collect())
    }
}

impl From<DigitVec<RADIX_u64, LittleEndian>> for num_bigint::BigUint {
    #[cfg(rustc_1_53)]
    fn from(v: &DigitVec<RADIX_u64, LittleEndian>) -> Self {
        let digits = v.digits
                        .iter()
                        .flat_map(|&d| [d as u32, (d >> 32) as u32])
                        .collect();
        Self::new(digits)
    }

    #[cfg(not(rustc_1_53))]
    fn from(v: DigitVec<RADIX_u64, LittleEndian>) -> Self {
        let mut digits = Vec::with_capacity(v.len() * 2);
        for d in v.digits.into_iter() {
            digits.push(d as u32);
            digits.push((d >> 32) as u32);
        }
        Self::new(digits)
    }
}

impl From<&DigitVec<RADIX_u64, LittleEndian>> for num_bigint::BigUint {
    #[cfg(rustc_1_53)]
    fn from(v: &DigitVec<RADIX_u64, LittleEndian>) -> Self {
        let digits = v.digits
                        .iter()
                        .flat_map(|&d| [d as u32, (d >> 32) as u32])
                        .collect();
        Self::new(digits)
    }

    #[cfg(not(rustc_1_53))]
    fn from(v: &DigitVec<RADIX_u64, LittleEndian>) -> Self {
        let mut digits = Vec::with_capacity(v.len() * 2);
        for d in v.digits.into_iter() {
            digits.push(d as u32);
            digits.push((d >> 32) as u32);
        }
        Self::new(digits)
    }
}

impl DigitVec<RADIX_10p19_u64, LittleEndian> {
    /// Convert a num biguint into DigitVec, using tmp as scratchpad
    pub(crate) fn from_biguint_using_tmp(
        n: &num_bigint::BigUint,
        tmp: &mut Vec<u64>,
    ) -> Self {
        tmp.clear();
        tmp.extend(n.iter_u64_digits());
        Self::from_2p64le_vec(tmp)
    }

    /// remove the bottom 'n' digits in the vector, returning the highest
    pub fn shift_n_digits_returning_high(&mut self, n: usize) -> u8 {
        use bigdigit::alignment::BigDigitSplitter;
        type Splitter = BigDigitSplitter::<RADIX_10p19_u64>;

        if n == 0 {
            return 0;
        }

        let (bd_count, d_count) = n.div_rem(&19);

        if d_count == 0 {
            // insig is top digit on previous bigdigit
            let ret = self.digits[bd_count - 1] / (RADIX_10p19_u64::RADIX as u64 / 10);
            self.digits.copy_within(bd_count.., 0);
            self.digits.truncate(self.len() - bd_count);
            return ret as u8;
        }

        let mask = Splitter::mask_low(d_count as u8);
        let (d0, insig) = mask.div_rem(self.digits[bd_count]);
        let ret = mask.div(insig * 10) as u8;

        let mut prev = d0;

        let mut j = 0;

        loop {
            if let Some(&d) = self.digits.get(bd_count + 1 + j) {
                let (hi, lo) = mask.split_and_shift(d);
                self.digits[j] = lo + prev;
                prev = hi;

                j += 1;
            } else {
                if prev != 0 {
                    self.digits[j] = prev;
                    j += 1;
                }
                self.digits.truncate(j);
                return ret;
            }
        }
    }

    /// Convert a base-2^64 DigitVec to 10^19 DigitVec
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

    /// Convert to a num BigInt with given sign
    pub fn into_bigint(self, sign: Sign) -> BigInt {
        let uint = self.into_biguint();
        BigInt::from_biguint(sign, uint)
    }

    /// Convert to BigUint
    pub fn into_biguint(self) -> BigUint {
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

impl From<DigitVec<RADIX_10p19_u64, LittleEndian>> for num_bigint::BigUint {
    fn from(v: DigitVec<RADIX_10p19_u64, LittleEndian>) -> Self {
        v.into_biguint()
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
        type R10p19 = RADIX_10p19_u64;

        match src.digits.len() {
            0 | 1 => {
                Self::from_vec(src.digits)
            }
            2 => {
                let (hi, lo) = R2p64::expanding_mul(src.digits[1], R10p19::RADIX as u64);
                let (sum, overflow) = src.digits[0].overflowing_add(lo);
                src.digits[0] = sum;
                src.digits[1] = hi + u64::from(overflow);
                Self::from_vec(src.digits)
            }
            _ => {
                let mut result = vec![0; src.len()];
                result[0] = src.digits[0];

                let mut scaler = BigInt::from(R10p19::RADIX as u64);
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
                    scaler *= R10p19::RADIX as u64;
                }
                Self::from_vec(result)
            }
        }
    }
}

#[cfg(test)]
mod test_from_biguint_using_tmp {
    use super::*;
    use crate::bigdigit::radix::RADIX_10p19_u64;

    macro_rules! impl_case {
        ($name:ident: $input:literal => $result:expr) => {
            #[test]
            fn $name() {
                let n: BigUint = $input.parse().unwrap();

                let mut tmp = Vec::new();
                let vec = DigitVec::from_biguint_using_tmp(&n, &mut tmp);
                let expected = &$result;
                assert_eq!(vec.digits.as_slice(), expected);
            }
        }
    }

    impl_case!(test_zero: "0" => []);
    impl_case!(test_3888089293362626678: "3888089293362626678" => [3888089293362626678]);
    impl_case!(test_10000000000000000000: "10000000000000000000" => [0, 1]);
    impl_case!(test_141905914:
        "1419059141115374799211309048234647259918822773497033524702964376392264024748829821875106774"
        => [
            4748829821875106774,
            2470296437639226402,
            2599188227734970335,
            4799211309048234647,
                141905914111537,
        ]);
}

/// Vector of base-10 digits
impl DigitVec<RADIX_10_u8, LittleEndian> {
    /// splits digits into `prec` significant digits, returning the lowest significant digit,
    /// highest insignificant digit, and the remaining insignificant digits in little endian order
    ///
    pub fn get_rounding_digits_at_prec(
        &self,
        prec: stdlib::num::NonZeroU64,
    ) -> (u8, u8, DigitSlice<'_, RADIX_10_u8, LittleEndian>) {
        let trimmed = self.digits.len().saturating_sub(prec.get() as usize);
        if trimmed == 0 {
            return (0, 0, DigitSlice::from_slice(&[]));
        }

        let (insig_digits, sig_digits) = self.digits.split_at(trimmed);
        debug_assert_eq!(trimmed, insig_digits.len());
        let (insig_digit, trailing_digits) = insig_digits.split_last().unwrap_or((&0, &[]));
        (sig_digits[0], *insig_digit, DigitSlice::from_slice(trailing_digits))
    }

    /// Round the digits in this vec, returning slice of the digits
    ///
    /// Note: this changes the value of 'self', and should be considered as
    /// just a buffer of bytes after rounding in place.
    ///
    pub fn round_at_prec_inplace(
        &mut self,
        prec: NonZeroU64,
        rounding: NonDigitRoundingData,
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
                    fill_slice_with_zero(&mut sig_digits[..idx]);
                }
                None => {
                    fill_slice_with_zero(sig_digits);
                    *sig_digits.last_mut().unwrap() = 1;
                    trimmed += 1;
                }
            }
        }

        debug_assert_eq!(prec.get() as usize, sig_digits.len());
        return (DigitSlice::from_slice(sig_digits), trimmed);
    }
}

#[cfg(rustc_1_50)]
fn fill_slice_with_zero<D: Zero + Clone>(s: &mut [D]) {
    s.fill(Zero::zero());
}

#[cfg(not(rustc_1_50))]
fn fill_slice_with_zero<D: Zero + Clone>(s: &mut [D]) {
    for r in s.iter_mut() {
        *r = Zero::zero();
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

    pub fn addassign_carry(&mut self, c: &mut R::Base) {
        E::addassign_carry_into_slice_at::<R>(self.digits, c, 0);
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
