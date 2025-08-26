//! Structs and traits for generic operations on big or little endian ints

use crate::stdlib;
use crate::stdlib::fmt;
use crate::stdlib::Vec;

#[cfg(not(rustc_1_75))]
use stdlib::Box;

use num_traits::{Zero, PrimInt};

use super::radix::RadixType;

/// Trait to allow generic parameterization of significant digit ordering
pub(crate) trait Endianness: Copy + Clone + Default + fmt::Debug {
    /// Name to use for debugging
    const NAME: &'static str;

    /// Iterate over digits in vec from least to most significance
    #[cfg(rustc_1_75)]
    fn into_iter<'a, D: 'a>(digits: Vec<D>) -> impl LeBigDigitIterator<'a, D>;

    /// Iterate in slice from least to most significance
    #[cfg(rustc_1_75)]
    fn iter_slice<D>(digits: &[D]) -> impl LeBigDigitIterator<'_, &D>;

    /// Iterate over mut digits in slice from least to most significance
    #[cfg(rustc_1_75)]
    fn iter_slice_mut<D>(digits: &mut [D]) -> impl LeBigDigitIterator<'_, &mut D>;

    #[cfg(not(rustc_1_75))]
    fn into_iter<'a, D: 'a>(digits: Vec<D>) -> LittleEndianBigDigitIter<'a, D>;

    #[cfg(not(rustc_1_75))]
    fn iter_slice<D>(digits: &[D]) -> LittleEndianBigDigitIter<'_, &D>;

    #[cfg(not(rustc_1_75))]
    fn iter_slice_mut<D>(digits: &mut [D]) -> LittleEndianBigDigitIter<'_, &mut D>;

    #[cfg(rustc_1_75)]
    fn addassign_carry_into_slice_at<R: RadixType>(
        digits: &mut [R::Base],
        carry: &mut R::Base,
        idx: usize,
    ) {
        for dest in Self::iter_slice_mut(digits).skip(idx) {
            R::addassign_carry(dest, carry);
            if carry.is_zero() {
                return;
            }
        }
    }

    #[cfg(not(rustc_1_75))]
    fn addassign_carry_into_slice_at<R: RadixType>(
        digits: &mut [R::Base],
        carry: &mut R::Base,
        idx: usize,
    );

    /// Place given digit at the most-significant end of the vecor
    fn push_significant_digit<D>(digits: &mut Vec<D>, d: D);

    /// Split slice into most-significant digit and 'the rest'
    ///
    /// If slice is empty zero and empty-slice is returned
    fn split_most_significant_digit<D: Zero + PrimInt>(digits: &[D]) -> (D, &[D]);

    /// Split significant zeros from digits returning pair (digits, zeros)
    fn split_significant_zeros<D: Zero>(digits: &[D]) -> (&[D], &[D]);

    /// Split slice into 'count' low-significant digits, and remaining
    /// significant digits
    fn split_least_significant<D>(digits: &[D], count: usize) -> (&[D], &[D]);

    /// Split mutable slice into 'count' low-significant digits, and
    /// remaining significant digits
    fn split_least_significant_mut<D>(digits: &mut [D], count: usize) -> (&mut [D], &mut [D]);

    /// Remove any zeros at the location of highest significance, if all zeros
    /// the vector will be cleared
    fn strip_significant_zeros<D: Copy + Zero>(digits: &mut Vec<D>);

    /// return number of consecutive zeros starting at significant
    fn count_significant_zeros<D: Zero>(digits: &[D]) -> usize {
        Self::iter_slice(digits).rev().position(|d| !d.is_zero()).unwrap_or(digits.len())
    }

    /// Correctly order a slice of little endian digits
    ///
    /// Reverses for BigEndian, no-op for LittleEndian
    fn reorder_le_digits<D: Copy>(digits: &mut [D]);

    /// Consider digits in slice past 'idx' to be little-endian digits
    /// of higher significance than those below; move them to correct
    /// position in the slice
    ///
    /// This will be a no-op for LittleEndian, and a rotate and reverse for BigEndian
    ///
    fn rotate_trailing_le_digits_at<D: Copy>(digits: &mut [D], idx: usize);
}


/// Empty struct indicating most-significant bigdigit first
#[derive(Copy, Clone, Debug, Default)]
pub(crate) struct BigEndian {}

/// Empty struct indicating least-significant bigdigit first
#[derive(Copy, Clone, Debug, Default)]
pub(crate) struct LittleEndian {}

impl Endianness for BigEndian {
    const NAME: &'static str = "BE";

    #[cfg(rustc_1_75)]
    fn into_iter<'a, D: 'a>(digits: Vec<D>) -> impl LeBigDigitIterator<'a, D> {
        digits.into_iter().rev()
    }

    #[cfg(rustc_1_75)]
    fn iter_slice<D>(digits: &[D]) -> impl LeBigDigitIterator<'_, &D> {
        digits.iter().rev()
    }

    #[cfg(rustc_1_75)]
    fn iter_slice_mut<D>(digits: &mut [D]) -> impl LeBigDigitIterator<'_, &mut D> {
        digits.iter_mut().rev()
    }

    #[cfg(not(rustc_1_75))]
    fn into_iter<'a, D: 'a>(digits: Vec<D>) -> LittleEndianBigDigitIter<'a, D> {
        LittleEndianBigDigitIter {
            digits: Box::new(digits.into_iter().rev()),
        }
    }

    #[cfg(not(rustc_1_75))]
    fn iter_slice<D>(digits: &[D]) -> LittleEndianBigDigitIter<'_, &D> {
        LittleEndianBigDigitIter {
            digits: Box::new(digits.iter().rev()),
        }
    }

    #[cfg(not(rustc_1_75))]
    fn iter_slice_mut<D>(digits: &mut [D]) -> LittleEndianBigDigitIter<'_, &mut D> {
        LittleEndianBigDigitIter {
            digits: Box::new(digits.iter_mut().rev()),
        }
    }

    #[cfg(not(rustc_1_75))]
    fn addassign_carry_into_slice_at<R: RadixType>(
        digits: &mut [R::Base],
        carry: &mut R::Base,
        idx: usize,
    ) {
        for dest in digits.iter_mut().rev().skip(idx) {
            R::addassign_carry(dest, carry);
            if carry.is_zero() {
                return;
            }
        }
    }

    fn push_significant_digit<D>(digits: &mut Vec<D>, d: D) {
        digits.insert(0, d);
    }

    fn split_least_significant<D>(digits: &[D], count: usize) -> (&[D], &[D]) {
        let (hi, lo) = digits.split_at(digits.len() - count);
        (lo, hi)
    }

    fn split_least_significant_mut<D>(digits: &mut [D], count: usize) -> (&mut [D], &mut [D]) {
        let (hi, lo) = digits.split_at_mut(digits.len() - count);
        (lo, hi)
    }

    fn split_most_significant_digit<D: Copy + Zero>(digits: &[D]) -> (D, &[D]) {
        digits.split_first().map(|(&d, r)| (d, r)).unwrap_or((Zero::zero(), &[]))
    }

    fn strip_significant_zeros<D: Copy + Zero>(digits: &mut Vec<D>) {
        if let Some(idx) = digits.iter().position(|d| !d.is_zero()) {
            digits.copy_within(idx.., 0);
            digits.truncate(digits.len() - idx);
        } else {
            digits.clear();
        }
    }

    fn split_significant_zeros<D: Zero>(digits: &[D]) -> (&[D], &[D]) {
        if let Some(idx) = digits.iter().position(|d| !d.is_zero()) {
            let (sig_zeros, digits) = digits.split_at(idx);
            (digits, sig_zeros)
        } else {
            (&[], digits)
        }
    }

    fn reorder_le_digits<D: Copy>(digits: &mut [D]) {
        digits.reverse()
    }

    fn rotate_trailing_le_digits_at<D: Copy>(digits: &mut [D], idx: usize) {
        Self::reorder_le_digits(&mut digits[idx..]);
        digits.rotate_left(idx);
    }
}


impl Endianness for LittleEndian {
    const NAME: &'static str = "LE";

    #[cfg(rustc_1_75)]
    fn into_iter<'a, D: 'a>(digits: Vec<D>) -> impl LeBigDigitIterator<'a, D> {
        digits.into_iter()
    }

    #[cfg(rustc_1_75)]
    fn iter_slice<D>(digits: &[D]) -> impl LeBigDigitIterator<'_, &D> {
        digits.iter()
    }

    #[cfg(rustc_1_75)]
    fn iter_slice_mut<D>(digits: &mut [D]) -> impl LeBigDigitIterator<'_, &mut D> {
        digits.iter_mut()
    }

    #[cfg(not(rustc_1_75))]
    fn into_iter<'a, D: 'a>(digits: Vec<D>) -> LittleEndianBigDigitIter<'a, D> {
        LittleEndianBigDigitIter {
            digits: Box::new(digits.into_iter()),
        }
    }

    #[cfg(not(rustc_1_75))]
    fn iter_slice<D>(digits: &[D]) -> LittleEndianBigDigitIter<'_, &D> {
        LittleEndianBigDigitIter {
            digits: Box::new(digits.iter()),
        }
    }

    #[cfg(not(rustc_1_75))]
    fn iter_slice_mut<D>(digits: &mut [D]) -> LittleEndianBigDigitIter<'_, &mut D> {
        LittleEndianBigDigitIter {
            digits: Box::new(digits.into_iter()),
        }
    }

    #[cfg(not(rustc_1_75))]
    fn addassign_carry_into_slice_at<R: RadixType>(
        digits: &mut [R::Base],
        carry: &mut R::Base,
        idx: usize,
    ) {
        for dest in digits.iter_mut().skip(idx) {
            R::addassign_carry(dest, carry);
            if carry.is_zero() {
                return;
            }
        }
    }

    fn push_significant_digit<D>(digits: &mut Vec<D>, d: D) {
        digits.push(d);
    }

    fn split_least_significant<D>(digits: &[D], count: usize) -> (&[D], &[D]) {
        digits.split_at(count)
    }

    fn split_least_significant_mut<D>(digits: &mut [D], count: usize) -> (&mut [D], &mut [D]) {
        digits.split_at_mut(count)
    }

    fn split_most_significant_digit<D: Copy + Zero>(digits: &[D]) -> (D, &[D]) {
        digits.split_last().map(|(&d, r)| (d, r)).unwrap_or((Zero::zero(), &[]))
    }

    fn strip_significant_zeros<D: Zero>(digits: &mut Vec<D>) {
        if let Some(idx) = digits.iter().rposition(|d| !d.is_zero()) {
            digits.truncate(idx + 1);
        } else {
            digits.clear();
        }
    }

    fn split_significant_zeros<D: Zero>(digits: &[D]) -> (&[D], &[D]) {
        if let Some(idx) = digits.iter().rposition(|d| !d.is_zero()) {
            let (digits, sig_zeros) = digits.split_at(idx);
            (digits, sig_zeros)
        } else {
            (&[], digits)
        }
    }

    #[allow(unused_variables)]
    fn reorder_le_digits<D: Copy>(digits: &mut [D]) {
        //no-op
    }

    #[allow(unused_variables)]
    fn rotate_trailing_le_digits_at<D: Copy>(digits: &mut [D], idx: usize) {
        //no-op
    }
}

/// Abstraction over fixed-size little-endian bigdigit iterators
///
/// Can be applied to slice, vecs, and num_bigint::{U32Digits, U64Digits}
/// allowing "easy" access to the digits.
pub(crate) trait LeBigDigitIterator<'a, D>
                    : Iterator<Item=D>
                    + ExactSizeIterator
                    + DoubleEndedIterator
{
}

/// Thin wrapper around boxed big-digit-iterator trait object
///
/// Used to implement generic endian iterators for versions of Rust before
/// Return Position Impl Trait In Trait (RPITIT) were implemented.
///
#[cfg(not(rustc_1_75))]
pub(crate) struct LittleEndianBigDigitIter<'a, D> {
    digits: Box<dyn LeBigDigitIterator<'a, D> + 'a>,
}

#[cfg(not(rustc_1_75))]
impl<D> Iterator for LittleEndianBigDigitIter<'_, D> {
    type Item = D;

    fn next(&mut self) -> Option<Self::Item> {
        self.digits.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.digits.size_hint()
    }
}

#[cfg(not(rustc_1_75))]
impl<D> DoubleEndedIterator for LittleEndianBigDigitIter<'_, D>  {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.digits.next_back()
    }
}

#[cfg(not(rustc_1_75))]
impl<D> ExactSizeIterator for LittleEndianBigDigitIter<'_, D>  {
    fn len(&self) -> usize {
        self.digits.len()
    }
}


impl<'a> LeBigDigitIterator<'a, u64> for num_bigint::U64Digits<'a> {}
impl<'a> LeBigDigitIterator<'a, u32> for num_bigint::U32Digits<'a> {}

impl<'a, D> LeBigDigitIterator<'a, &'a D> for stdlib::slice::Iter<'a, D> {}
impl<'a, D> LeBigDigitIterator<'a, &'a D> for stdlib::iter::Rev<stdlib::slice::Iter<'a, D>> {}
impl<'a, D> LeBigDigitIterator<'a, &'a mut D> for stdlib::slice::IterMut<'a, D> {}
impl<'a, D> LeBigDigitIterator<'a, &'a mut D> for stdlib::iter::Rev<stdlib::slice::IterMut<'a, D>> {}

impl<D> LeBigDigitIterator<'_, D> for stdlib::vec::IntoIter<D> {}
impl<D> LeBigDigitIterator<'_, D> for stdlib::iter::Rev<stdlib::vec::IntoIter<D>> {}
