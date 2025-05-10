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

    /// Place given digit at the most-significant end of the vecor
    fn push_significant_digit<D>(digits: &mut Vec<D>, d: D);

    /// Split slice into most-significant digit and 'the rest'
    ///
    /// If slice is empty zero and empty-slice is returned
    fn split_most_significant_digit<D: Zero + PrimInt>(digits: &[D]) -> (D, &[D]);
}

/// Empty struct indicating most-significant bigdigit first
#[derive(Copy, Clone, Debug, Default)]
pub(crate) struct BigEndian {}

/// Empty struct indicating least-significant bigdigit first
#[derive(Copy, Clone, Debug, Default)]
pub(crate) struct LittleEndian {}

impl Endianness for BigEndian {
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

    fn push_significant_digit<D>(digits: &mut Vec<D>, d: D) {
        digits.insert(0, d);
    }

    fn split_most_significant_digit<D: Copy + Zero>(digits: &[D]) -> (D, &[D]) {
        digits.split_first().map(|(&d, r)| (d, r)).unwrap_or((Zero::zero(), &[]))
    }
}


impl Endianness for LittleEndian {
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

    fn push_significant_digit<D>(digits: &mut Vec<D>, d: D) {
        digits.push(d);
    }

    fn split_most_significant_digit<D: Copy + Zero>(digits: &[D]) -> (D, &[D]) {
        digits.split_last().map(|(&d, r)| (d, r)).unwrap_or((Zero::zero(), &[]))
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

impl<'a> LeBigDigitIterator<'a, u64> for num_bigint::U64Digits<'a> {}
impl<'a> LeBigDigitIterator<'a, u32> for num_bigint::U32Digits<'a> {}

impl<'a, D> LeBigDigitIterator<'a, &'a D> for stdlib::slice::Iter<'a, D> {}
impl<'a, D> LeBigDigitIterator<'a, &'a D> for stdlib::iter::Rev<stdlib::slice::Iter<'a, D>> {}
impl<'a, D> LeBigDigitIterator<'a, &'a mut D> for stdlib::slice::IterMut<'a, D> {}
impl<'a, D> LeBigDigitIterator<'a, &'a mut D> for stdlib::iter::Rev<stdlib::slice::IterMut<'a, D>> {}

impl<D> LeBigDigitIterator<'_, D> for stdlib::vec::IntoIter<D> {}
impl<D> LeBigDigitIterator<'_, D> for stdlib::iter::Rev<stdlib::vec::IntoIter<D>> {}
