//! Structs and traits for generic operations on big or little endian ints

use crate::stdlib::fmt;
use crate::stdlib::Vec;
use num_traits::{Zero, PrimInt};

use super::radix::RadixType;

/// Trait to allow generic parameterization of significant digit ordering
pub(crate) trait Endianness : Copy + Clone + Default + fmt::Debug {
    /// Iterate over digits in vec from least to most significance
    #[cfg(rustc_1_75)]
    #[allow(dead_code)]
    fn into_iter<D>(digits: Vec<D>) -> impl Iterator<Item=D>;

    /// Iterate over mut digits in slice from least to most significance
    #[cfg(rustc_1_75)]
    fn iter_slice_mut<D>(digits: &mut [D]) -> impl Iterator<Item=&mut D>;

    #[cfg(not(rustc_1_75))]
    #[allow(dead_code)]
    fn into_iter<'a, D: 'static>(digits: Vec<D>) -> LittleEndianBigDigitIter<'a, D>;

    #[cfg(not(rustc_1_75))]
    fn iter_slice_mut<'a, D>(digits: &'a mut [D]) -> LittleEndianBigDigitIter<'a, &'a mut D>;

    /// Add 'carry' into digits, starting at least-significant digit 'idx'
    fn addassign_carry_into_slice_at<R: RadixType>(
        digits: &mut [R::Base], carry: &mut R::Base, idx: usize
    ) {
        for dest in Self::iter_slice_mut(digits).skip(idx) {
            R::addassign_carry(dest, carry);
            if carry.is_zero() {
                return;
            }
        }
    }

    /// Place given digit at the most-significant end of the vecor
    fn push_significant_digit<D>(digits: &mut Vec<D>, d: D);

    /// Split slice into most-significant digit and 'the rest'
    ///
    /// If slice is empty zero and empty-slice is returned
    fn split_most_significant_digit<D: Zero + PrimInt>(digits: &[D]) -> (D, &[D]);

    /// Extract base-10 digits in endian-order from bigiuint
    fn bigint_to_digits(n: &num_bigint::BigUint) -> Vec<u8>;

    /// Build BigUint from base-10 digits in slice
    fn biguint_from_digits(n: &[u8]) -> Option<num_bigint::BigUint>;

    /// Remove any zeros at the location of highest significance, if all zeros
    /// the vector will be cleared
    fn strip_significant_zeros<D: Copy + Zero>(digits: &mut Vec<D>);
}


/// Empty struct indicating most-significant bigdigit first
#[derive(Copy,Clone,Debug,Default)]
pub(crate) struct BigEndian {}

/// Empty struct indicating least-significant bigdigit first
#[derive(Copy,Clone,Debug,Default)]
pub(crate) struct LittleEndian {}


impl Endianness for BigEndian {
    #[cfg(rustc_1_75)]
    fn into_iter<D>(digits: Vec<D>) -> impl Iterator<Item=D> {
        digits.into_iter().rev()
    }

    #[cfg(rustc_1_75)]
    fn iter_slice_mut<D>(digits: &mut [D]) -> impl Iterator<Item=&mut D> {
        digits.iter_mut().rev()
    }

    #[cfg(not(rustc_1_75))]
    fn into_iter<'a, D: 'static>(digits: Vec<D>) -> LittleEndianBigDigitIter<'a, D> {
        LittleEndianBigDigitIter { digits: Box::new(digits.into_iter().rev()) }
    }

    #[cfg(not(rustc_1_75))]
    fn iter_slice_mut<'a, D>(digits: &'a mut [D]) -> LittleEndianBigDigitIter<'a, &'a mut D> {
        LittleEndianBigDigitIter { digits: Box::new(digits.iter_mut().rev()) }
    }

    fn push_significant_digit<D>(digits: &mut Vec<D>, d: D) {
        digits.insert(0, d);
    }

    fn split_most_significant_digit<D: Copy + Zero>(digits: &[D]) -> (D, &[D]) {
        digits.split_first().map(|(&d, r)| (d, r)).unwrap_or((num_traits::Zero::zero(), &[]))
    }

    fn bigint_to_digits(n: &num_bigint::BigUint) -> Vec<u8> {
        n.to_radix_be(10)
    }

    fn biguint_from_digits(n: &[u8]) -> Option<num_bigint::BigUint> {
        num_bigint::BigUint::from_radix_be(n, 10)
    }

    fn strip_significant_zeros<D: Copy + Zero>(digits: &mut Vec<D>){
        if let Some(idx) = digits.iter().position(|d| !d.is_zero()) {
            digits.copy_within(idx.., 0);
            digits.truncate(digits.len() - idx);
        } else {
            digits.clear();
        }
    }
}


impl Endianness for LittleEndian {
    #[cfg(rustc_1_75)]
    fn into_iter<D>(digits: Vec<D>) -> impl Iterator<Item=D> {
        digits.into_iter()
    }

    #[cfg(rustc_1_75)]
    fn iter_slice_mut<D>(digits: &mut [D]) -> impl Iterator<Item=&mut D> {
        digits.iter_mut()
    }

    #[cfg(not(rustc_1_75))]
    fn into_iter<'a, D: 'static>(digits: Vec<D>) -> LittleEndianBigDigitIter<'a, D> {
        LittleEndianBigDigitIter { digits: Box::new(digits.into_iter()) }
    }

    #[cfg(not(rustc_1_75))]
    fn iter_slice_mut<'a, D>(digits: &'a mut [D]) -> LittleEndianBigDigitIter<'a, &'a mut D> {
        LittleEndianBigDigitIter { digits: Box::new(digits.into_iter()) }
    }

    fn push_significant_digit<D>(digits: &mut Vec<D>, d: D) {
        digits.push(d);
    }

    fn split_most_significant_digit<D: Copy + Zero>(digits: &[D]) -> (D, &[D]) {
        digits.split_last().map(|(&d, r)| (d, r)).unwrap_or((num_traits::Zero::zero(), &[]))
    }

    fn bigint_to_digits(n: &num_bigint::BigUint) -> Vec<u8> {
        n.to_radix_le(10)
    }

    fn biguint_from_digits(n: &[u8]) -> Option<num_bigint::BigUint> {
        num_bigint::BigUint::from_radix_le(n, 10)
    }

    fn strip_significant_zeros<D: Zero>(digits: &mut Vec<D>){
        if let Some(idx) = digits.iter().rposition(|d| !d.is_zero()) {
            digits.truncate(idx + 1);
        } else {
            digits.clear();
        }
    }
}


#[cfg(not(rustc_1_75))]
pub(crate) struct LittleEndianBigDigitIter<'a, D> {
    digits: Box<dyn Iterator<Item=D> + 'a>
}

#[cfg(not(rustc_1_75))]
impl<D> Iterator for LittleEndianBigDigitIter<'_, D> {
    type Item = D;

    fn next(&mut self) -> Option<Self::Item> {
        self.digits.next()
    }
}
