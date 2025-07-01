//! Structs and traits for generic operations on big or little endian ints

use crate::stdlib::fmt;
use crate::stdlib::Vec;
use num_traits::{Zero, PrimInt};


/// Trait to allow generic parameterization of significant digit ordering
pub(crate) trait Endianness : Copy + Clone + Default + fmt::Debug {
    /// Iterate over digits in vec from least to most significance
    fn into_iter<D>(digits: Vec<D>) -> impl Iterator<Item=D>;

    /// Iterate over mut digits in slice from least to most significance
    fn iter_slice_mut<D>(digits: &mut [D]) -> impl Iterator<Item=&mut D>;

    /// Place given digit at the most-significant end of the vecor
    fn push_significant_digit<D>(digits: &mut Vec<D>, d: D);

    /// Place given digit at the most-significant end of the vecor
    fn split_most_significant_digit<D: Zero + PrimInt>(digits: &[D]) -> (D, &[D]);

    /// Extract digits in correct order from bigiuint
    fn bigint_to_digits(n: &num_bigint::BigUint) -> Vec<u8>;

    /// Extract digits in correct order from bigiuint
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
    /// Iterate over digits in slice from least to most significance
    fn into_iter<D>(digits: Vec<D>) -> impl Iterator<Item=D> {
        digits.into_iter().rev()
    }

    fn iter_slice_mut<D>(digits: &mut [D]) -> impl Iterator<Item=&mut D>{
        digits.iter_mut().rev()
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
    fn into_iter<D>(digits: Vec<D>) -> impl Iterator<Item=D> {
        digits.into_iter()
    }

    fn iter_slice_mut<D>(digits: &mut [D]) -> impl Iterator<Item=&mut D> {
        digits.iter_mut()
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
