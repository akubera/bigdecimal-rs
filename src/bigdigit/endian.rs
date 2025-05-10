//! Structs and traits for generic operations on big or little endian ints

use crate::stdlib::fmt;
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
}
