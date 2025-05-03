//! Structs and traits for generic operations on big or little endian ints


/// Trait to allow generic parameterization of significant digit ordering
pub(crate) trait Endianness {
    /// Iterate over digits in vec from least to most significance
    fn into_iter<D>(digits: Vec<D>) -> impl Iterator<Item=D>;

    /// Iterate over mut digits in slice from least to most significance
    fn iter_slice_mut<D>(digits: &mut [D]) -> impl Iterator<Item=&mut D>;

    /// Place given digit at the most-significant end of the vecor
    fn push_significant_digit<D>(digits: &mut Vec<D>, d: D);
}


/// Empty struct indicating most-significant bigdigit first
#[derive(Copy,Clone,Debug)]
pub(crate) struct BigEndian {}

/// Empty struct indicating least-significant bigdigit first
#[derive(Copy,Clone,Debug)]
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
}
