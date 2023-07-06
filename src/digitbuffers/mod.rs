//! Definitions of owned collections of digits
//!
//! The choice how to store the digits in a BigDecimal is a very
//! important one, and hard to maintain both flexibility and
//! efficiency.
//!
//! Some layouts may be optimized for math operations, others for
//! reading & writing. Most likely the most efficient ones are
//! those matching the source of the digits: strings of human
//! readable, or base-10000,
//!
//! This module
//!

// struct DigitBuffer;

use stdlib::marker::PhantomData;

/// Stateless endianess type to indicate BigEndian digit storage
pub struct BigEndian;

/// Stateless endianess type to indicate LittleEndian digit storage
pub struct LittleEndian;

/// Trait to allow genric parameterization of DigitBuffers endianess
pub trait Endianess {}

impl Endianess for BigEndian {}
impl Endianess for LittleEndian {}

//struct DigitBuffer<T, E: Endianess> {
//}
//

/// Generic Digit Buffer
///
pub struct DigitBuf<BaseType, E: Endianess> {
    _data: Vec<BaseType>,
    _endianess: PhantomData<E>,
}


/// Buffer of individual digits
pub type IndividualDigitBuf = DigitBuf<u8, BigEndian>;
