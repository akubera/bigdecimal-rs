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
#![allow(non_camel_case_types)]
#![allow(dead_code)]


// struct DigitBuffer;

use stdlib::marker::PhantomData;
use stdlib::u64;
use stdlib::vec::Vec;

/// Stateless endianess type to indicate BigEndian digit storage
pub struct BigEndian;

/// Stateless endianess type to indicate LittleEndian digit storage
pub struct LittleEndian;

/// Trait to allow genric parameterization of DigitBuffers endianess
pub trait Endianess {}

impl Endianess for BigEndian {}
impl Endianess for LittleEndian {}


/// Radix=*10* / storage=*u8*
pub struct RADIX_10_u8;

/// Radix=*10,000* storage=*i16*
pub struct RADIX_10E4_i16;
pub struct Radix10e9;
pub struct Radix2e32;
pub struct Radix2e64;

pub trait RadixType {
    type Base;
    type BaseDouble;

    fn radix() -> Self::BaseDouble;
}

macro_rules! impl_radix_type {
    ($t:ty : base=$base:ty, base-double=$doublewide:ty, radix=$radix:expr) => {
        impl RadixType for $t {
            type Base = $base;
            type BaseDouble = $doublewide;

            fn radix() -> Self::BaseDouble { $radix }
        }
    };
}

impl_radix_type!(
    Radix2e64:
        base = u64,
        base-double = u128,
        radix = u64::MAX as u128 + 1
);

impl_radix_type!(
    Radix2e32:
        base = u32,
        base-double = u64,
        radix = u32::MAX as u64 + 1
);

impl_radix_type!(
    RADIX_10E4_i16:
        base = i16,
        base-double = i32,
        radix = 10_000
);

impl_radix_type!(
    Radix10e9:
        base = u32,
        base-double = u64,
        radix = 1_000_000_000
);

impl_radix_type!(
    RADIX_10_u8:
        base = u8,
        // u8 can fit 10**2, so it's appropriate for double-wide type
        base-double = u8,
        radix = 10
);

//struct DigitBuffer<T, E: Endianess> {
//}
//

/// Generic Digit Buffer
///
pub struct DigitBuf<E: Endianess, R: RadixType> {
    _data: Vec<R::Base>,
    _endianess: PhantomData<E>,
    _radix: PhantomData<R>,
}


/// Buffer of individual digits
pub type IndividualDigitBuf = DigitBuf<BigEndian, RADIX_10_u8>;

/// Buffer storing 9 decimal digits in a u32
pub type StandardDigitBuf = DigitBuf<LittleEndian, Radix10e9>;

pub type PostgresStyle = DigitBuf<LittleEndian, RADIX_10E4_i16>;


enum DigitBuffers {
    /// Individual digits
    Individual(IndividualDigitBuf),
    ///
    Standard(IndividualDigitBuf),
    /// Postgres style
    Postgres(PostgresStyle),
}

pub struct DigitInfo {
    /// Any of the digit buffers
    data: DigitBuffers,
}
