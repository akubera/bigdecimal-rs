//! Structs and traits for generic operations on big or little endian ints


/// Trait to allow generic parameterization of significant digit ordering
pub(crate) trait Endianness {}


/// Empty struct indicating most-significant bigdigit first
#[derive(Copy,Clone,Debug)]
pub(crate) struct BigEndian {}

/// Empty struct indicating least-significant bigdigit first
#[derive(Copy,Clone,Debug)]
pub(crate) struct LittleEndian {}

impl Endianness for BigEndian {}

impl Endianness for LittleEndian {}
