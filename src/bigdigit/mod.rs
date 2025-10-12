//! BigDigit types and routines
//!
//! Constants and structures defining the "BigDigit" components of BigDecimal.
//!
//! BigDigit is generic over Radix types, allowing the properties of
//! a bigdigit to be specified in the radix, and the the overall behavior
//! of the bigdigit (i.e. add_with_carry) as methods on the BigDigit.
//!
//! NOTE: These are distinct from the BigDigits in num_bigint.
//!

pub mod alignment;
pub mod digitvec;
pub mod endian;
pub mod radix;
