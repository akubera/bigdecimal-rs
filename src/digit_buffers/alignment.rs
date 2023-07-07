//! Alignment of digits within digit-buffer
//!
//! The naive, unaligned state of digit-buffer starts (or ends) with
//! the least signficiant digit.
//! This makes adding and subtracting digits within a digit vector
//! very inefficient, as work must be done to shift the values of
//! the big digits so they line up properly.
//!
//! The alignment structs provide a solution to this, as they data
//! add zeros to the end of the number such that, given the scale
//! of the bigdecimal, the boundary of the 'ones' digit (10^0) falls
//! on the boundary of the big digits.
//! This guarantees that aligned bigdecimals will have their digits
//! in lock-step, and bigdecimals only need to calculate the relative
//! offset of bigdigts within their own vectors (which should be
//! trivial compared to shifting every digit relative to a precision
//! point).
//!

/// AlignmentDetails
#[derive(Debug)]
pub(crate) struct AlignmentDetails {
    pub a_digits_to_skip: usize,
    pub shifted_a_count: usize,
    pub a_offset: usize,
    pub shifted_b_count: usize,
    pub b_offset: usize,
}
