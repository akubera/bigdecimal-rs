// \file src/context.rs

//! A `Context` object is the set of parameters that define otherwise
//! ambiguous arithmetical operations.
//!
//! Each BigDecimal object has its own context object, and all
//! operations will follow the more 'restricted' rule.

use std::cmp;

pub static DEFAULT_PRECISION: u64 = 34;
pub static DEFAULT_ROUNDING_MODE: RoundingMode = RoundingMode::HalfEven;

/// Information regarding behavior of certain BigDecimal operations
///
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct Context {
    /// The maximum number of digits to store
    pub precision: u64,

    /// Method to round numbers
    pub rounding_mode: RoundingMode,
}

impl Default for Context {
    fn default() -> Context {
        Context {
            precision: DEFAULT_PRECISION,
            rounding_mode: DEFAULT_ROUNDING_MODE,
        }
    }
}

impl Context {
    pub fn merge(lhs: &Context, rhs: &Context) -> Context {
        Context {
            precision: cmp::min(lhs.precision, rhs.precision),
            rounding_mode: lhs.rounding_mode,
        }
    }
}

/// Determines how to calculate the last digit of the number
///
/// Default rounding mode is HalfUp
///
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum RoundingMode {
    /// Always round away from zero
    ///
    ///
    /// * 5.5 -> 6.0
    /// * 2.5 -> 3.0
    /// * 1.6 -> 2.0
    /// * 1.1 -> 2.0
    /// * 1.0 -> 1.0
    /// * -1.0 -> -1.0
    /// * -1.1 -> -2.0
    /// * -1.6 -> -2.0
    /// * -2.5 -> -3.0
    /// * -5.5 -> -6.0
    Up,

    /// Always round towards zero
    ///
    /// |  |      |
    /// |-----:|:-----|
    /// | 5.5  | 5.0  |
    /// | 2.5  | 2.0  |
    /// | 1.6  | 1.0  |
    /// | 1.1  | 1.0  |
    /// | 1.0  | 1.0  |
    /// | -1.0 | -1.0 |
    /// | -1.1 | -1.0 |
    /// | -1.6 | -1.0 |
    /// | -2.5 | -2.0 |
    /// | -5.5 | -5.0 |
    Down,

    /// Towards +∞
    ///
    /// * 5.5 -> 6.0
    /// * 2.5 -> 3.0
    /// * 1.6 -> 2.0
    /// * 1.1 -> 2.0
    /// * 1.0 -> 1.0
    /// * -1.0 -> -1.0
    /// * -1.1 -> -1.0
    /// * -1.6 -> -1.0
    /// * -2.5 -> -2.0
    /// * -5.5 -> -5.0
    Ceiling,

    /// Towards -∞
    ///
    /// * 5.5 -> 5.0
    /// * 2.5 -> 2.0
    /// * 1.6 -> 1.0
    /// * 1.1 -> 1.0
    /// * 1.0 -> 1.0
    /// * -1.0 -> -1.0
    /// * -1.1 -> -2.0
    /// * -1.6 -> -2.0
    /// * -2.5 -> -3.0
    /// * -5.5 -> -6.0
    Floor,

    /// Round to 'nearest neighbor', or up if ending decimal is 5
    ///
    /// * 5.5 -> 6.0
    /// * 2.5 -> 3.0
    /// * 1.6 -> 2.0
    /// * 1.1 -> 1.0
    /// * 1.0 -> 1.0
    /// * -1.0 -> -1.0
    /// * -1.1 -> -1.0
    /// * -1.6 -> -2.0
    /// * -2.5 -> -3.0
    /// * -5.5 -> -6.0
    HalfUp,

    /// Round to 'nearest neighbor', or down if ending decimal is 5
    ///
    /// * 5.5 -> 5.0
    /// * 2.5 -> 2.0
    /// * 1.6 -> 2.0
    /// * 1.1 -> 1.0
    /// * 1.0 -> 1.0
    /// * -1.0 -> -1.0
    /// * -1.1 -> -1.0
    /// * -1.6 -> -2.0
    /// * -2.5 -> -2.0
    /// * -5.5 -> -5.0
    HalfDown,

    /// Round to 'nearest neighbor', if equidistant, round towards
    /// nearest even digit
    ///
    /// * 5.5 -> 6.0
    /// * 2.5 -> 2.0
    /// * 1.6 -> 2.0
    /// * 1.1 -> 1.0
    /// * 1.0 -> 1.0
    /// * -1.0 -> -1.0
    /// * -1.1 -> -1.0
    /// * -1.6 -> -2.0
    /// * -2.5 -> -2.0
    /// * -5.5 -> -6.0
    HalfEven,
}
