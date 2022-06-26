// \file src/context.rs

//! A `Context` object is the set of parameters that define otherwise
//! ambiguous arithmetical operations.
//!
//! Each BigDecimal object has its own context object, and all
//! operations will follow the more 'restricted' rule.

use std::cmp;

pub static DEFAULT_PRECISION: u64 = 34;
pub static DEFAULT_MAX_PRECISION: u64 = 999999999;
pub static DEFAULT_ROUNDING_MODE: RoundingMode = RoundingMode::HalfEven;

static MAX_EXP: i32 = 999999999;
static MIN_EXP: i32 = -999999999;

/// Information regarding behavior of certain BigDecimal operations
///
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct Context {
    /// The maximum number of digits to store
    pub precision: u64,

    /// Method to round numbers
    pub rounding_mode: RoundingMode,

    /// Maximum positive exponent
    pub exp_max: i32,

    /// Minimun exponent (negative)
    pub exp_min: i32,

    /// Trap-enabler flags
    pub traps: u32,

    /// status flags
    pub status: Status,

    /// Apply exponent clamp
    pub clamp: bool,
}

impl Default for Context {
    fn default() -> Context {
        Context {
            precision: DEFAULT_PRECISION,
            rounding_mode: DEFAULT_ROUNDING_MODE,
            exp_max: MAX_EXP,
            exp_min: MIN_EXP,
            status: Status { bits: 0 },
            traps: 0x00000002,
            clamp: false,
        }
    }
}

impl Context {
    pub fn merge(lhs: &Context, rhs: &Context) -> Context {
        Context {
            precision: cmp::min(lhs.precision, rhs.precision),
            rounding_mode: lhs.rounding_mode,
            exp_max: cmp::max(lhs.exp_max, rhs.exp_max),
            exp_min: cmp::min(lhs.exp_min, rhs.exp_min),
            status: Status { bits: 0 },
            traps: lhs.traps | rhs.traps,
            clamp: false,
        }
    }
}

bitflags! {
    /// Operation status flags stored in context object
    pub struct Status: u32 {
        /// Operation has overflowed
        const OVERFLOW             = 0x00000200;
        /// Operation has underflowed to zero
        const UNDERFLOW            = 0x00002000;
        /// Operation output was affected by boundary limits
        const CLAMPED              = 0x00000400;
        /// Rounding occurred though possibly no information was lost
        const ROUNDED              = 0x00000800;
        /// Divide by zero
        const DIVBYZERO            = 0x00000002;
        /// Divide by zero
        const DIVIMPOSSIBLE        = 0x00000004;
        /// Output too big
        const INSUFFICIENT_STORAGE = 0x00000010;
        /// Indicates that rounding occurred and the result is not exact
        const INEXACT              = 0x00000020;
    }
}

/// Determines how to calculate the last digit of the number
///
/// Default rounding mode is HalfUp
///
#[allow(non_snake_case)]
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum RoundingMode {
    /// Always round away from zero
    ///
    ///
    /// * 5.5 → 6.0
    /// * 2.5 → 3.0
    /// * 1.6 → 2.0
    /// * 1.1 → 2.0
    /// * -1.1 → -2.0
    /// * -1.6 → -2.0
    /// * -2.5 → -3.0
    /// * -5.5 → -6.0
    Up,

    /// Always round towards zero
    ///
    /// * 5.5  →  5.0
    /// * 2.5  →  2.0
    /// * 1.6  →  1.0
    /// * 1.1  →  1.0
    /// * -1.1 → -1.0
    /// * -1.6 → -1.0
    /// * -2.5 → -2.0
    /// * -5.5 → -5.0
    Down,

    /// Towards +∞
    ///
    /// * 5.5 → 6.0
    /// * 2.5 → 3.0
    /// * 1.6 → 2.0
    /// * 1.1 → 2.0
    /// * -1.1 → -1.0
    /// * -1.6 → -1.0
    /// * -2.5 → -2.0
    /// * -5.5 → -5.0
    Ceiling,

    /// Towards -∞
    ///
    /// * 5.5 → 5.0
    /// * 2.5 → 2.0
    /// * 1.6 → 1.0
    /// * 1.1 → 1.0
    /// * -1.1 → -2.0
    /// * -1.6 → -2.0
    /// * -2.5 → -3.0
    /// * -5.5 → -6.0
    Floor,

    /// Round to 'nearest neighbor', or up if ending decimal is 5
    ///
    /// * 5.5 → 6.0
    /// * 2.5 → 3.0
    /// * 1.6 → 2.0
    /// * 1.1 → 1.0
    /// * -1.1 → -1.0
    /// * -1.6 → -2.0
    /// * -2.5 → -3.0
    /// * -5.5 → -6.0
    HalfUp,

    /// Round to 'nearest neighbor', or down if ending decimal is 5
    ///
    /// * 5.5 → 5.0
    /// * 2.5 → 2.0
    /// * 1.6 → 2.0
    /// * 1.1 → 1.0
    /// * -1.1 → -1.0
    /// * -1.6 → -2.0
    /// * -2.5 → -2.0
    /// * -5.5 → -5.0
    HalfDown,

    /// Round to 'nearest neighbor', if equidistant, round towards
    /// nearest even digit
    ///
    /// * 5.5 → 6.0
    /// * 2.5 → 2.0
    /// * 1.6 → 2.0
    /// * 1.1 → 1.0
    /// * -1.1 → -1.0
    /// * -1.6 → -2.0
    /// * -2.5 → -2.0
    /// * -5.5 → -6.0
    ///
    HalfEven,
}


impl RoundingMode {
    /// Perform the rounding operation
    ///
    /// Parameters
    /// ----------
    /// * Signed (bool) - True if number should be interpreted as negative
    /// * Pair (u8, u8) - The two digits in question to be rounded.
    ///     i.e. to round 0.345, you would pass (4, 5). As decimal digits, they
    ///     must be less than ten!
    ///
    /// Returns
    /// -------
    /// Returns the first number of the pair, rounded. The sign is not preserved.
    ///
    /// Examples
    /// --------
    /// - To round 2341, pass in `false, (4, 1)` → get 4 or 5 depending on scheme
    /// - To round -0.1, pass in `true, (0, 1)` → returns either 0 or 1
    ///
    pub fn round_digits(&self, signed: bool, pair: (u8, u8)) -> u8
    {
        use RoundingMode::*;
        let (lhs, rhs) = pair;

        if rhs == 0 {
            return lhs;
        }

        match *self {
            Up => lhs + 1,
            Down => lhs,
            Floor => lhs + signed as u8,
            Ceiling => lhs + 1 - signed as u8,

            HalfUp => if rhs >= 5 { lhs + 1 } else { lhs },
            HalfDown => if rhs > 5 { lhs + 1 } else { lhs },
            HalfEven => if rhs > 5 || rhs == 5 && lhs % 2 != 0 { lhs + 1 } else { lhs },
        }
    }
}


#[cfg(test)]
mod context_tests {

    #[test]
    fn test_do_rounding() {
        use RoundingMode::*;


        // (a, b, c, d) => round(a.b)->c  round(-a.b)->d
        let vals = vec![
            (Up, (0, 0), 0, 0),
                                      //       0.1  -0.1
            (Up, (0, 1), 1, -1),      //  Up    1    -1
            (Down, (0, 1), 0, 0),     // Down   0     0
            (Ceiling, (0, 1), 1, 0),  // Ceil   1     0
            (Floor, (0, 1), 0, -1),   // Floor  0    -1

                                       //       0.7  -0.7
            (Up, (0, 7), 1, -1),       //  Up    1    -1
            (Down, (0, 7), 0, 0),      // Down   0     0
            (Ceiling, (0, 7), 1, 0),   // Ceil   1     0
            (Floor, (0, 7), 0, -1),    // Floor  0    -1
            (HalfUp, (0, 7), 1, -1),   //  HUP   1    -1
            (HalfDown, (0, 7), 1, -1), //  HDN   1    -1
            (HalfEven, (0, 7), 1, -1), //  HEV   1    -1

                                       //        1.5   -1.5
            (HalfUp, (1, 5), 2, -2),   //  HUP    2     -2
            (HalfDown, (1, 5), 1, -1), //  HDN    1     -1
            (HalfEven, (1, 5), 2, -2), //  HDN    2     -2

                                       //        2.5   -2.5
            (HalfUp, (2, 5), 3, -3),   //  HUP    3     -3
            (HalfDown, (2, 5), 2, -2), //  HDN    2     -2
            (HalfEven, (2, 5), 2, -2), //  HEV    2     -2

            (HalfDown, (0, 6), 1, -1),
            (HalfDown, (0, 5), 0, -0),
            (HalfDown, (0, 4), 0, -0),
            (HalfEven, (0, 5), 0, 0),

            (Up, (3, 0), 3, -3),
            (Down, (3, 0), 3, -3),
            (Up, (3, 0), 3, -3),
        ];

        for (mode, a, b, c) in vals {
            assert_eq!(mode.round_digits(false, a), b);
            assert_eq!(mode.round_digits(true, a) as i8, -c);
        }
    }
}
