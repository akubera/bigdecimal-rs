//! Rounding structures and subroutines

use crate::Sign;
use stdlib;

/// Determines how to calculate the last digit of the number
///
/// Default rounding mode is HalfUp
///
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
    /// * sign (Sign) - Sign of the number to be rounded
    /// * pair (u8, u8) - The two digits in question to be rounded.
    ///     i.e. to round 0.345 to two places, you would pass (4, 5).
    ///          As decimal digits, they
    ///     must be less than ten!
    /// * trailing_zeros (bool) - True if all digits after the pair are zero.
    ///       This has an effect if the right hand digit is 0 or 5.
    ///
    /// Returns
    /// -------
    /// Returns the first number of the pair, rounded. The sign is not preserved.
    ///
    /// Examples
    /// --------
    /// - To round 2341, pass in `Plus, (4, 1), true` → get 4 or 5 depending on scheme
    /// - To round -0.1051, to two places: `Minus, (0, 5), false` → returns either 0 or 1
    /// - To round -0.1, pass in `true, (0, 1)` → returns either 0 or 1
    ///
    /// Calculation of pair of digits from full number, and the replacement of that number
    /// should be handled separately
    ///
    pub fn round_pair(&self, sign: Sign, pair: (u8, u8), trailing_zeros: bool) -> u8 {
        use self::RoundingMode::*;
        use stdlib::cmp::Ordering::*;

        let (lhs, rhs) = pair;
        // if all zero after digit, never round
        if rhs == 0 && trailing_zeros {
            return lhs;
        }
        let up = lhs + 1;
        let down = lhs;
        match (*self, rhs.cmp(&5)) {
            (Up,        _) => up,
            (Down,      _) => down,
            (Floor,     _) => if sign == Sign::Minus { up } else { down },
            (Ceiling,   _) => if sign == Sign::Minus { down } else { up },
            (_,      Less) => down,
            (_,      Greater) => up,
            (_,        Equal) if !trailing_zeros => up,
            (HalfUp,   Equal) => up,
            (HalfDown, Equal) => down,
            (HalfEven, Equal) => if lhs % 2 == 0 { down } else { up },
        }
    }

    /// Round value at particular digit, returning replacement digit
    ///
    /// Parameters
    /// ----------
    /// * at_digit (NonZeroU8) - 0-based index of digit at which to round.
    ///                  0 would be the first digit, and would
    ///
    /// * sign (Sign) - Sign of the number to be rounded
    /// * value (u32) - The number containing digits to be rounded.
    /// * trailing_zeros (bool) - True if all digits after the value are zero.
    ///
    /// Returns
    /// -------
    /// Returns the first number of the pair, rounded. The sign is not preserved.
    ///
    /// Examples
    /// --------
    /// - To round 823418, at digit-index 3: `3, Plus, 823418, true` → 823000 or 824000, depending on scheme
    /// - To round -100205, at digit-index 1: `1, Minus, 100205, true` → 100200 or 100210
    ///
    /// Calculation of pair of digits from full number, and the replacement of that number
    /// should be handled separately
    ///
    pub fn round_u32(
        &self,
        at_digit: stdlib::num::NonZeroU8,
        sign: Sign,
        value: u32,
        trailing_zeros: bool,
    ) -> u32 {
        let shift = 10u32.pow(at_digit.get() as u32 - 1);
        let splitter = shift * 10;

        // split 'value' into high and low
        let (top, bottom) = num_integer::div_rem(value, splitter);
        let lhs = (top % 10) as u8;
        let (rhs, remainder) = num_integer::div_rem(bottom, shift);
        let pair = (lhs, rhs as u8);
        let rounded = self.round_pair(sign, pair, trailing_zeros && remainder == 0);

        // replace low digit with rounded value
        let full = top - lhs as u32 + rounded as u32;

        // shift rounded value back to position
        full * splitter
    }
}


#[cfg(test)]
include!("rounding.tests.rs");
