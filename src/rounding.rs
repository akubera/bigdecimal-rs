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
    pub fn round_u32(&self, at_digit: stdlib::num::NonZeroU8, sign: Sign, value: u32, trailing_zeros: bool) -> u32 {
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
#[allow(non_snake_case)]
mod test_round_pair {
    use paste::paste;
    use super::*;

    macro_rules! impl_test {
        ( $($mode:ident),+ => $expected:literal) => {
            $(
                paste! {
                    #[test]
                    fn [< mode_ $mode >]() {
                        let (pair, sign, trailing_zeros) = test_input();
                        let mode = self::RoundingMode::$mode;
                        let result = mode.round_pair(sign, pair, trailing_zeros);
                        assert_eq!(result, $expected);
                    }
                }
            )*
        }
    }

    macro_rules! define_test_input {
        ( - $lhs:literal . $rhs:literal $($t:tt)* ) => {
            define_test_input!(sign=Sign::Minus, pair=($lhs, $rhs), $($t)*);
        };
        ( $lhs:literal . $rhs:literal $($t:tt)*) => {
            define_test_input!(sign=Sign::Plus, pair=($lhs, $rhs), $($t)*);
        };
        ( sign=$sign:expr, pair=$pair:expr, ) => {
            define_test_input!(sign=$sign, pair=$pair, trailing_zeros=true);
        };
        ( sign=$sign:expr, pair=$pair:expr, 000x ) => {
            define_test_input!(sign=$sign, pair=$pair, trailing_zeros=false);
        };
        ( sign=$sign:expr, pair=$pair:expr, trailing_zeros=$trailing_zeros:literal ) => {
            fn test_input() -> ((u8, u8), Sign, bool) { ($pair, $sign, $trailing_zeros) }
        };
    }

    mod case_0_1 {
        use super::*;

        define_test_input!(0 . 1);

        impl_test!(Up, Ceiling => 1);
        impl_test!(Down, Floor, HalfUp, HalfDown, HalfEven => 0);
    }

    mod case_neg_0_1 {
        use super::*;

        define_test_input!(-0 . 1);

        impl_test!(Up, Floor => 1);
        impl_test!(Down, Ceiling, HalfUp, HalfDown, HalfEven => 0);
    }

    mod case_0_5 {
        use super::*;

        define_test_input!( 0 . 5 );

        impl_test!(Up, Ceiling, HalfUp => 1);
        impl_test!(Down, Floor, HalfDown, HalfEven => 0);
    }

    mod case_neg_0_5 {
        use super::*;

        define_test_input!(-0 . 5);

        impl_test!(Up, Floor, HalfUp => 1);
        impl_test!(Down, Ceiling, HalfDown, HalfEven => 0);
    }

    mod case_0_5_000x {
        use super::*;

        // ...000x indicates a non-zero trailing digit; affects behavior of rounding N.0 and N.5
        define_test_input!(0 . 5 000x);

        impl_test!(Up, Ceiling, HalfUp, HalfDown, HalfEven => 1);
        impl_test!(Down, Floor => 0);
    }

    mod case_neg_0_5_000x {
        use super::*;

        define_test_input!(-0 . 5 000x);

        impl_test!(Up, Floor, HalfUp, HalfDown, HalfEven => 1);
        impl_test!(Down, Ceiling => 0);
    }

    mod case_0_7 {
        use super::*;

        define_test_input!(0 . 7);

        impl_test!(Up, Ceiling, HalfUp, HalfDown, HalfEven => 1);
        impl_test!(Down, Floor => 0);
    }

    mod case_neg_0_7 {
        use super::*;

        define_test_input!(-0 . 7);

        impl_test!(Up, Floor, HalfUp, HalfDown, HalfEven => 1);
        impl_test!(Down, Ceiling => 0);
    }

    mod case_neg_4_3_000x {
        use super::*;

        define_test_input!(-4 . 3 000x);

        impl_test!(Up, Floor => 5);
        impl_test!(Down, Ceiling, HalfUp, HalfDown, HalfEven => 4);
    }


    mod case_9_5_000x {
        use super::*;

        define_test_input!(9 . 5 000x);

        impl_test!(Up, Ceiling, HalfDown, HalfUp, HalfEven => 10);
        impl_test!(Down, Floor => 9);
    }

    mod case_9_5 {
        use super::*;

        define_test_input!(9 . 5);

        impl_test!(Up, Ceiling, HalfUp, HalfEven => 10);
        impl_test!(Down, Floor, HalfDown => 9);
    }

    mod case_8_5 {
        use super::*;

        define_test_input!(8 . 5);

        impl_test!(Up, Ceiling, HalfUp => 9);
        impl_test!(Down, Floor, HalfDown, HalfEven => 8);
    }

    mod case_neg_6_5 {
        use super::*;

        define_test_input!(-6 . 5);

        impl_test!(Up, Floor, HalfUp => 7);
        impl_test!(Down, Ceiling, HalfDown, HalfEven => 6);
    }

    mod case_neg_6_5_000x {
        use super::*;

        define_test_input!(-6 . 5 000x);

        impl_test!(Up, Floor, HalfUp, HalfDown, HalfEven => 7);
        impl_test!(Down, Ceiling => 6);
    }

    mod case_3_0 {
        use super::*;

        define_test_input!(3 . 0);

        impl_test!(Up, Down, Ceiling, Floor, HalfUp, HalfDown, HalfEven => 3);
    }

    mod case_3_0_000x {
        use super::*;

        define_test_input!(3 . 0 000x);

        impl_test!(Up, Ceiling => 4);
        impl_test!(Down, Floor, HalfUp, HalfDown, HalfEven => 3);
    }

    mod case_neg_2_0 {
        use super::*;

        define_test_input!(-2 . 0);

        impl_test!(Up, Down, Ceiling, Floor, HalfUp, HalfDown, HalfEven => 2);
    }

    mod case_neg_2_0_000x {
        use super::*;

        define_test_input!(-2 . 0 000x);

        impl_test!(Up, Floor => 3);
        impl_test!(Down, Ceiling, HalfUp, HalfDown, HalfEven => 2);
    }
}


#[cfg(test)]
#[allow(non_snake_case)]
mod test_round_u32 {
    use paste::paste;
    use super::*;

    macro_rules! impl_test {
        ( $pos:literal :: $($mode:ident),+ => $expected:literal) => {
            $(
                paste! {
                    #[test]
                    fn [< digit_ $pos _mode_ $mode >]() {
                        let (value, sign, trailing_zeros) = test_input();
                        let mode = self::RoundingMode::$mode;
                        let pos = stdlib::num::NonZeroU8::new($pos as u8).unwrap();
                        let result = mode.round_u32(pos, sign, value, trailing_zeros);
                        assert_eq!(result, $expected);
                    }
                }
            )*
        }
    }

    macro_rules! define_test_input {
        ( - $value:literal $($t:tt)* ) => {
            define_test_input!(sign=Sign::Minus, value=$value $($t)*);
        };
        ( $value:literal $($t:tt)* ) => {
            define_test_input!(sign=Sign::Plus, value=$value $($t)*);
        };
        ( sign=$sign:expr, value=$value:literal ...000x ) => {
            define_test_input!(sign=$sign, value=$value, trailing_zeros=false);
        };
        ( sign=$sign:expr, value=$value:literal ) => {
            define_test_input!(sign=$sign, value=$value, trailing_zeros=true);
        };
        ( sign=$sign:expr, value=$value:expr, trailing_zeros=$trailing_zeros:literal ) => {
            fn test_input() -> (u32, Sign, bool) { ($value, $sign, $trailing_zeros) }
        };
    }

    mod case_13950000 {
        use super::*;

        define_test_input!(13950000);

        impl_test!(3 :: Up => 13950000);
        impl_test!(5 :: Up, Ceiling, HalfUp, HalfEven => 14000000);
        impl_test!(5 :: Down, HalfDown => 13900000);
    }

    mod case_neg_35488622_000x {
         use super::*;

        // ...000x indicates non-zero trailing digit
        define_test_input!(-35488622 ...000x);

        impl_test!(1 :: Up => 35488630);
        impl_test!(1 :: Down => 35488620);
        impl_test!(2 :: Up => 35488700);
        impl_test!(2 :: Down => 35488600);
        impl_test!(7 :: Up, Floor => 40000000);
        impl_test!(7 :: Down, Ceiling => 30000000);
        impl_test!(8 :: Up => 100000000);
        impl_test!(8 :: Down => 0);
    }
}
