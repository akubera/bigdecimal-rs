//! Define arithmetical context
//!

use crate::rounding::RoundingMode;
use stdlib::num::NonZeroU64;
use stdlib;

use num_traits::{ToPrimitive, Zero};

use crate::{
    Sign,
    BigDecimal,
    BigDecimalRef
};

// const DEFAULT_PRECISION: u64 = ${RUST_BIGDECIMAL_DEFAULT_PRECISION} or 100;
include!(concat!(env!("OUT_DIR"), "/default_precision.rs"));

/// Mathematical Context
///
/// Stores rules for numerical operations, such as how to round and
/// number of digits to keep.
///
/// Defaults are defined at compile time, determined by environment
/// variables:
///
/// | Variable                                |   Descripiton   | default  |
/// |-----------------------------------------|-----------------|----------|
/// | `RUST_BIGDECIMAL_DEFAULT_PRECISION`     | digit precision | 100      |
/// | `RUST_BIGDECIMAL_DEFAULT_ROUNDING_MODE` | rounding-mode   | HalfEven |
///
/// It is recommended that the user set explict values of a Context and *not*
/// rely on compile time constants, but the option is there if necessary.
///
#[derive(Debug, Clone)]
pub struct Context {
    /// total number of digits
    precision: NonZeroU64,
    /// how to round
    rounding: RoundingMode,
}

impl Context {
    /// Create context with precision and rounding mode
    pub fn new(precision: NonZeroU64, rounding: RoundingMode) -> Self {
        Context {
            precision: precision,
            rounding: rounding,
        }
    }

    /// Copy context with new precision value
    pub fn with_precision(&self, precision: NonZeroU64) -> Self {
        Self {
            precision: precision,
            ..*self
        }
    }

    /// Copy context with new precision value
    pub fn with_prec<T: ToPrimitive>(&self, precision: T) -> Option<Self> {
        precision
            .to_u64()
            .map(NonZeroU64::new)
            .flatten()
            .map(|prec| {
                Self {
                    precision: prec,
                    ..*self
                }
            })
    }

    /// Copy context with new rounding mode
    pub fn with_rounding_mode(&self, mode: RoundingMode) -> Self {
        Self {
            rounding: mode,
            ..*self
        }
    }

    /// Return maximum precision
    pub fn precision(&self) -> NonZeroU64 {
        self.precision
    }

    /// Return rounding mode
    pub fn rounding_mode(&self) -> RoundingMode {
        self.rounding
    }

    /// Round digits x and y with the rounding mode
    pub(crate) fn round_pair(&self, sign: Sign, x: u8, y: u8, trailing_zeros: bool) -> u8 {
        self.rounding.round_pair(sign, (x, y), trailing_zeros)
    }

    /// Round digits x and y with the rounding mode
    #[allow(dead_code)]
    pub(crate) fn round_pair_with_carry(&self, sign: Sign, x: u8, y: u8, trailing_zeros: bool, carry: &mut u8) -> u8 {
        let r = self.round_pair(sign, x, y, trailing_zeros);
        if r == 10 {
            *carry = 1;
            0
        } else {
            r
        }
    }
}

impl stdlib::default::Default for Context {
    fn default() -> Self {
        Self {
            precision: NonZeroU64::new(DEFAULT_PRECISION).unwrap(),
            rounding: RoundingMode::HalfEven,
        }
    }
}

impl Context {
    /// Add two big digit references
    pub fn add_refs<'a, 'b, A, B>(&self, a: A, b: B) -> BigDecimal
    where
        A: Into<BigDecimalRef<'a>>,
        B: Into<BigDecimalRef<'b>>,
    {
        let mut sum = BigDecimal::zero();
        self.add_refs_into(a, b, &mut sum);
        sum
    }

    /// Add two decimal refs, storing value in dest
    pub fn add_refs_into<'a, 'b, A, B>(&self, a: A, b: B, dest: &mut BigDecimal)
    where
        A: Into<BigDecimalRef<'a>>,
        B: Into<BigDecimalRef<'b>>,
    {
        let a = a.into();
        let b = b.into();
        let sum = a.to_owned() + b.to_owned();
        *dest = sum.with_precision_round(self.precision, self.rounding)
    }
}


#[cfg(test)]
mod test_context {
    use super::*;

    #[test]
    fn contstructor_and_setters() {
        let ctx = Context::default();
        let c = ctx.with_prec(44).unwrap();
        assert_eq!(c.precision.get(), 44);
        assert_eq!(c.rounding, RoundingMode::HalfEven);

        let c = c.with_rounding_mode(RoundingMode::Down);
        assert_eq!(c.precision.get(), 44);
        assert_eq!(c.rounding, RoundingMode::Down);
    }

    #[test]
    fn sum_two_references() {
        use stdlib::ops::Neg;

        let ctx = Context::default();
        let a: BigDecimal = "209682.134972197168613072130300".parse().unwrap();
        let b: BigDecimal = "3.0782968222271332463325639E-12".parse().unwrap();

        let sum = ctx.add_refs(&a, &b);
        assert_eq!(sum, "209682.1349721971716913689525271332463325639".parse().unwrap());

        // make negative copy of b without cloning values
        let neg_b = b.to_ref().neg();

        let sum = ctx.add_refs(&a, neg_b);
        assert_eq!(sum, "209682.1349721971655347753080728667536674361".parse().unwrap());

        let sum = ctx.with_prec(27).unwrap().with_rounding_mode(RoundingMode::Up).add_refs(&a, neg_b);
        assert_eq!(sum, "209682.134972197165534775309".parse().unwrap());
    }
}
