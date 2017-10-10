//! 64-bit decimal number
//!
//! For more information, check dec64.com
//!

use std::num::FpCategory;
// use num::traits::Float as FloatTrait;
use num::traits::{Zero, One};
use std::ops::{Add, Mul};


pub mod consts {
    use super::Dec64;
    /// π
    pub const PI: Dec64 = Dec64 { bits: 0x6F9C9E6576434C_F0 };
    /// -π
    pub const NPI: Dec64 = Dec64 { bits: 0x9063619A89BCB4_F0 };
    /// 2π
    pub const TWO_PI: Dec64 = Dec64 { bits: 0x165286144ADA42_F1 };

    /// π/2
    pub const FRAC_PI_2: Dec64 = Dec64 { bits: 0x37CE4F32BB21A6_F0 };
    /// π/4
    pub const FRAC_PI_4: Dec64 = Dec64 { bits: 0x37CE4F32BB21A600 / 2 + 0xF0 };

    /// -π/2
    pub const NEG_FRAC_PI_2: Dec64 = Dec64 { bits: 0xC831B0CD44DE59_F0 };

    /// Euler's number (e ~ 2.718)
    pub const E: Dec64 = Dec64 { bits: 0x6092A113D8D574_F0 };

    /// Smallest possible positive number
    pub const EPSILON: Dec64 = Dec64 { bits: 0x01_81};

    /// this number is *not* a number
    pub const NAN: Dec64 = Dec64 { bits: 0x00_80};

    /// largest represented number
    pub const MAX: Dec64 = Dec64 { bits: 36028797018963967 << 8 | 127 };
    /// smallest represented number (negative)
    pub const MIN: Dec64 = Dec64 { bits: (-36028797018963968i64 << 8) as u64 | 127 };
}

#[inline]
fn decimal_digits(n: f64) -> u16
{
  (n.abs().log10().floor() + 1.0) as u16
}


/// 64-bit decimal number.
///
///
/// <pre>
/// [-------- coefficient --------|  exponent  ]
/// 63                            7            0
/// </pre>
///
/// <math xmlns="http://www.w3.org/1998/Math/MathML">
///   <mi>value</mi>
///   <mo>=</mo>
///   <mi>coefficient</mi>
///   <mo>×</mo>
///   <msup>
///     <mn>10</mn>
///     <mi>exponent</mi>
///   </msup>
/// </math>
///
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Dec64 {
    bits: u64,
}


impl Dec64 {
    /// construct with coefficeint and exponent
    pub fn from_raw_parts(coefficient: i64, exponent: i8) -> Dec64 {
      let coefficient = (coefficient << 8) as u64;
      let exponent = exponent as u64 & 0xFF;
      Dec64 { bits: coefficient | exponent }
    }

    pub fn is_nan(&self) -> bool {
        self.bits as i8 == -128
    }

    pub fn classify(&self) -> FpCategory {
        if self.bits == 0x80 {
            FpCategory::Nan
        } else {
            FpCategory::Normal
        }
    }

    pub fn signum(&self) -> Dec64 {
        if self.is_nan() {
            Dec64 { bits: self.bits }
        } else if self.bits & (1 << 63) == 0 {
            Dec64::from_raw_parts(1, 0)
        } else {
            Dec64::from_raw_parts(-1, 0)
        }
    }

}

impl Zero for Dec64 {
    #[inline]
    fn zero() -> Self {
        Dec64 { bits : 0x0 }
    }

    #[inline]
    fn is_zero(&self) -> bool {
        (self.bits & !0x7F) == 0
    }
}

impl One for Dec64 {
    fn one() -> Self {
        Dec64 { bits : 1 << 8 }
    }
}


impl Default for Dec64 {
    fn default() -> Self {
        Self::zero()
    }
}

macro_rules! impl_tofrom_int {
  ($( $int_t:ty ),*) => ($(
    impl From<$int_t> for Dec64 {
      fn from(num: $int_t) -> Self {
        Dec64 {
          bits: (num as u64) << 8
        }
      }
    }

    impl From<Dec64> for $int_t {
      fn from(dec: Dec64) -> $int_t {
        let exponent = dec.bits as i8;

        let coefficient = dec.bits >> 8 as i64;

        return if exponent <= 0 {
            coefficient
           } else {
            coefficient * 10u64.pow(exponent as u32)
        } as $int_t
      }
    }
)*)
}

impl_tofrom_int!(i8, i16, i32, i64, isize, u8, u16, u32, u64, usize);


impl From<f64> for Dec64 {
    fn from(float: f64) -> Dec64 {
      // use std;
        let _dec_digits = decimal_digits(float);
        let float_bits = float.to_bits();

        // let z = float_bits >> (::std::f64::MANTISSA_DIGITS - 1)  & 0x7FF;
        let _fraction = float_bits & !(0xFFFu64);
        let _exponent = (float_bits >> 52) & 0x7FF;
        let _sign_bit = float_bits >> 63;

        // grisu2::
        /*
        if float < 0.0 {
        let (coefficient, exponent) = grisu2::convert(-float);

            Dec64::from_raw_parts(-(coefficient as i64), exponent as i8)
        } else {
            let (coefficient, exponent) = grisu2::convert(float);

            Dec64::from_raw_parts(coefficient as i64, exponent as i8)
        }
        */
        Dec64::from_raw_parts(0, 0)
    }
}


// impl From<Dec64> for f64 {
//     fn from(dec: Dec64) -> f64 {
//         (dec.coefficient() as f64) * exponent_to_power_f64(dec.exponent())
//     }
// }

// impl_tofrom_float!(f32, f64);

impl Add<Dec64> for Dec64 {
    type Output = Dec64;

    fn add(self, rhs: Dec64) -> Self::Output {
        if self.bits & 0xFF == rhs.bits & 0xFF {
            Dec64 { bits: self.bits | rhs.bits & !0xFF }
        } else {
            Dec64::default()
        }
    }
}

impl Mul<Dec64> for Dec64 {
    type Output = Dec64;

    fn mul(self, _rhs: Dec64) -> Self::Output {
        Dec64::default()
    }
}


#[cfg(test)]
mod test {
  use super::*;

  #[cfg_attr(rustfmt, rustfmt_skip)]
  #[test]
  fn test_constants() {
    let vals = vec![
      (consts::E, (27182818284590452, -16)),
      (consts::NPI, (-31415926535897932, -16)),
      //  negative_maxint = dec64_new(-36028797018963968, 0);
      //   negative_maxnum = dec64_new(-36028797018963968, 127);

    ];

    for (check_const, (c, e)) in vals {
      let expected_dec = Dec64::from_raw_parts(c, e);
      assert_eq!(check_const, expected_dec);
    }
  }

  #[cfg_attr(rustfmt, rustfmt_skip)]
  #[test]
  fn test_constructor() {
    let vals = vec![
      ((2, 3), 200., 0b00000000_00000010_00000011),
      ((5, -1), 0.5, 0x5FF),
    ];

    for ((c, e), ex_float, expected_bits) in vals {
      let dec = Dec64::from_raw_parts(c, e);
      assert_eq!(dec.bits, expected_bits);
      // assert!((ex_float - dec.into::<f64>()).abs() < 1e-4);
    }
  }



}
