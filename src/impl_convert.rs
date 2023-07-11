//! Code for implementing From/To BigDecimals

use crate::BigDecimal;
use crate::stdlib::convert::TryFrom;


macro_rules! impl_from_int_primitive {
    ($t:ty) => {
        impl From<$t> for BigDecimal {
            fn from(n: $t) -> Self {
                BigDecimal {
                    int_val: n.into(),
                    scale: 0,
                }
            }
        }

        impl From<&$t> for BigDecimal {
            fn from(n: &$t) -> Self {
                BigDecimal {
                    int_val: (*n).into(),
                    scale: 0,
                }
            }
        }
    };
}

impl_from_int_primitive!(u8);
impl_from_int_primitive!(u16);
impl_from_int_primitive!(u32);
impl_from_int_primitive!(u64);
impl_from_int_primitive!(u128);
impl_from_int_primitive!(i8);
impl_from_int_primitive!(i16);
impl_from_int_primitive!(i32);
impl_from_int_primitive!(i64);
impl_from_int_primitive!(i128);


impl TryFrom<f32> for BigDecimal {
    type Error = super::ParseBigDecimalError;

    #[inline]
    fn try_from(n: f32) -> Result<Self, Self::Error> {
        crate::parsing::try_parse_from_f32(n)
    }
}

impl TryFrom<f64> for BigDecimal {
    type Error = super::ParseBigDecimalError;

    #[inline]
    fn try_from(n: f64) -> Result<Self, Self::Error> {
        crate::parsing::try_parse_from_f64(n)
    }
}
