//! Code for implementing From/To BigDecimals

use super::BigDecimal;


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
