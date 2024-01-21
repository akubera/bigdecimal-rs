//!
//! Support for serde implementations
//!
use crate::*;
use serde::{de, ser};


impl ser::Serialize for BigDecimal {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ser::Serializer,
    {
        serializer.collect_str(&self)
    }
}

/// Used by SerDe to construct a BigDecimal
struct BigDecimalVisitor;

impl<'de> de::Visitor<'de> for BigDecimalVisitor {
    type Value = BigDecimal;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "a number or formatted decimal string")
    }

    fn visit_str<E>(self, value: &str) -> Result<BigDecimal, E>
    where
        E: de::Error,
    {
        BigDecimal::from_str(value).map_err(|err| E::custom(format!("{}", err)))
    }

    fn visit_u64<E>(self, value: u64) -> Result<BigDecimal, E>
    where
        E: de::Error,
    {
        Ok(BigDecimal::from(value))
    }

    fn visit_i64<E>(self, value: i64) -> Result<BigDecimal, E>
    where
        E: de::Error,
    {
        Ok(BigDecimal::from(value))
    }

    fn visit_f64<E>(self, value: f64) -> Result<BigDecimal, E>
    where
        E: de::Error,
    {
        BigDecimal::try_from(value).map_err(|err| E::custom(format!("{}", err)))
    }
}

#[cfg(not(feature = "string-only"))]
impl<'de> de::Deserialize<'de> for BigDecimal {
    fn deserialize<D>(d: D) -> Result<Self, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        d.deserialize_any(BigDecimalVisitor)
    }
}

#[cfg(feature = "string-only")]
impl<'de> de::Deserialize<'de> for BigDecimal {
    fn deserialize<D>(d: D) -> Result<Self, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        d.deserialize_str(BigDecimalVisitor)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use paste::paste;

    use serde_test::{
        Token, assert_tokens, assert_de_tokens, assert_de_tokens_error
    };

    mod serde_serialize_deserialize_str {
        use super::*;

        macro_rules! impl_case {
            ($name:ident : $input:literal => $output:literal) => {
                #[test]
                fn $name() {
                    let expected = Token::Str($output);
                    let decimal: BigDecimal = $input.parse().unwrap();
                    assert_tokens(&decimal, &[expected]);
                }
            }
        }

        impl_case!(case_1d0: "1.0" => "1.0");
        impl_case!(case_0d5: "0.5" => "0.5");
        impl_case!(case_50: "50" => "50");
        impl_case!(case_50000: "50000" => "50000");
        impl_case!(case_1en3: "1e-3" => "0.001");
        impl_case!(case_10e11: "10e11" => "1.0E+12");
        impl_case!(case_d25: ".25" => "0.25");
        impl_case!(case_12d34e1: "12.34e1" => "123.4");
        impl_case!(case_40d0010: "40.0010" => "40.0010");
    }

    #[cfg(not(feature = "string-only"))]
    mod serde_deserialize_int {
        use super::*;

        macro_rules! impl_case {
            ( $( $ttype:ident ),+ : -$input:literal ) => {
                $( paste! { impl_case!([< case_n $input _ $ttype:lower >] : $ttype : -$input); } )*
            };
            ( $( $ttype:ident ),+ : $input:literal ) => {
                $( paste! { impl_case!([< case_ $input _ $ttype:lower >] : $ttype : $input); } )*
            };
            ($name:ident : $type:ident : $input:literal) => {
                #[test]
                fn $name() {
                    let expected = BigDecimal::from($input);
                    let token = Token::$type($input);
                    assert_de_tokens(&expected, &[token]);
                }
            };
        }

        impl_case!(I8, I16, I32, I64, U8, U16, U32, U64 : 0);
        impl_case!(I8, I16, I32, I64, U8, U16, U32, U64 : 1);
        impl_case!(I8, I16, I32, I64 : -1);
        impl_case!(I64: -99999999999i64);
        impl_case!(I64: -9_223_372_036_854_775_808i64);
    }

    #[cfg(not(feature = "string-only"))]
    mod serde_deserialize_float {
        use super::*;

        macro_rules! impl_case {
            ( $name:ident : $input:literal => $ttype:ident : $expected:literal ) => {
                paste! {
                    #[test]
                    fn [< $name _ $ttype:lower >]() {
                        let expected: BigDecimal = $expected.parse().unwrap();
                        let token = Token::$ttype($input);
                        assert_de_tokens(&expected, &[token]);
                    }
                }
            };
            ( $name:ident : $input:literal => $( $ttype:ident : $expected:literal )+ ) => {
                $( impl_case!($name : $input => $ttype : $expected); )*
            };
            ( $name:ident : $input:literal => $( $ttype:ident ),+ : $expected:literal ) => {
                $( impl_case!($name : $input => $ttype : $expected); )*
            };
        }

        impl_case!(case_1d0 : 1.0 => F32, F64 : "1");
        impl_case!(case_1d1 : 1.1 => F32 : "1.10000002384185791015625"
                                     F64 : "1.100000000000000088817841970012523233890533447265625");

        impl_case!(case_0d001834988943300:
            0.001834988943300 => F32 : "0.001834988943301141262054443359375"
                                 F64 : "0.00183498894330000003084768511740776375518180429935455322265625");

        impl_case!(case_n869651d9131236838:
            -869651.9131236838 => F32 : "-869651.9375"
                                  F64 : "-869651.91312368377111852169036865234375");

        impl_case!(case_n1en20:
            -1e-20 => F32 : "-9.999999682655225388967887463487205224055287544615566730499267578125E-21"
                      F64 : "-999999999999999945153271454209571651729503702787392447107715776066783064379706047475337982177734375e-119");
    }

    #[cfg(not(feature = "string-only"))]
    mod serde_deserialize_nan {
        use super::*;

        #[test]
        fn case_f32() {
            let tokens = [ Token::F32(f32::NAN) ];
            assert_de_tokens_error::<BigDecimal>(&tokens, "NAN");
        }

        #[test]
        fn case_f64() {
            let tokens = [ Token::F64(f64::NAN) ];
            assert_de_tokens_error::<BigDecimal>(&tokens, "NAN");
        }
    }
}
