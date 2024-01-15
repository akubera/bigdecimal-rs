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

    mod serde_serialize {
        use super::*;

        macro_rules! impl_case {
            ($name:ident : $input:literal => $output:literal) => {
                #[test]
                fn $name() {
                    let expected = format!("\"{}\"", $output);
                    let decimal: BigDecimal = $input.parse().unwrap();
                    let value = serde_json::to_string(&decimal).unwrap();
                    assert_eq!(expected, value);
                }
            }
        }

        impl_case!(case_1d0: "1.0" => "1.0");
        impl_case!(case_0d5: "0.5" => "0.5");
        impl_case!(case_50: "50" => "50");
        impl_case!(case_50000: "50000" => "50000");
        impl_case!(case_1en3: "1e-3" => "0.001");
        impl_case!(case_1e12: "1e12" => "1000000000000");
        impl_case!(case_d25: ".25" => "0.25");
        impl_case!(case_12d34e1: "12.34e1" => "123.4");
        impl_case!(case_40d0010: "40.0010" => "40.0010");
    }

    mod serde_deserialize_str {
        use super::*;

        macro_rules! impl_case {
            ($name:ident : $input:literal => $output:literal) => {
                #[test]
                fn $name() {
                    let expected: BigDecimal = $output.parse().unwrap();

                    let s = $input;
                    let value: BigDecimal = serde_json::from_str(&format!("\"{}\"", s)).unwrap();
                    assert_eq!(expected, value);
                }
            }
        }

        impl_case!(case_1d0: "1.0" => "1.0");
        impl_case!(case_0d5: "0.5" => "0.5");
        impl_case!(case_50: "50" => "50");
        impl_case!(case_50000: "50000" => "50000");
        impl_case!(case_1en3: "1e-3" => "0.001");
        impl_case!(case_1e12: "1e12" => "1000000000000");
        impl_case!(case_d25: ".25" => "0.25");
        impl_case!(case_12d34e1: "12.34e1" => "123.4");
        impl_case!(case_40d0010: "40.0010" => "40.0010");
    }


    #[cfg(not(feature = "string-only"))]
    mod serde_deserialize_int {
        use super::*;

        macro_rules! impl_case {
            (-$input:literal) => {
                paste! { impl_case!([< case_n $input >] : -$input); }
            };
            ($input:literal) => {
                paste! { impl_case!([< case_ $input >] : $input); }
            };
            ($name:ident : $input:literal) => {
                #[test]
                fn $name() {
                    let n = $input;
                    let expected = BigDecimal::from_i64(n).unwrap();
                    let value: BigDecimal = serde_json::from_str(&serde_json::to_string(&n).unwrap()).unwrap();
                    assert_eq!(expected, value);
                }
            }
        }

        impl_case!(0);
        impl_case!(1);
        impl_case!(81516161);
        impl_case!(-370);
        impl_case!(-8);
        impl_case!(-99999999999);
    }


    #[cfg(not(feature = "string-only"))]
    mod serde_deserialize_f64 {
        use super::*;
        use stdlib::f64::consts;

        macro_rules! impl_case {
            ($name:ident : $input:expr) => {
                #[test]
                fn $name() {
                    let n = $input;
                    let expected = BigDecimal::from_f64(n).unwrap();
                    let value: BigDecimal = serde_json::from_str(&serde_json::to_string(&n).unwrap()).unwrap();
                    assert_eq!(expected, value);
                }
            }
        }

        impl_case!(case_1d0: 1.0);
        impl_case!(case_0d1: 0.1);
        impl_case!(case_0d5: 0.5);
        impl_case!(case_50d0: 50.0);
        impl_case!(case_pi: consts::PI);
        impl_case!(case_pi_times_100: consts::PI * 100.0);
        impl_case!(case_pi_times_30000: consts::PI * 30000.0);
    }

}
