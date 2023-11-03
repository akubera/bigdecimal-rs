//!
//! Support for serde implementations
//!
use crate::{BigDecimal, fmt, FromStr, TryFrom};
use serde::{de, ser};

#[allow(unused_imports)]
use num_traits::FromPrimitive;

/// Serialize/deserialize [`BigDecimal`] as arbitrary precision numbers in JSON using the `arbitrary_precision` feature within `serde_json`.
///
/// ```
/// # extern crate serde;
/// # use serde::{Serialize, Deserialize};
/// # use bigdecimal::BigDecimal;
/// # use std::str::FromStr;
///
/// #[derive(Serialize, Deserialize)]
/// pub struct ArbitraryExample {
///     #[serde(with = "bigdecimal::impl_serde::arbitrary_precision")]
///     value: BigDecimal,
/// }
///
/// let value = ArbitraryExample { value: BigDecimal::from_str("123.400").unwrap() };
/// assert_eq!(
///     &serde_json::to_string(&value).unwrap(),
///     r#"{"value":123.400}"#
/// );
/// ```
#[cfg(feature = "arbitrary-precision")]
pub mod arbitrary_precision {
    use crate::{BigDecimal, FromStr, stdlib::string::ToString};
    use serde::{Serialize, Deserialize};

    pub fn deserialize<'de, D>(deserializer: D) -> Result<BigDecimal, D::Error>
    where
        D: serde::de::Deserializer<'de>,
    {
        serde_json::Number::deserialize(deserializer)?.to_string().parse().map_err(serde::de::Error::custom)

    }

    pub fn serialize<S>(value: &BigDecimal, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serde_json::Number::from_str(&value.to_string())
            .map_err(serde::ser::Error::custom)?
            .serialize(serializer)
    }
}

/// Serialize/deserialize [`Option<BigDecimal>`] as arbitrary precision numbers in JSON using the `arbitrary_precision` feature within `serde_json`.
///
/// ```
/// # extern crate serde;
/// # use serde::{Serialize, Deserialize};
/// # use bigdecimal::BigDecimal;
/// # use std::str::FromStr;
///
/// #[derive(Serialize, Deserialize)]
/// pub struct ArbitraryExample {
///     #[serde(with = "bigdecimal::impl_serde::arbitrary_precision_option")]
///     value: Option<BigDecimal>,
/// }
///
/// let value = ArbitraryExample { value: Some(BigDecimal::from_str("123.400").unwrap()) };
/// assert_eq!(
///     &serde_json::to_string(&value).unwrap(),
///     r#"{"value":123.400}"#
/// );
///
/// let value = ArbitraryExample { value: None };
/// assert_eq!(
///     &serde_json::to_string(&value).unwrap(),
///     r#"{"value":null}"#
/// );
/// ```
#[cfg(feature = "arbitrary-precision")]
pub mod arbitrary_precision_option {
    use crate::{BigDecimal, FromStr, stdlib::string::ToString};
    use serde::{Serialize, Deserialize};

    pub fn deserialize<'de, D>(deserializer: D) -> Result<Option<BigDecimal>, D::Error>
    where
        D: serde::de::Deserializer<'de>,
    {
        Option::<serde_json::Number>::deserialize(deserializer)?.map(|num| num.to_string().parse().map_err(serde::de::Error::custom)).transpose()

    }

    pub fn serialize<S>(value: &Option<BigDecimal>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match *value {
            Some(ref decimal) => serde_json::Number::from_str(&decimal.to_string())
                .map_err(serde::ser::Error::custom)?
                .serialize(serializer),
            None => serializer.serialize_none(),
        }
    }
}

impl ser::Serialize for BigDecimal {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ser::Serializer,
    {
        serializer.collect_str(&self)
    }
}

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
extern crate serde_json;
    use crate::{BigDecimal, FromStr};
    use serde::Deserialize;

    #[test]
    fn test_serde_serialize() {
        let vals = vec![
            ("1.0", "1.0"),
            ("0.5", "0.5"),
            ("50", "50"),
            ("50000", "50000"),
            ("1e-3", "0.001"),
            ("1e12", "1000000000000"),
            ("0.25", "0.25"),
            ("12.34", "12.34"),
            ("0.15625", "0.15625"),
            ("0.3333333333333333", "0.3333333333333333"),
            ("3.141592653589793", "3.141592653589793"),
            ("94247.77960769380", "94247.77960769380"),
            ("10.99", "10.99"),
            ("12.0010", "12.0010"),
        ];
        for (s, v) in vals {
            let expected = format!("\"{}\"", v);
            let value = serde_json::to_string(&BigDecimal::from_str(s).unwrap()).unwrap();
            assert_eq!(expected, value);
        }
    }

    #[test]
    fn test_serde_deserialize_str() {
        let vals = vec![
            ("1.0", "1.0"),
            ("0.5", "0.5"),
            ("50", "50"),
            ("50000", "50000"),
            ("1e-3", "0.001"),
            ("1e12", "1000000000000"),
            ("0.25", "0.25"),
            ("12.34", "12.34"),
            ("0.15625", "0.15625"),
            ("0.3333333333333333", "0.3333333333333333"),
            ("3.141592653589793", "3.141592653589793"),
            ("94247.77960769380", "94247.77960769380"),
            ("10.99", "10.99"),
            ("12.0010", "12.0010"),
        ];
        for (s, v) in vals {
            let expected = BigDecimal::from_str(v).unwrap();
            let value: BigDecimal = serde_json::from_str(&format!("\"{}\"", s)).unwrap();
            assert_eq!(expected, value);
        }
    }

    #[test]
    #[cfg(not(feature = "string-only"))]
    fn test_serde_deserialize_int() {
        use crate::FromPrimitive;

        let vals = vec![0, 1, 81516161, -370, -8, -99999999999];
        for n in vals {
            let expected = BigDecimal::from_i64(n).unwrap();
            let value: BigDecimal = serde_json::from_str(&serde_json::to_string(&n).unwrap()).unwrap();
            assert_eq!(expected, value);
        }
    }

    #[test]
    #[cfg(not(any(feature = "string-only", feature = "arbitrary-precision")))]
    fn test_serde_deserialize_f64() {
        use crate::{FromPrimitive,stdlib::f64::consts::PI};

        let vals = vec![
            1.0,
            0.5,
            0.25,
            50.0,
            50000.,
            0.001,
            12.34,
            5.0 * 0.03125,
            PI,
            PI * 10000.0,
            PI * 30000.0,
        ];
        for n in vals {
            let expected = BigDecimal::from_f64(n).unwrap();
            let value: BigDecimal = serde_json::from_str(&serde_json::to_string(&n).unwrap()).unwrap();
            assert_eq!(expected, value);
        }
    }

    /// Not a great test but demonstrates why `arbitrary-precision` exists.
    #[test]
    #[cfg(not(feature = "arbitrary-precision"))]
    fn test_normal_precision() {
        #[derive(Deserialize, Debug, PartialEq, Eq)]
        struct ViaF64 {
            n: BigDecimal,
        }

        let json = r#"{ "n": 0.1 }"#;
        let expected = BigDecimal::from_str("0.1").expect("should parse 0.1 as BigDecimal");
        let deser: ViaF64 = serde_json::from_str(json).expect("should parse JSON");

        // 0.1 is directly representable in `BigDecimal`, but not `f64` so the default deserialization fails.
        assert_ne!(expected, deser.n);
    }

    #[test]
    #[cfg(feature = "arbitrary-precision")]
    fn test_arbitrary_precision() {
        use serde::Deserialize;

        #[derive(Deserialize, Debug, PartialEq, Eq)]
        struct ArbitraryPrec {
            #[serde(with = "crate::impl_serde::arbitrary_precision")]
            n: BigDecimal
        }

        let json = r#"{ "n": 0.1 }"#;
        let expected = BigDecimal::from_str("0.1").expect("should parse 0.1 as BigDecimal");
        let deser: ArbitraryPrec = serde_json::from_str(json).expect("should parse JSON");

        assert_eq!(expected, deser.n);
    }
}
