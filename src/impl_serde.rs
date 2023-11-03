//!
//! Support for serde implementations
//!
use crate::*;
use serde::{de, ser};

#[allow(unused_imports)]
use num_traits::FromPrimitive;

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
    use super::*;

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
        let vals = vec![0, 1, 81516161, -370, -8, -99999999999];
        for n in vals {
            let expected = BigDecimal::from_i64(n).unwrap();
            let value: BigDecimal = serde_json::from_str(&serde_json::to_string(&n).unwrap()).unwrap();
            assert_eq!(expected, value);
        }
    }

    #[test]
    #[cfg(not(feature = "string-only"))]
    fn test_serde_deserialize_f64() {
        let vals = vec![
            1.0,
            0.5,
            0.25,
            50.0,
            50000.,
            0.001,
            12.34,
            5.0 * 0.03125,
            stdlib::f64::consts::PI,
            stdlib::f64::consts::PI * 10000.0,
            stdlib::f64::consts::PI * 30000.0,
        ];
        for n in vals {
            let expected = BigDecimal::from_f64(n).unwrap();
            let value: BigDecimal = serde_json::from_str(&serde_json::to_string(&n).unwrap()).unwrap();
            assert_eq!(expected, value);
        }
    }
}
