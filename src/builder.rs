// \file src/builder.rs

//! Simple helper objects

#![allow(non_snake_case)]
use std::str::FromStr;
/*
use std::convert::TryFrom;
*/

use super::{BigDecimal, ParseBigDecimalError};
use super::context::{Context, RoundingMode};


/// Standard builder for bigdecimal
pub struct BigDecimalBuilder {
    precision: u64,
    rounding: RoundingMode,
}

impl Into<Context> for BigDecimalBuilder {
    fn into(self) -> Context {
        Context {
            precision: self.precision,
            rounding_mode: self.rounding,
        }
    }
}

/// Build BigDecimal using String as a source
pub struct BigDecimalBuilderString {
    builder: BigDecimalBuilder,
    src: String,
}

impl BigDecimalBuilderString {}

// Build BigDecimal using integer as source
pub struct BigDecimalBuilderInt {
    builder: BigDecimalBuilder,
    src: i64,
}

// Build BigDecimal using float as a source
pub struct BigDecimalBuilderFloat {
    builder: BigDecimalBuilder,
    src: f64,
}


// trait BigDecimalBuilderTrait<T: Into<BigDecimal>> {
// }

impl BigDecimalBuilder {
    pub fn WithString(self, src: String) -> BigDecimalBuilderString {
        BigDecimalBuilderString {
            builder: self,
            src: src,
        }
    }

    pub fn WithInt(self, src: i64) -> BigDecimalBuilderInt {
        BigDecimalBuilderInt {
            builder: self,
            src: src,
        }
    }

    pub fn WithFloat(self, src: f64) -> BigDecimalBuilderFloat {
        BigDecimalBuilderFloat {
            builder: self,
            src: src,
        }
    }
}

/*
impl TryFrom<BigDecimalBuilderString> for BigDecimal {
    type Error = ParseBigDecimalError;

    #[inline]
    fn try_from(obj: BigDecimalBuilderString) -> Result<BigDecimal, ParseBigDecimalError> {
        let ctx: Context = obj.builder.into();
        BigDecimal::from_str(&obj.src).map(|mut result| {
            result.context = ctx;
            result
        })
    }
}
*/

impl From<BigDecimalBuilderString> for Result<BigDecimal, ParseBigDecimalError> {
    #[inline]
    fn from(obj: BigDecimalBuilderString) -> Result<BigDecimal, ParseBigDecimalError> {
        let ctx: Context = obj.builder.into();
        BigDecimal::from_str(&obj.src).map(|mut result| {
            result.context = ctx;
            result
        })
    }
}

impl From<BigDecimalBuilderInt> for BigDecimal {
    #[inline]
    fn from(obj: BigDecimalBuilderInt) -> BigDecimal {
        let mut result: BigDecimal = obj.src.into();
        result.context = obj.builder.into();
        return result;
    }
}

impl From<BigDecimalBuilderFloat> for BigDecimal {
    #[inline]
    fn from(obj: BigDecimalBuilderFloat) -> BigDecimal {
        let mut result: BigDecimal = obj.src.into();
        result.context = obj.builder.into();
        return result;
    }
}
