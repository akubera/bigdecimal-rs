// \file src/builder.rs

//! Simple helper objects

#![allow(non_snake_case)]
use std::str::FromStr;
/*
use std::convert::TryFrom;
*/

use super::{BigDecimal, ParseBigDecimalError};
use context::{self, Context, RoundingMode};


/// Standard builder for bigdecimal
#[derive(Clone)]
pub struct BigDecimalBuilder {
    precision: u64,
    rounding: RoundingMode,
}

impl BigDecimalBuilder {
    pub fn new() -> BigDecimalBuilder {
        BigDecimalBuilder {
            precision: context::DEFAULT_PRECISION,
            rounding: context::DEFAULT_ROUNDING_MODE,
        }
    }

    pub fn Precision(&self, prec: u64) -> Self {
        let mut result = self.clone();
        result.precision = prec;
        return result;
    }
}

macro_rules! impl_common_methods {
    ($X:ty) => {
        pub fn Precision(&self, prec: u64) -> $X {
            let mut result = self.clone();
            result.builder.precision = prec;
            return result;
        }

        pub fn RoundingMode(&self, rm: RoundingMode) -> $X {
            let mut result = self.clone();
            result.builder.rounding = rm;
            return result;
        }
    }
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
#[derive(Clone)]
pub struct BigDecimalBuilderString {
    builder: BigDecimalBuilder,
    src: String,
}

// Build BigDecimal using integer as source
#[derive(Clone)]
pub struct BigDecimalBuilderInt {
    builder: BigDecimalBuilder,
    src: i64,
}

// Build BigDecimal using float as a source
#[derive(Clone)]
pub struct BigDecimalBuilderFloat {
    builder: BigDecimalBuilder,
    src: f64,
}


impl BigDecimalBuilderString {
    impl_common_methods!(BigDecimalBuilderString);
}

// trait BigDecimalBuilderTrait<T: Into<BigDecimal>> {
// }

impl BigDecimalBuilder {
    pub fn WithString(&self, src: &str) -> BigDecimalBuilderString {
        BigDecimalBuilderString {
            builder: self.clone(),
            src: src.into(),
        }
    }

    pub fn WithInt(&self, src: i64) -> BigDecimalBuilderInt {
        BigDecimalBuilderInt {
            builder: self.clone(),
            src: src,
        }
    }

    pub fn WithFloat(&self, src: f64) -> BigDecimalBuilderFloat {
        BigDecimalBuilderFloat {
            builder: self.clone(),
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

impl From<BigDecimalBuilderString> for BigDecimal {
    #[inline]
    fn from(obj: BigDecimalBuilderString) -> BigDecimal {
        let mut result = BigDecimal::from_str(&obj.src).unwrap();
        result.context = obj.builder.into();
        return result;
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
