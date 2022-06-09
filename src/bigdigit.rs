use std::mem::swap;

use crate::BigDecimal;

use arithmetic::addition::add_digit_vecs_into;
use arithmetic::multiplication::multiply_digit_vecs_into;

// use crate::arithmetic::multiplication::multiply_digit_vecs;

/// The BigDigit used in BigDecimal
///
/// These are distinct from the BigDigits in BigIntger

// pub type BigDigitBase = u8;
// pub type BigDigitBaseDouble = u16;
// pub type BigDigitBaseSignedDouble = i16;
// pub const MAX_DIGITS_PER_BIGDIGIT: usize = 2;
// pub const BIG_DIGIT_RADIX: BigDigitBaseDouble = 100;

pub type BigDigitBase = u32;
pub type BigDigitBaseDouble = u64;
pub type BigDigitBaseSignedDouble = i64;
pub const BIG_DIGIT_RADIX: BigDigitBaseDouble = 1000000000;
pub const BIG_DIGIT_RADIX_I64: i64 = BIG_DIGIT_RADIX as i64;
pub const MAX_DIGITS_PER_BIGDIGIT: usize = 9;

pub const BIG_DIGIT_BITS: usize = std::mem::size_of::<BigDigitBase>() * 8;
pub(crate) const RADIX_IS_POWER_OF_TEN: bool = is_power_of_ten(BIG_DIGIT_RADIX);
pub(crate) const RADIX_POWER_OF_TEN: Option<usize> = power_of_ten(BIG_DIGIT_RADIX);

// Vector of BigDigits
pub type BigDigitVec = Vec<BigDigitBase>;

macro_rules! bigdigit_vec {
    [ ] => {
        vec![]
    };
    [ capacity = $capacity:expr ] => {
        BigDigitVec::with_capacity($capacity as usize)
    };
    [ $($e:expr),* ] => {
        vec![$($e),*]
    };
    [ $e:tt ] => {
        vec![$e]
    };
}


impl From<&BigDecimal> for BigDigitVec {
    fn from(obj: &BigDecimal) -> BigDigitVec {
        let mut result = bigdigit_vec![];
        return result;
    }
}


/// returns true if number is a power of ten (10^x)
#[cfg(rustc_1_46)]
const fn is_power_of_ten(n: BigDigitBaseDouble) -> bool {
    match n % 10 {
        1 if n == 1 => true,
        0 => is_power_of_ten(n / 10),
        _ => false,
    }
}

#[cfg(not(rustc_1_46))]
const fn is_power_of_ten(n: BigDigitBaseDouble) -> bool {
    return true;
}

#[cfg(rustc_1_46)]
const fn power_of_ten(n: BigDigitBaseDouble) -> Option<usize> {
    match n {
        1 => Some(0),
        0..=9 => None,
        _ if n % 10 != 0 => None,
        _ => match power_of_ten(n / 10) {
            None => None,
            Some(p) => Some(1 + p),
        },
    }
}

#[cfg(not(rustc_1_46))]
const fn power_of_ten(n: BigDigitBaseDouble) -> Option<usize> {
    Some(MAX_DIGITS_PER_BIGDIGIT)
}

#[cfg(rustc_1_46)]
#[cfg(test)]
mod test_power_of_ten {
    use super::*;

    macro_rules! impl_case {
        ($n:literal, $expected:expr) => {
            paste! {
                #[test]
                fn [< case_ $n >]() {
                    assert_eq!(power_of_ten($n), $expected);
                }
            }
        };
    }

    impl_case!(1, Some(0));
    impl_case!(100, Some(2));
    impl_case!(10000, Some(4));

    impl_case!(101, None);
    impl_case!(200, None);
}

#[inline]
pub(crate) fn to_power_of_ten(n: u32) -> BigDigitBase {
    (10 as BigDigitBase).pow(n)
}

/// to bigdigit vec
pub(crate) fn to_bigdigit_vec<T: Iterator<Item = u64>>(digits: T, radix: u128) -> Vec<BigDigitBase> {
    let mut digits = digits.peekable();

    let mut result = convert_to_bigdigit_vec(digits.next().unwrap_or(0) as u128);
    if digits.peek().is_none() {
        return result;
    }

    let radix_factor = convert_to_bigdigit_vec(radix);
    let mut radix_shift_vec = vec![1];
    let mut digit_vec = Vec::with_capacity(32);
    let mut tmp = Vec::with_capacity(32);
    for digit in digits {
        multiply_digit_vecs_into(&radix_shift_vec, &radix_factor, &mut tmp);
        swap(&mut radix_shift_vec, &mut tmp);

        write_int_into_vec(digit as u128, &mut digit_vec);
        multiply_digit_vecs_into(&digit_vec, &radix_shift_vec, &mut tmp);
        swap(&mut digit_vec, &mut tmp);

        add_digit_vecs_into(&result, &digit_vec, &mut tmp);
        swap(&mut result, &mut tmp);
    }
    return result;
}

/// Trait for converting to Vector of BigDigits
pub trait IntoBigDigitVec {
    fn into(&self) -> Vec<BigDigitBase>;
}

impl IntoBigDigitVec for num_bigint::BigInt {
    fn into(&self) -> Vec<BigDigitBase> {
        to_bigdigit_vec(self.iter_u64_digits(), crate::MAX_BIG_DIGIT_BASE_DOUBLE)
    }
}

fn convert_to_bigdigit_vec(digit: u128) -> Vec<BigDigitBase> {
    if digit == 0 {
        return vec![0];
    }

    let mut result = vec![];
    write_int_into_vec(digit, &mut result);
    return result;
}

fn write_int_into_vec(mut digit: u128, result: &mut Vec<BigDigitBase>) {
    let radix = BIG_DIGIT_RADIX as u128;

    result.clear();

    if digit == 0 {
        result.push(0);
        return;
    }

    while digit != 0 {
        result.push((digit % radix) as BigDigitBase);
        digit = digit / radix;
    }
}

pub(crate) fn convert_to_base_u32_vec(decimal_digits: &[BigDigitBase]) -> Vec<u32> {
    let mut result = Vec::with_capacity(decimal_digits.len());

    // let radix = u32::max as BigDigitBaseDouble;
    let radix = 1u64 << 32;

    let mut base_digits = Vec::with_capacity(result.capacity());
    base_digits.push(1);
    result.push(0);

    for &value in decimal_digits.iter() {
        if value != 0 {
            do_mul_and_add_into!(
                value, &base_digits, result, radix; u32, u64
            );
        }
        let mut carry = 0;
        for digit in base_digits.iter_mut() {
            let tmp = *digit as BigDigitBaseDouble * BIG_DIGIT_RADIX + carry;
            *digit = (tmp % radix) as u32;
            carry = tmp / radix;
        }

        while carry != 0 {
            base_digits.push((carry % radix) as u32);
            carry /= radix;
        }
    }

    return result;
}

pub(crate) fn convert_to_base_u32_vec_into<'a, T: Iterator<Item = &'a u64>>(
    // mut decimal_digits: &mut IntoIterator<Item = T>,
    // decimal_digits: &Vec<u128>,
    decimal_digits: T,
    result: &mut Vec<u32>,
) {
    let radix = u32::max as BigDigitBaseDouble;

    let mut base_digits = Vec::with_capacity(result.capacity());
    base_digits.push(1);
    result.push(0);

    for &value in decimal_digits {
        // let value: u128 = val.into();
        if value != 0 {
            do_mul_and_add_into!(
                value, &base_digits, result, 1u64<<32; u32, u64
            );
        }
        let mut carry = 0;
        for digit in base_digits.iter_mut() {
            let tmp = *digit as BigDigitBaseDouble * BIG_DIGIT_RADIX + carry;
            *digit = (tmp % radix) as u32;
            carry = tmp / radix;
        }

        while carry != 0 {
            base_digits.push((carry % radix) as u32);
            carry /= radix;
        }
    }
}

/// Convert floating point to an approximate pair (n, scale)
/// where `x ~= n * 10^scale`
#[inline(always)]
pub(crate) fn to_single_bigdigit(x: f64) -> (BigDigitBase, i32) {
    // if x == 0.0 {
    if !x.is_normal() {
        return (0, 0);
    }

    debug_assert!(x > 0.0);

    let f = x.fract();
    let x_log = x.abs().log10().ceil() as i32;
    if 0 <= x_log && x_log < MAX_DIGITS_PER_BIGDIGIT as i32 && f == 0.0 {
        return (x as BigDigitBase, 0);
    }

    let mut scale = x_log - MAX_DIGITS_PER_BIGDIGIT as i32;
    let mut value = (x * 10f64.powi(-scale)).round() as BigDigitBase;

    while value % 10 == 0 {
        value /= 10;
        scale += 1;
    }
    return (value, scale);

    if x_log < MAX_DIGITS_PER_BIGDIGIT as i32 {
        let scale = x_log - MAX_DIGITS_PER_BIGDIGIT as i32;
        let value = x * 10f64.powi(-scale);
        (value as BigDigitBase, scale)
    } else {
        let scale = x_log - MAX_DIGITS_PER_BIGDIGIT as i32;
        let value = (x * 10.0_f64.powi(-scale)).round() as BigDigitBase;
        // debug_assert!(value < BIG_DIGIT_RADIX as BigDigitBase);
        (value.min(BIG_DIGIT_RADIX as BigDigitBase - 1), scale)
    }
}

#[cfg(test)]
mod test_to_single_bigdigit {
    use super::*;

    macro_rules! impl_test {
        ($name:literal, $x:literal; $expect:expr, $scale:literal ) => {
            paste! {
                #[test]
                fn [< case_ $name >]() {
                    let (digit, scale) = to_single_bigdigit($x);
                    assert_eq!(digit, $expect);
                    assert_eq!(scale, $scale);
                }
            }
        };
    }

    impl_test!(14_0, 14.0; 14, 0);
    impl_test!(14_5, 14.5; 145, -1);

}

/// Count the number of digits, in slice of bigdigits
///
/// Assumes little endian notation base $10^9$ bigdigits
///
pub(crate) fn count_digits(v: &[BigDigitBase]) -> usize
{
    debug_assert!(v.len() > 0);
    let digits_in_int = |n: BigDigitBase| {
        if n < 10 {
            1
        } else if n < 100 {
            2
        } else if n < 1000 {
            3
        } else if n < 10000 {
            4
        } else if n < 100000 {
            5
        } else if n < 1000000 {
            6
        } else if n < 10000000 {
            7
        } else if n < 100000000 {
            8
        } else if n < 1000000000 {
            9
        } else {
            unreachable!()
        }
    };

    MAX_DIGITS_PER_BIGDIGIT * (v.len() - 1) + digits_in_int(v[v.len() - 1])
}

#[cfg(test)]
mod test_count_digits {
    use super::*;

    macro_rules! test_case {
        ( $n:literal; $expected:literal ) => {
            test_case!((NAME = $n); [$n]; $expected);
        };
        ( [$($n:literal),*] ; $expected:literal ) => {
            test_case!( (NAME $($n)* = ); [$($n),*]; $expected );
        };
        ( (NAME $head:literal $($rest:literal)* = $($name:literal)*); [$($n:literal),*]; $expected:literal ) => {
            test_case!( (NAME $($rest)* = $head $($name)*); [$($n),*]; $expected );
        };
        ( (NAME = $($name:literal)*); [$($n:literal),*]; $expected:literal ) => {
            paste! {
                #[test]
                fn [< case_ $($name)* >]() {{
                    let count = count_digits(&[$($n),*]);
                    assert_eq!(count, $expected);
                }}
            }
        };
    }

    test_case!(0; 1);
    test_case!(1; 1);
    test_case!(2; 1);
    test_case!(9; 1);
    test_case!(10; 2);
    test_case!(99; 2);
    test_case!(199; 3);
    test_case!(301548653; 9);
    test_case!([384309465, 765728666, 201]; 21);
    test_case!(
        [70592446, 177162782, 274783218, 24352950, 191976889,
            216917990, 28818228, 5216000]; 70);
}


#[inline]
pub(crate) fn decimal_shift_and_mask(n: usize) -> (BigDigitBase, BigDigitBase)
{
    let R = BIG_DIGIT_RADIX as BigDigitBase;

    let shift = to_power_of_ten(n as BigDigitBase);
    let mask = R / shift;
    return (shift, mask);
}
