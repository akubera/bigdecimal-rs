use num_bigint::Sign;
use num_integer::div_rem;

use crate::bigdigit::{
    BIG_DIGIT_RADIX, BigDigitBase, BigDigitBaseDouble, BigDigitVec, MAX_DIGITS_PER_BIGDIGIT
};
use crate::{context::RoundingInfo, RoundingMode};

pub(crate) fn round(
    digit_vec: &[BigDigitBase],
    scale: i64,
    new_scale: i64,
    rounding_mode: RoundingMode,
) -> BigDigitVec {
    // index of digit from 'right' of the decimal point
    //
    // |------[decimal_digit_count = 40]-------|
    //    |----------[scale = 38]--------------|
    // 63.94267984578837493714331685623619705438
    //        ^------[rounding_point = 33]-----|  (if n_digits = 5)
    //  ^------------[rounding_point = 38]-----|  (if n_digits = 0)
    //                  [rounding_point = 0]---^  (if n_digits = 38)
    //
    let rounding_point = scale - new_scale;
    dbg!(rounding_point);

    // no rounding to do, just clone the decimal
    // if rounding_point == 0 {
    //     return decimal.clone();
    // }

    // we are extending precision of the decimal (to the right),
    // increase bigint and set 'ndigits' as the scale
    if rounding_point < 0 {
        // TODO: check if precision should play a part here
        let trailing_zeros = (-rounding_point) as usize;

        let (zero_bigdigit_count, offset) = div_rem(trailing_zeros, MAX_DIGITS_PER_BIGDIGIT);

        let mut new_digits = Vec::with_capacity(digit_vec.len() + 1 + zero_bigdigit_count);
        new_digits.resize(zero_bigdigit_count, 0);

        if offset == 0 {
            new_digits.extend_from_slice(&digit_vec);
        } else {
            let digit_splitter = ten_to_pow!(MAX_DIGITS_PER_BIGDIGIT - offset);
            let digit_shifter = ten_to_pow!(offset);

            new_digits.push(0);
            for (&digit, i) in digit_vec.iter().zip(new_digits.len() - 1..) {
                let (high, low) = div_rem(digit, digit_splitter);
                new_digits[i] += low * digit_shifter;
                new_digits.push(high);
            }
        }

        return new_digits;
    }

    // at this point, rounding_point > 0
    let rounding_point = rounding_point as usize;
    let rounding_info = RoundingInfo::from(&digit_vec, rounding_point);

    let rounded_digit = match (
        rounding_mode,
        Sign::Plus,
        rounding_info.left,
        rounding_info.right,
        rounding_info.suffix_zeros,
    ) {
        // all digits following "left" are zero -> never change "left"
        (_, _, left, 0, true) => left,
        // Towards +∞
        (RoundingMode::Ceiling, Sign::Plus, left, _, _) => left + 1,
        (RoundingMode::Ceiling, Sign::NoSign, left, _, _) => left,
        (RoundingMode::Ceiling, Sign::Minus, left, _, _) => left,
        // Away from 0
        (RoundingMode::Up, _, left, _, _) => left + 1,
        // Handle rounding-point = 5
        (RoundingMode::HalfUp, _, left, 5, true) => left + 1,
        (RoundingMode::HalfUp, _, left, right, _) => left + (right >= 5) as u8,
        (RoundingMode::HalfEven, _, left, 5, true) => left + left % 2,
        (RoundingMode::HalfEven, _, left, right, _) => left + (right >= 5) as u8,
        (RoundingMode::HalfDown, _, left, 5, true) => left,
        (RoundingMode::HalfDown, _, left, right, _) => left + (right >= 5) as u8,
        // Towards 0
        (RoundingMode::Down, _, left, _, _) => left,
        // Towards -∞
        (RoundingMode::Floor, Sign::Plus, left, _, _) => left,
        (RoundingMode::Floor, Sign::NoSign, left, _, _) => left,
        (RoundingMode::Floor, Sign::Minus, left, _, _) => left + 1,
    } as BigDigitBaseDouble;

    let digit_shifter = ten_to_pow!(rounding_info.offset);
    let digit_booster = ten_to_pow!(MAX_DIGITS_PER_BIGDIGIT as u8 - rounding_info.offset);

    // rounding to the left of the decimal point
    if new_scale < 0 {
        if digit_vec.len() == rounding_info.index + 1 {
            let number = digit_vec[rounding_info.index] as BigDigitBaseDouble;
            let shifted_number = number / digit_shifter;
            let new_digit_number = (shifted_number - shifted_number % 10) + rounded_digit;
            let new_digits = digit_vec![ (FROM-BASE-TEN) new_digit_number ];
            return new_digits;
        }
    }

    if digit_vec.len() <= rounding_info.index {
        let digit = match (Sign::Plus, rounding_mode) {
            (_, RoundingMode::Up) => 1,
            (Sign::Minus, RoundingMode::Ceiling) => 0,
            (Sign::NoSign, RoundingMode::Ceiling) => 0,
            (Sign::Plus, RoundingMode::Ceiling) => 1,
            (_, RoundingMode::Down) => 0,
            (Sign::Minus, RoundingMode::Floor) => 1,
            (Sign::NoSign, RoundingMode::Floor) => 0,
            (Sign::Plus, RoundingMode::Floor) => 0,
            (_, RoundingMode::HalfUp) => 0,
            (_, RoundingMode::HalfDown) => 0,
            (_, RoundingMode::HalfEven) => 0,
        };

        return vec![digit];
    }

    // only process one digit
    if digit_vec.len() == rounding_info.index + 1 {
        let number = digit_vec[rounding_info.index] as BigDigitBaseDouble;
        let shifted_number = number / digit_shifter;
        let new_digit_number = (shifted_number - shifted_number % 10) + rounded_digit;
        let new_digits = digit_vec![ (FROM-BASE-TEN) new_digit_number ];

        return new_digits;
    }

    let digit_0 = {
        let number = digit_vec[rounding_info.index] as BigDigitBaseDouble;
        let x = number / digit_shifter;
        x - x % 10 + rounded_digit
    };

    // handle crossing bigdigit boundary
    // [_____x] [y_______] ->
    if rounding_info.offset == 0 {
        let mut rounded_digit_vec = Vec::with_capacity(digit_vec.len() - rounding_info.index + 1);

        // position from which to copy remaining digits
        let mut index = rounding_info.index + 1;

        // whether or not more data needs copied
        let needs_copy = if digit_0 < BIG_DIGIT_RADIX {
            rounded_digit_vec.push(digit_0 as BigDigitBase);
            index < digit_vec.len() // needs copy if index is less than length
        } else {
            rounded_digit_vec.push((digit_0 - BIG_DIGIT_RADIX) as BigDigitBase);

            loop {
                let shifted_digit = digit_vec[index] as BigDigitBaseDouble + 1;
                index += 1;
                if shifted_digit < BIG_DIGIT_RADIX {
                    rounded_digit_vec.push(shifted_digit as BigDigitBase);
                    break index < digit_vec.len(); // needs copy if index is less than length
                }
                rounded_digit_vec.push(0);
                if index == digit_vec.len() {
                    rounded_digit_vec.push(1);
                    break false; // does not need to copy from digit_vec
                }
            }
        };

        if needs_copy {
            rounded_digit_vec.extend_from_slice(&digit_vec[index..]);
        }

        let new_digits = crate::bigdigit::convert_to_base_u32_vec(&rounded_digit_vec);
        return new_digits;
    }

    let approx_bigdigit_count = (digit_vec.len() * MAX_DIGITS_PER_BIGDIGIT)
        .saturating_sub(rounding_point)
        .max(1);

    let mut result = Vec::with_capacity(approx_bigdigit_count);

    let d_i = digit_vec[rounding_info.index + 1] as BigDigitBaseDouble;

    let (h, l) = div_rem(d_i, digit_shifter);

    let (mut carry, x) = div_rem(digit_0 + (l * digit_booster), BIG_DIGIT_RADIX);
    result.push(x as BigDigitBase);
    result.push(h as BigDigitBase);

    let mut i = 2;

    // while std::intrinsics::unlikely(carry != 0) {
    while carry != 0 {
        debug_assert_eq!(carry, 1);

        if rounding_info.index + i == digit_vec.len() {
            return vec![0];
        }

        let d_i = digit_vec[rounding_info.index + i] as BigDigitBaseDouble;
        let (h, l) = div_rem(d_i, digit_shifter);

        let (crry, x) = div_rem(
            result[i - 1] as BigDigitBaseDouble + (l * digit_booster) + carry,
            BIG_DIGIT_RADIX,
        );
        carry = crry;

        result[i - 1] = x as BigDigitBase;
        result.push(h as BigDigitBase);

        i += 1;
    }

    while rounding_info.index + i < digit_vec.len() {
        let d_i = digit_vec[rounding_info.index + i] as BigDigitBaseDouble;
        let (h, l) = div_rem(d_i, digit_shifter);
        result[i - 1] += (l * digit_booster) as BigDigitBase;
        result.push(h as BigDigitBase);
        i += 1;
    }

    let new_digits = crate::bigdigit::convert_to_base_u32_vec(&result);
    return new_digits;
}
