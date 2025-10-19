//! Routines for multiplying numbers
//!
#![allow(dead_code)]
#![allow(clippy::identity_op)]

use stdlib::num::NonZeroU64;
use num_traits::AsPrimitive;

use crate::*;
use crate::rounding::{NonDigitRoundingData, InsigData};

use super::log10;

use crate::bigdigit::{
    radix::{RadixType, RadixPowerOfTen, RADIX_u64, RADIX_10_u8, RADIX_10p19_u64},
    endian::{Endianness, LittleEndian, BigEndian},
    digitvec::{DigitVec, DigitSlice},
};

type BigDigitVec = DigitVec<RADIX_u64, LittleEndian>;
type BigDigitVecBe = DigitVec<RADIX_u64, BigEndian>;
type BigDigitSliceU64<'a> = DigitSlice<'a, RADIX_u64, LittleEndian>;

type BigDigitVecP19 = DigitVec<RADIX_10p19_u64, LittleEndian>;
type BigDigitSliceP19<'a> = DigitSlice<'a, RADIX_10p19_u64, LittleEndian>;

type SmallDigitVec = DigitVec<RADIX_10_u8, LittleEndian>;

const BASE2_BIGINT_MUL_THRESHOLD: u64 = 128;


pub(crate) fn multiply_decimals_with_context<'a, A, B>(
    dest: &mut BigDecimal,
    a: A,
    b: B,
    ctx: &Context,
) where
    A: Into<BigDecimalRef<'a>>,
    B: Into<BigDecimalRef<'a>>,
{
    let a = a.into();
    let b = b.into();

    impl_multiply_decimals_with_context(dest, a, b, ctx);
}

pub fn impl_multiply_decimals_with_context(
    dest: &mut BigDecimal,
    a: BigDecimalRef,
    b: BigDecimalRef,
    ctx: &Context,
) {
    if a.is_zero() || b.is_zero() {
        *dest = BigDecimal::zero();
        return;
    }

    let sign = a.sign() * b.sign();
    let rounding_data = NonDigitRoundingData {
        sign: sign,
        mode: ctx.rounding_mode(),
    };

    let a_uint = a.digits;
    let b_uint = b.digits;

    match (a, b.is_one_quickcheck(), b, a.is_one_quickcheck()) {
        (x, Some(true), _, _) | (_, _, x, Some(true)) => {
            let WithScale {
                value: rounded_uint,
                scale: rounded_scale,
            } = rounding_data.round_biguint_to_prec(x.digits.clone(), ctx.precision());

            dest.scale = x.scale + rounded_scale;
            dest.int_val = BigInt::from_biguint(sign, rounded_uint);
            return;
        }
        _ => {}
    }

    if let (Some(x), Some(y)) = (a_uint.to_u64(), b_uint.to_u64()) {
        multiply_scaled_u64_into_decimal(
            dest,
            WithScale { value: x, scale: a.scale },
            WithScale { value: y, scale: b.scale },
            ctx.precision(),
            rounding_data,
        );
        debug_assert_eq!(dest.sign(), sign);
        return;
    }

    let a_vec = BigDigitVec::from(a_uint);
    let b_vec = BigDigitVec::from(b_uint);

    let digit_vec = BigDigitVec::new();
    let mut digit_vec_scale = WithScale::from((digit_vec, 0));

    multiply_scaled_u64_slices_with_prec_into(
        &mut digit_vec_scale,
        WithScale { value: a_vec.as_digit_slice(), scale: a.scale },
        WithScale { value: b_vec.as_digit_slice(), scale: b.scale },
        ctx.precision(),
        rounding_data,
    );

    dest.int_val = BigInt::from_biguint(sign, digit_vec_scale.value.into());
    dest.scale = digit_vec_scale.scale;
}

pub(crate) fn multiply_scaled_u64_into_decimal(
    dest: &mut BigDecimal,
    a: WithScale<u64>,
    b: WithScale<u64>,
    prec: NonZeroU64,
    rounding_data: NonDigitRoundingData,
) {
    use crate::arithmetic::decimal::count_digits_u128;

    let mut product = a.value as u128 * b.value as u128;
    let digit_count = count_digits_u128(product) as u64;

    let mut digits_to_remove = digit_count.saturating_sub(prec.get()) as u32;

    if digits_to_remove == 0 {
        dest.int_val = BigInt::from_biguint(rounding_data.sign, product.into());
        dest.scale = a.scale + b.scale;
        return;
    }

    let shifter = 10u128.pow(digits_to_remove - 1);
    let (hi, trailing) = product.div_rem(&shifter);
    let (shifted_product, insig_digit) = hi.div_rem(&10);
    let sig_digit = (shifted_product % 10) as u8;

    let rounded_digit = rounding_data.round_pair(
        (sig_digit, insig_digit as u8),
        trailing == 0,
    );

    product = shifted_product - sig_digit as u128 + rounded_digit as u128;

    if rounded_digit >= 10 {
        debug_assert_eq!(rounded_digit, 10);

        let old_digit_count = digit_count - digits_to_remove as u64;
        debug_assert_eq!(old_digit_count, count_digits_u128(shifted_product) as u64);

        let rounded_digit_count = count_digits_u128(product) as u64;
        if old_digit_count != rounded_digit_count {
            debug_assert_eq!(rounded_digit_count, old_digit_count + 1);
            product /= 10;
            digits_to_remove += 1;
        }
    }

    let digit_array = mul_split_u128_to_u32x4(product);
    dest.int_val.assign_from_slice(rounding_data.sign, &digit_array);

    dest.scale = a.scale + b.scale - digits_to_remove as i64;
}

/// Multiply digits in slices a and b, ignoring all factors that come from
/// digits "below" the given index (which is stored at index 0 in the dest)
///
/// ```ignore
///     a₀ a₁ a₂ a₃ ...
///  b₀| 0  1  2  3
///  b₁| 1  2  3  4   <- indexes in vector of the 'full' product
///  b₂| 2  3  4  5 ...
///  ```
///  If given idx '3', `dest[0] = a₁b₂ + a₂b₁ + a₃b₀` and `dest[1] = a₂b₂+...` etc
///
/// Carrying from lower digits is not calculated, so care must be given
/// to ensure data enough digits are provided.
///
pub(crate) fn multiply_at_product_index<R, E, EA, EB>(
    dest: &mut DigitVec<R, E>,
    a: DigitSlice<R, EA>,
    b: DigitSlice<R, EB>,
    idx: usize,
) where
    R: RadixType,
    E: Endianness,
    EA: Endianness,
    EB: Endianness,
{
    debug_assert!(b.len() <= a.len());

    dest.resize((a.len() + b.len()).saturating_sub(idx));

    let b_idx_min = idx.saturating_sub(a.len() - 1);

    for (b_idx, &x) in b.iter_le().enumerate().skip(b_idx_min).rev() {
        let a_idx_min = idx.saturating_sub(b_idx);
        debug_assert!(a_idx_min < a.len());

        let dest_idx = a_idx_min + b_idx - idx;

        let mut dest_digits = dest.iter_le_mut().skip(dest_idx);
        let mut carry = Zero::zero();
        for &y in a.iter_le().skip(a_idx_min) {
            R::carrying_mul_add_inplace(
                x, y, dest_digits.next().unwrap(), &mut carry
            );
        }
        R::add_carry_into(dest_digits, &mut carry);
        if !carry.is_zero() {
            dest.push_significant_digit(carry);
        }
    }
}


pub(crate) fn multiply_at_idx_into<R: RadixType>(
    dest: &mut DigitVec<R, LittleEndian>,
    a: DigitSlice<R, LittleEndian>,
    b: DigitSlice<R, LittleEndian>,
    idx: usize,
) {
    debug_assert!(a.len() + b.len() <= dest.len() + idx);
    for (ia, &da) in a.digits.iter().enumerate() {
        if da.is_zero() {
            continue;
        }
        let mut carry = Zero::zero();
        for (&db, result) in b.digits.iter().zip(dest.digits.iter_mut().skip(idx + ia)) {
            R::carrying_mul_add_inplace(da, db, result, &mut carry);
        }
        dest.add_value_at(idx + ia + b.len(), carry);
    }
}

pub(crate) fn multiply_big_int_with_ctx(a: &BigInt, b: &BigInt, ctx: Context) -> WithScale<BigInt> {
    let sign = a.sign() * b.sign();
    // Rounding prec: usize
    let rounding_data = NonDigitRoundingData {
        sign: sign,
        mode: ctx.rounding_mode(),
    };

    // if bits are under this threshold, just multiply full integer and round
    if a.bits() + b.bits() < BASE2_BIGINT_MUL_THRESHOLD {
        return ctx.round_bigint(a * b);
    }

    let mut tmp = Vec::new();
    let a_p19_vec = BigDigitVecP19::from_biguint_using_tmp(a.magnitude(), &mut tmp);
    let b_p19_vec = BigDigitVecP19::from_biguint_using_tmp(b.magnitude(), &mut tmp);

    let mut result = WithScale::default();
    multiply_slices_with_prec_into_p19(
        &mut result,
        a_p19_vec.as_digit_slice(),
        b_p19_vec.as_digit_slice(),
        ctx.precision(),
        rounding_data
    );

    WithScale {
        scale: result.scale,
        value: result.value.into_bigint(sign),
    }
}

/// Store product of 'a' & 'b' into dest, only calculating 'prec'
/// number of digits
///
/// Use 'rounding' to round at requested position.
/// Assumes 'a' & 'b' are full numbers, so all insignificant digits
/// are zero.
///
pub(crate) fn multiply_slices_with_prec_into_p19(
    dest: &mut WithScale<BigDigitVecP19>,
    a: BigDigitSliceP19,
    b: BigDigitSliceP19,
    prec: NonZeroU64,
    rounding: NonDigitRoundingData
) {
    multiply_slices_with_prec_into_p19_z(dest, a, b, prec, rounding, true)
}


/// Store product of 'a' & 'b' into dest, only calculating 'prec' number of digits
///
/// Use 'rounding' information to round at requested position.
/// The 'assume_trailing_zeros' parameter determines proper rounding technique if
/// 'a' & 'b' are partial numbers, where trailing insignificant digits may or may
/// not be zero.
///
pub(crate) fn multiply_slices_with_prec_into_p19_z(
    dest: &mut WithScale<BigDigitVecP19>,
    a: BigDigitSliceP19,
    b: BigDigitSliceP19,
    prec: NonZeroU64,
    rounding: NonDigitRoundingData,
    assume_trailing_zeros: bool,
) {
    use super::bigdigit::alignment::BigDigitSplitter;
    use super::bigdigit::alignment::BigDigitSliceSplitterIter;
    type R = RADIX_10p19_u64;

    if a.len() < b.len() {
        // ensure a is the longer of the two digit slices
        return multiply_slices_with_prec_into_p19_z(dest, b, a, prec, rounding, assume_trailing_zeros);
    }

    dest.value.clear();

    if b.is_all_zeros() || a.is_all_zeros() {
        // multiplication by zero: return after clearing dest
        return;
    }

    debug_assert_ne!(a.len(), 0);
    debug_assert_ne!(b.len(), 0);

    let WithScale { value: dest, scale: result_scale } = dest;

    // minimum possible length of each integer, given length of bigdigit vecs
    let pessimistic_product_digit_count = (a.len() + b.len() - 2) * R::DIGITS + 1;

    // require more digits of precision for overflow and rounding
    // max number of digits produced by adding all bigdigits at any
    // particular "digit-index" i of the product
    //  log10( Σ a_m × b_n (∀ m+n=i) )
    let max_digit_sum_width = (2.0 * log10(R::max() as f64) + log10(b.len() as f64)).ceil() as usize;
    let max_bigdigit_sum_width = R::divceil_digit_count(max_digit_sum_width);
    // the "index" of the product which could affect the significant results
    let digits_to_skip = pessimistic_product_digit_count.saturating_sub(prec.get() as usize + 1);
    let bigdigits_to_skip = R::divceil_digit_count(digits_to_skip)
                              .saturating_sub(max_bigdigit_sum_width);

    let a_start;
    let b_start;
    if bigdigits_to_skip == 0 {
        // we've requested more digits than product will produce; don't skip any digits
        a_start = 0;
        b_start = 0;
    } else {
        // the indices of the least significant bigdigits in a and b which may contribute
        // to the significant digits in the product
        a_start = bigdigits_to_skip.saturating_sub(b.len());
        b_start = bigdigits_to_skip.saturating_sub(a.len());
    }

    let a_sig = a.trim_insignificant(a_start);
    let b_sig = b.trim_insignificant(b_start);

    let a_sig_digit_count = a_sig.count_decimal_digits();
    let b_sig_digit_count = b_sig.count_decimal_digits();

    // calculate maximum number of digits from product
    let max_sigproduct_bigdigit_count = R::divceil_digit_count(a_sig_digit_count + b_sig_digit_count + 1);
    let mut product =
        BigDigitVecP19::with_capacity(max_sigproduct_bigdigit_count + max_bigdigit_sum_width + 1);

    *result_scale -= (R::DIGITS * bigdigits_to_skip) as i64;

    multiply_at_product_index(&mut product, a, b, bigdigits_to_skip);
    product.remove_leading_zeros();

    let product_digit_count = product.count_decimal_digits();

    // precision plus the rounding digit
    let digits_to_remove = product_digit_count.saturating_sub(prec.get() as usize);
    if digits_to_remove == 0 {
        debug_assert_eq!(a_start, 0);
        debug_assert_eq!(b_start, 0);
        debug_assert_eq!(bigdigits_to_skip, 0);

        // no need to trim the results, everything was significant;
        *dest = product;
        return;
    }

    // removing insignificant digits decreases the scale
    *result_scale -= digits_to_remove as i64;

    // keep adding more multiplication terms if the number ends with 999999...., until
    // the nines stop or it overflows.
    // NOTE: the insignificant digits in 'product' will be _wrong_ and must be ignored
    let trailing_zeros = assume_trailing_zeros && calculate_partial_product_trailing_zeros(
        &mut product, a, b, bigdigits_to_skip, digits_to_remove
    );

    // remove the digits, returning the top one to be used
    let insig_digit = product.shift_n_digits_returning_high(digits_to_remove);
    let sig_digit = (product.digits[0] % 10) as u8;

    let insig_rounding_data = InsigData {
        rounding_data: rounding,
        digit: insig_digit,
        trailing_zeros,
    };

    let rounded_digit = insig_rounding_data.round_digit(sig_digit);

    let mut carry = rounded_digit as u64;

    product.digits[0] -= sig_digit as u64;

    R::add_carry_into_slice(
        &mut product.digits, &mut carry
    );

    if carry != 0 {
        debug_assert!(product.digits.iter().all(|&d| d == 0));
        *result_scale -= 1;
        *product.digits.last_mut().unwrap() = (R::RADIX as u64) / 10;
    }

    if rounded_digit == 10 && product.count_decimal_digits() != prec.get() as usize {
        *result_scale -= 1;

        if let Some((hi, zeros)) = product.digits.split_last_mut() {
            debug_assert!(*hi >= 10);
            debug_assert!(zeros.iter().all(|&d| d == 0));
            *hi /= 10;
        } else {
            unreachable!();
        }
    }

    *dest = product;
}

/// Store `a * b` into dest, to limited precision
pub(crate) fn multiply_scaled_u64_slices_with_prec_into(
    dest: &mut WithScale<BigDigitVec>,
    a: WithScale<BigDigitSliceU64>,
    b: WithScale<BigDigitSliceU64>,
    prec: NonZeroU64,
    rounding: NonDigitRoundingData,
) {
    let a_base10: BigDigitVecP19 = a.value.into();
    let b_base10: BigDigitVecP19 = b.value.into();

    let mut product = WithScale::default();
    multiply_slices_with_prec_into_p19(
        &mut product,
        a_base10.as_digit_slice(),
        b_base10.as_digit_slice(),
        prec,
        rounding,
    );

    dest.scale = a.scale + b.scale + product.scale;
    dest.value = product.value.into();
}

/// Calculate the 'backwards' product of a & b, stopping when it can be
/// proven that no further overflow can happen
///
/// Return true if the product after overflow-calculation has all
/// trailing zeros.
///
/// Parameter 'v' here is the pre-calculated "extended" product of a & b,
/// extended meaning it has incorrect insignificant digits that were
/// calculated to add overflow/carrys into the significant digits.
/// This function continues multiplying trailing digits if there is a
/// chance that a rounding.
///
/// 'product_idx' is the index of the true product where v starts
/// (i.e. v[0] corresponds to true_product[product_idx], used here for
/// calculating the insignificant product of a and b, backwards.
///
/// 'digits_to_remove' is the number of digits in v that should be
/// considered insignificant, and may be changed by this function.
///
fn calculate_partial_product_trailing_zeros(
    v: &mut BigDigitVecP19,
    a: BigDigitSliceP19,
    b: BigDigitSliceP19,
    product_idx: usize,
    digits_to_remove: usize,
) -> bool {
    type R = RADIX_10p19_u64;

    if digits_to_remove == 0 {
        return true;
    }

    debug_assert!(b.len() <= a.len());
    debug_assert!(digits_to_remove <= v.count_decimal_digits());

    let (insig_bd_count, insig_d_count) = R::divmod_digit_count(digits_to_remove);
    debug_assert!(insig_bd_count > 0 || insig_d_count > 0);

    let trailing_zeros;
    let trailing_nines;

    // index of the first "full" insignificant big-digit
    let top_insig_idx;

    match (insig_bd_count, insig_d_count as u8) {
        (0, 0) => unreachable!(),
        (0, 1) => {
            return true;
        }
        (0, 2) => {
            return v.digits[0] % 10 == 0;
        }
        (0, n) => {
            let splitter = ten_to_the_u64(n - 1);
            return v.digits[0] % splitter == 0;
        }
        (1, 0) => {
            let splitter = ten_to_the_u64(R::DIGITS as u8 - 1);
            return v.digits[0] % splitter == 0;
        }
        (1, 1) => {
            return v.digits[0] == 0;
        }
        (i, 1) => {
            // special case when the 'top' insignificant digit is
            // with the other digits
            trailing_zeros = v.digits[i - 1] == 0;
            trailing_nines = v.digits[i - 1] == R::max();
            top_insig_idx = i - 1;
        }
        (i, 0) => {
            // split on a boundary, check previous bigdigit
            let insig = v.digits[i - 1];
            let splitter = ten_to_the_u64(R::DIGITS as u8 - 1);
            let insig_digits = insig % splitter;
            trailing_zeros = insig_digits == 0
                             && v.iter_le().take(i - 1).all(Zero::is_zero);
            trailing_nines = insig_digits == splitter - 1;
            top_insig_idx = i - 2;
        }
        (i, n) => {
            let insig = v.digits[i];
            let splitter = ten_to_the_u64(n - 1);
            let insig_digits = insig % splitter;
            trailing_zeros = insig_digits == 0
                             && v.iter_le().take(i).all(Zero::is_zero);
            trailing_nines = insig_digits == splitter - 1;
            top_insig_idx = i - 1;
        }
    }


    // the insignificant digits should be at least one bigdigit wider
    // than the maximum overflow from one iteration of preceding digits
    // debug_assert!(insig_bd_count >= max_bigdigit_sum_width, "{}, {}", insig_bd_count, max_bigdigit_sum_width);

    // not zero and no chance for overflow
    if !trailing_zeros && !trailing_nines {
        return false;
    }

    if product_idx == 0 {
        // no new multiplications needs to happen, just return if
        // product has trailing zeros
        return trailing_zeros
            && v.digits[..top_insig_idx].iter().all(|&d| d == 0);
    }

    // check if last bigdigit in product is not zero before iterative multiplication
    if trailing_zeros && (a.digits[0].saturating_mul(b.digits[0])) != 0 {
       return false;
    }

    for idx in (0..product_idx).rev() {
        let a_range;
        let b_range;
        if idx < b.len() {
            // up to and including 'idx'
            a_range = 0..idx + 1;
            b_range = 0..idx + 1;
        } else if idx < a.len() {
            a_range = idx - b.len() + 1..idx + 1;
            b_range = 0..b.len();
        } else {
            a_range = idx - b.len() + 1..a.len();
            b_range = idx - a.len() + 1..b.len();
        }
        debug_assert_eq!(
            a_range.end - a_range.start,
            b_range.end - b_range.start,
        );

        let a_start = a_range.start;
        let b_start = b_range.start;
        let a_digits = a.digits[a_range].iter();
        let b_digits = b.digits[b_range].iter().rev();

        let mut d0 = 0;

        let mut carry = Zero::zero();
        for (&x, &y) in a_digits.zip(b_digits) {
            R::carrying_mul_add_inplace(x, y, &mut d0, &mut carry);
            R::add_carry_into(v.digits.iter_mut(), &mut carry);
        }
        debug_assert_eq!(carry, 0);

        let top_insig = v.digits[top_insig_idx];
        if top_insig != R::max() {
            // we have overflowed!
            return v.least_n_are_zero(top_insig_idx)
                && a.least_n_are_zero(a_start)
                && b.least_n_are_zero(b_start);
        }

        // shift the insignificant digits in the vector by one
        // (i.e. the '9999999' in highest insig bigdigit may be ignored)
        v.digits.copy_within(..top_insig_idx, 1);
        v.digits[0] = d0;
    }

    // never overflowed, therefore "trailing zeros" is false
    return false;
}

/// Calculate dest = a * b to at most 'prec' number of bigdigits, truncating (not rounding)
/// the results.
///
/// The scale of these vector/slices is number of *bigdigits*, not number of digits.
///
/// Returns the number of 'skipped' bigdigits in the result.
///
pub(crate) fn mul_scaled_slices_truncating_into<R, E, EA, EB>(
    dest: &mut WithScale<DigitVec<R, E>>,
    a: WithScale<DigitSlice<'_, R, EA>>,
    b: WithScale<DigitSlice<'_, R, EB>>,
    prec: u64,
) -> usize
where
    R: RadixType,
    E: Endianness,
    EA: Endianness,
    EB: Endianness,
{
    use super::bigdigit::alignment::BigDigitSplitter;
    use super::bigdigit::alignment::BigDigitSliceSplitterIter;
    type R = RADIX_10p19_u64;

    if a.value.len() < b.value.len() {
        // ensure a is the longer of the two digit slices
        return mul_scaled_slices_truncating_into(dest, b, a, prec);
    }

    let WithScale { value: product, scale: dest_scale } = dest;
    let WithScale { value: a, scale: a_scale } = a;
    let WithScale { value: b, scale: b_scale } = b;

    *dest_scale = a_scale + b_scale;
    product.clear();

    if b.is_all_zeros() || a.is_all_zeros() {
        // multiplication by zero: return after clearing dest
        return 0;
    }

    debug_assert_ne!(a.len(), 0);
    debug_assert_ne!(b.len(), 0);

    // require more digits of precision for overflow and rounding
    // max number of digits produced by adding all bigdigits at any
    // particular "digit-index" i of the product
    //  log10( Σ a_m × b_n (∀ m+n=i) )
    let max_digit_sum_width = (2.0 * log10(R::max() as f64) + log10(b.len() as f64)).ceil() as usize;
    let max_bigdigit_sum_width = R::divceil_digit_count(max_digit_sum_width);

    let max_product_size = a.len() + b.len();
    let max_vector_size = prec as usize + max_bigdigit_sum_width;
    let bigdigits_to_skip = max_product_size.saturating_sub(max_vector_size);

    *dest_scale -= bigdigits_to_skip as i64;

    multiply_at_product_index(product, a, b, bigdigits_to_skip);
    product.remove_leading_zeros();
    let extra_digit_count = product.len().saturating_sub(prec as usize);
    product.remove_insignificant_digits(extra_digit_count);
    *dest_scale -= extra_digit_count as i64;

    return bigdigits_to_skip;
}


/// split u64 into high and low bits
fn split_u64(x: u64) -> (u64, u64) {
    x.div_rem(&(1 << 32))
}

fn mul_split_u64_u64(a: u64, b: u64) -> [u32; 4] {
    let p = u128::from(a) * u128::from(b);
    mul_split_u128_to_u32x4(p)
}

fn mul_split_u128_to_u32x4(n: u128) -> [u32; 4] {
    [
        (n >> 0).as_(),
        (n >> 32).as_(),
        (n >> 64).as_(),
        (n >> 96).as_(),
    ]
}

/// Add carry into dest
#[inline]
fn _apply_carry_u64(dest: &mut [u32], mut idx: usize, mut carry: u64) {
    while carry != 0 {
        idx += 1;
        let (c, r) = split_u64(dest[idx] as u64 + carry);
        dest[idx] = r as u32;
        carry = c;
    }
}

/// Evaluate (a + (b << 64))^2, where a and b are u64's, storing
/// the result as u32's in *dest*, starting at location *idx*
///
/// This is useful for a and b as adjacent big-digits in a big-
/// number, or components of a u128, squared.
///
/// (a + (b << 64))^2 = a^2 + (2 ab) << 64 + (b^2) << 128
///
pub(crate) fn multiply_2_u64_into_u32(
    dest: &mut [u32], mut idx: usize, a: u64, b: u64
) {
    let [aa0, aa1, aa2, aa3] = mul_split_u64_u64(a, a);
    let [ab0, ab1, ab2, ab3] = mul_split_u64_u64(a, b);
    let [bb0, bb1, bb2, bb3] = mul_split_u64_u64(b, b);

    let (carry, r0) = split_u64(dest[idx] as u64         + aa0 as u64);
    dest[idx] = r0 as u32;

    idx += 1;
    let (carry, r1) = split_u64(dest[idx] as u64 + carry + aa1 as u64);
    dest[idx] = r1 as u32;

    idx += 1;
    let (carry, r2) = split_u64(dest[idx] as u64 + carry + aa2 as u64 + ab0 as u64 * 2);
    dest[idx] = r2 as u32;

    idx += 1;
    let (carry, r3) = split_u64(dest[idx] as u64 + carry + aa3 as u64 + ab1 as u64 * 2);
    dest[idx] = r3 as u32;

    idx += 1;
    let (carry, r4) = split_u64(dest[idx] as u64 + carry              + ab2 as u64 * 2 + bb0 as u64);
    dest[idx] = r4 as u32;

    idx += 1;
    let (carry, r5) = split_u64(dest[idx] as u64 + carry              + ab3 as u64 * 2 + bb1 as u64);
    dest[idx] = r5 as u32;

    idx += 1;
    let (carry, r6) = split_u64(dest[idx] as u64 + carry                               + bb2 as u64);
    dest[idx] = r6 as u32;

    idx += 1;
    let (carry, r7) = split_u64(dest[idx] as u64 + carry                               + bb3 as u64);
    dest[idx] = r7 as u32;

    _apply_carry_u64(dest, idx + 1, carry);
}

/// dest += ((b<<64) + a) * ((z<<64) + y)
pub(crate) fn _multiply_into_4_u64(
    dest: &mut [u32], idx: usize, a: u64, b: u64, y: u64, z: u64
) {
    let [ay0, ay1, ay2, ay3] = mul_split_u64_u64(a, y);
    let [az0, az1, az2, az3] = mul_split_u64_u64(a, z);
    let [by0, by1, by2, by3] = mul_split_u64_u64(b, y);
    let [bz0, bz1, bz2, bz3] = mul_split_u64_u64(b, z);

    let (carry, r0) = split_u64(dest[idx + 0] as u64         + (ay0 as u64                                       ) * 2);
    dest[idx + 0] = r0 as u32;

    let (carry, r1) = split_u64(dest[idx + 1] as u64 + carry + (ay1 as u64                                       ) * 2);
    dest[idx + 1] = r1 as u32;

    let (carry, r2) = split_u64(dest[idx + 2] as u64 + carry + (ay2 as u64 + az0 as u64 + by0 as u64             ) * 2);
    dest[idx + 2] = r2 as u32;

    let (carry, r3) = split_u64(dest[idx + 3] as u64 + carry + (ay3 as u64 + az1 as u64 + by1 as u64             ) * 2);
    dest[idx + 3] = r3 as u32;

    let (carry, r4) = split_u64(dest[idx + 4] as u64 + carry + (             az2 as u64 + by2 as u64 + bz0 as u64) * 2);
    dest[idx + 4] = r4 as u32;

    let (carry, r5) = split_u64(dest[idx + 5] as u64 + carry + (             az3 as u64 + by3 as u64 + bz1 as u64) * 2);
    dest[idx + 5] = r5 as u32;

    let (carry, r6) = split_u64(dest[idx + 6] as u64 + carry + (                                       bz2 as u64) * 2);
    dest[idx + 6] = r6 as u32;

    let (carry, r7) = split_u64(dest[idx + 7] as u64 + carry + (                                       bz3 as u64) * 2);
    dest[idx + 7] = r7 as u32;

    _apply_carry_u64(dest, idx + 8, carry);
}

/// dest[idx..] += a ** 2
pub(crate) fn _multiply_1_u64_into_u32(
    dest: &mut [u32],
    mut idx: usize,
    a: u64
) {
    let [a0, a1, a2, a3] = mul_split_u64_u64(a, a);

    let (carry, r0) = split_u64(dest[idx] as u64 + a0 as u64);
    dest[idx] = r0 as u32;

    idx += 1;
    let (carry, r1) = split_u64(dest[idx] as u64 + carry + a1 as u64);
    dest[idx] = r1 as u32;

    idx += 1;
    let (carry, r2) = split_u64(dest[idx] as u64 + carry + a2 as u64);
    dest[idx] = r2 as u32;

    idx += 1;
    let (carry, r3) = split_u64(dest[idx] as u64 + carry + a3 as u64);
    dest[idx] = r3 as u32;

    _apply_carry_u64(dest, idx + 1, carry);
}


/// Evaluate (a + b << 64)^2 and store in dest at location idx
pub(crate) fn _multiply_2_u64_into_u32(
    dest: &mut [u32],
    mut idx: usize,
    a: u64,
    b: u64,
) {
    let [aa0, aa1, aa2, aa3] =  mul_split_u64_u64(a, a);
    let [ab0, ab1, ab2, ab3] =  mul_split_u64_u64(a, b);
    let [bb0, bb1, bb2, bb3] =  mul_split_u64_u64(b, b);

    let (carry, r0) = split_u64(dest[idx] as u64         + aa0 as u64);
    dest[idx] = r0 as u32;

    idx += 1;
    let (carry, r1) = split_u64(dest[idx] as u64 + carry + aa1 as u64);
    dest[idx] = r1 as u32;

    idx += 1;
    let (carry, r2) = split_u64(dest[idx] as u64 + carry + aa2 as u64 + ab0 as u64 * 2);
    dest[idx] = r2 as u32;

    idx += 1;
    let (carry, r3) = split_u64(dest[idx] as u64 + carry + aa3 as u64 + ab1 as u64 * 2);
    dest[idx] = r3 as u32;

    idx += 1;
    let (carry, r4) = split_u64(dest[idx] as u64 + carry              + ab2 as u64 * 2 + bb0 as u64);
    dest[idx] = r4 as u32;

    idx += 1;
    let (carry, r5) = split_u64(dest[idx] as u64 + carry              + ab3 as u64 * 2 + bb1 as u64);
    dest[idx] = r5 as u32;

    idx += 1;
    let (carry, r6) = split_u64(dest[idx] as u64 + carry                               + bb2 as u64);
    dest[idx] = r6 as u32;

    idx += 1;
    let (carry, r7) = split_u64(dest[idx] as u64 + carry                               + bb3 as u64);
    dest[idx] = r7 as u32;

    _apply_carry_u64(dest, idx + 1, carry);
}


/// Evaluate z * (a + b << 64) and store in dest at location idx
pub(crate) fn _multiply_3_u64_into_u32(
    dest: &mut [u32],
    mut idx: usize,
    a: u64,
    b: u64,
    z: u64,
) {
    let [az0, az1, az2, az3] = mul_split_u64_u64(a, z);
    let [bz0, bz1, bz2, bz3] = mul_split_u64_u64(b, z);

    let (carry, r0) = split_u64(dest[idx] as u64         + (az0 as u64             ) * 2);
    dest[idx] = r0 as u32;

    idx += 1;
    let (carry, r1) = split_u64(dest[idx] as u64 + carry + (az1 as u64             ) * 2);
    dest[idx] = r1 as u32;

    idx += 1;
    let (carry, r2) = split_u64(dest[idx] as u64 + carry + (az2 as u64 + bz0 as u64) * 2);
    dest[idx] = r2 as u32;

    idx += 1;
    let (carry, r3) = split_u64(dest[idx] as u64 + carry + (az3 as u64 + bz1 as u64) * 2);
    dest[idx] = r3 as u32;

    idx += 1;
    let (carry, r4) = split_u64(dest[idx] as u64 + carry + (             bz2 as u64) * 2);
    dest[idx] = r4 as u32;

    idx += 1;
    let (carry, r5) = split_u64(dest[idx] as u64 + carry + (             bz3 as u64) * 2);
    dest[idx] = r5 as u32;

    _apply_carry_u64(dest, idx + 1, carry);
}


/// dest[idx0..] += (a + (b << 64)) * z
pub(crate) fn multiply_thrup_spread_into(
    dest: &mut [u32],
    idx0: usize,
    a: u32,
    b: u32,
    z: u32,
) {
    let a = a as u64;
    let b = b as u64;
    let z = z as u64;

    let az = a * z;
    let bz = b * z;

    let (azh, azl) = split_u64(az);
    let (bzh, bzl) = split_u64(bz);

    let (carry, r0) = split_u64(dest[idx0 + 0] as u64 + azl * 2);
    dest[idx0 + 0] = r0 as u32;

    let (carry, r1) = split_u64(dest[idx0 + 1] as u64 + carry + (azh + bzl) * 2);
    dest[idx0 + 1] = r1 as u32;

    let (mut carry, r2) = split_u64(dest[idx0 + 2] as u64 + carry + bzh * 2);
    dest[idx0 + 2] = r2 as u32;

    let mut idx = idx0 + 3;
    while carry != 0 {
        let (c, overflow) = split_u64(dest[idx] as u64 + carry);
        dest[idx] = overflow as u32;
        carry = c;
        idx += 1;
    }
}

/// Multiply two pairs of bigdigits, storing carries into dest,
///
pub(crate) fn multiply_thrup_spread_into_wrapped(
    dest: &mut [u32],
    idx0: usize,
    a: u32,
    b: u32,
    z: u32,
) {
    let a = a as u64;
    let b = b as u64;
    let z = z as u64;

    let az = a * z;
    let bz = b * z;

    let (azh, azl) = split_u64(az);
    let (bzh, bzl) = split_u64(bz);

    let (carry, r0) = split_u64(dest[idx0 + 0] as u64 + azl * 2);
    dest[idx0 + 0] = r0 as u32;

    let (carry, r1) = split_u64(dest[idx0 + 1] as u64 + carry + (azh + bzl) * 2);
    dest[idx0 + 1] = r1 as u32;

    let (mut carry, r2) = split_u64(dest[idx0 + 2] as u64 + carry + bzh * 2);
    dest[idx0 + 2] = r2 as u32;

    let mut idx = idx0 + 3;
    while carry != 0 {
        let (c, overflow) = split_u64(dest[idx] as u64 + carry);
        dest[idx] = overflow as u32;
        carry = c;
        idx += 1;
    }
}

/// Multiply two pairs of bigdigits, storing carries into dest,
///
/// Used for multiplying `(a + b) * (y + z) => (ay + by + az + bz)`
/// Where (a,b) and (x,y) pairs are consecutive bigdigits.
///
/// Results of the multiplication are stored in 'dest' starting
/// with ay at index 'idx'
///
pub(crate) fn multiply_quad_spread_into(
    dest: &mut [u32],
    idx0: usize,
    a: u32,
    b: u32,
    y: u32,
    z: u32,
) {
    let ay = a as u64 * y as u64;
    let az = a as u64 * z as u64;

    let by = b as u64 * y as u64;
    let bz = b as u64 * z as u64;

    let (ayh, ayl) = split_u64(ay);
    let (azh, azl) = split_u64(az);
    let (byh, byl) = split_u64(by);
    let (bzh, bzl) = split_u64(bz);

    let (carry, r0) = split_u64(dest[idx0 + 0] as u64 + ayl * 2);
    dest[idx0 + 0] = r0 as u32;

    let (carry, r1) = split_u64(dest[idx0 + 1] as u64 + carry + (ayh + azl + byl) * 2);
    dest[idx0 + 1] = r1 as u32;

    let (carry, r2) = split_u64(dest[idx0 + 2] as u64 + carry + (azh + byh + bzl) * 2);
    dest[idx0 + 2] = r2 as u32;

    let (mut carry, r3) = split_u64(dest[idx0 + 3] as u64 + carry + bzh * 2);
    dest[idx0 + 3] = r3 as u32;

    let mut idx = idx0 + 4;
    while carry != 0 {
        let (c, overflow) = split_u64(dest[idx] as u64 + carry);
        dest[idx] = overflow as u32;
        carry = c;
        idx += 1;
    }
}

/// multiply_quad_spread_into
///
pub(crate) fn multiply_quad_spread_into_wrapping(
    dest: &mut [u32],
    idx: usize,
    a: u32,
    b: u32,
    y: u32,
    z: u32,
) {
    let ay = a as u64 * y as u64;
    let az = a as u64 * z as u64;

    let by = b as u64 * y as u64;
    let bz = b as u64 * z as u64;

    let (ayh, ayl) = split_u64(ay);
    let (azh, azl) = split_u64(az);
    let (byh, byl) = split_u64(by);
    let (bzh, bzl) = split_u64(bz);

    let wrap = dest.len();
    let mut idx = idx % wrap;

    let (carry, r0) = split_u64(dest[idx] as u64 + ayl * 2);
    dest[idx] = r0 as u32;

    idx = (idx + 1) % wrap;
    let (carry, r1) = split_u64(dest[idx] as u64 + carry + (ayh + azl + byl) * 2);
    dest[idx] = r1 as u32;

    idx = (idx + 1) % wrap;
    let (carry, r2) = split_u64(dest[idx] as u64 + carry + (azh + byh + bzl) * 2);
    dest[idx] = r2 as u32;

    idx = (idx + 1) % wrap;
    let (mut carry, r3) = split_u64(dest[idx] as u64 + carry + bzh * 2);
    dest[idx] = r3 as u32;

    while carry != 0 {
        idx = (idx + 1) % wrap;
        let (c, overflow) = split_u64(dest[idx] as u64 + carry);
        dest[idx] = overflow as u32;
        carry = c;
    }
}

#[cfg(test)]
mod test {
    use super::*;
    include!("multiplication.tests.rs");
}
