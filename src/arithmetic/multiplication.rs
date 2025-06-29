//! Routines for multiplying numbers
//!
#![allow(dead_code)]
#![allow(unreachable_code)]
#![allow(unused_variables)]

use stdlib::num::NonZeroU64;
use num_traits::AsPrimitive;

use crate::*;
use crate::rounding::{NonDigitRoundingData, InsigData};

use crate::bigdigit::{
    radix::{RadixType, RADIX_u64, RADIX_10_u8, RADIX_10p19_u64},
    endian::{Endianness, LittleEndian, BigEndian},
    digitvec::{DigitVec, DigitSlice},
};

type BigDigitVec = DigitVec<RADIX_u64, LittleEndian>;
type BigDigitVecBe = DigitVec<RADIX_u64, BigEndian>;
type BigDigitSlice<'a> = DigitSlice<'a, RADIX_u64, LittleEndian>;

type BigDigitVecP19 = DigitVec<RADIX_10p19_u64, LittleEndian>;
type BigDigitSliceP19<'a> = DigitSlice<'a, RADIX_10p19_u64, LittleEndian>;

type SmallDigitVec = DigitVec<RADIX_10_u8, LittleEndian>;

const BASE2_BIGINT_MUL_THRESHOLD: u64 = 128;


pub(crate) fn multiply_decimals_with_context<'a, A, B>(
    dest: &mut BigDecimal,
    a: A,
    b: B,
    ctx: &Context,
)
where
    A: Into<BigDecimalRef<'a>>,
    B: Into<BigDecimalRef<'a>>,
{
    let a = a.into();
    let b = b.into();

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

    let a_vec = BigDigitVec::from(a_uint);
    let b_vec = BigDigitVec::from(b_uint);

    let digit_vec = BigDigitVec::new();
    let mut digit_vec_scale = WithScale::from((digit_vec, 0));

    multiply_slices_with_prec_into(
        &mut digit_vec_scale,
        a_vec.as_digit_slice(),
        b_vec.as_digit_slice(),
        ctx.precision(),
        rounding_data
    );

    dest.int_val = BigInt::from_biguint(sign, digit_vec_scale.value.into());
    dest.scale = a.scale + b.scale - digit_vec_scale.scale;
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
pub(crate) fn multiply_at_product_index<R: RadixType>(
    dest: &mut DigitVec<R, LittleEndian>,
    a: DigitSlice<R, LittleEndian>,
    b: DigitSlice<R, LittleEndian>,
    idx: usize,
) {
    debug_assert!(b.len() <= a.len());

    dest.resize((a.len() + b.len()).saturating_sub(idx));

    let b_idx_min = idx.saturating_sub(a.len() - 1);

    for b_idx in (b_idx_min..b.len()).rev() {
        let a_idx_min = idx.saturating_sub(b_idx);
        debug_assert!(a_idx_min < a.len());

        let mut dest_idx = a_idx_min + b_idx - idx;

        let mut carry = Zero::zero();
        let x = b.digits[b_idx];
        for &y in a.digits.iter().skip(a_idx_min) {
            R::carrying_mul_add_inplace(
                x, y, &mut dest.digits[dest_idx], &mut carry
            );
            dest_idx += 1;
        }
        R::add_carry_into(dest.digits.iter_mut().skip(dest_idx), &mut carry);
        if !carry.is_zero() {
            dest.digits.push(carry);
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
    use bigdigit::radix::RadixPowerOfTen;

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

    // trim the trailing zeros from the multiplication
    let a_tz = a_p19_vec.digits.iter()
                               .position(|&d| d != 0)
                               .unwrap_or(a_p19_vec.len());
    let b_tz = b_p19_vec.digits.iter()
                               .position(|&d| d != 0)
                               .unwrap_or(b_p19_vec.len());

    let mut result = WithScale::default();
    multiply_slices_with_prec_into_p19(
        &mut result,
        a_p19_vec.as_digit_slice_at(a_tz),
        b_p19_vec.as_digit_slice_at(b_tz),
        ctx.precision(),
        rounding_data
    );

    // increase scale by this many trailing-zeros
    let trailing_zero_bigdigit_count = a_tz + b_tz;
    let trailing_zero_scale = (RADIX_10p19_u64::DIGITS * trailing_zero_bigdigit_count) as i64;

    WithScale {
        scale: result.scale - trailing_zero_scale,
        value: result.value.into_bigint(sign),
    }
}


#[allow(unreachable_code)]
pub(crate) fn multiply_slices_with_prec_into_p19(
    dest: &mut WithScale<BigDigitVecP19>,
    a: BigDigitSliceP19,
    b: BigDigitSliceP19,
    prec: NonZeroU64,
    rounding: NonDigitRoundingData
) {
    use crate::bigdigit::radix::RadixPowerOfTen;
    use super::bigdigit::alignment::BigDigitSplitter;
    use super::bigdigit::alignment::BigDigitSliceSplitterIter;
    type R = RADIX_10p19_u64;

    let radix = R::RADIX as u64;

    if a.len() < b.len() {
        // ensure a is the longer of the two digit slices
        return multiply_slices_with_prec_into_p19(dest, b, a, prec, rounding);
    }

    debug_assert_ne!(a.len(), 0);
    debug_assert_ne!(b.len(), 0);
    debug_assert_ne!(a.digits.first().unwrap(), &0);
    debug_assert_ne!(b.digits.first().unwrap(), &0);

    let WithScale { value: dest, scale: result_scale } = dest;

    // we need at least this many bigdigits to resolve 'prec' base-10 digits
    // let a_digit_count = a.count_decimal_digits();
    // let b_digit_count = b.count_decimal_digits();
    // let product_digit_count = a_digit_count + b_digit_count;

    // minimum possible length of each integer, given length of bigdigit vecs
    let pessimistic_product_digit_count = (a.len() + b.len() - 2) * R::DIGITS + 1;

    // require more digits of precision for overflow and rounding
    // max number of digits produced by adding all bigdigits at any
    // particular "digit-index" i of the product
    //  log10( Σ a_m × b_n (∀ m+n=i) )
    let max_digit_sum_width = (2.0 * (R::max() as f32).log10() + (b.len() as f32).log10()).ceil() as usize;
    let max_bigdigit_sum_width = max_digit_sum_width.div_ceil(RADIX_10p19_u64::DIGITS);
    // the "index" of the product which could affect the significant results
    let bigdigits_to_skip = pessimistic_product_digit_count
                                .saturating_sub(prec.get() as usize + 1)
                                .div_ceil(RADIX_10p19_u64::DIGITS)
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
    let max_sigproduct_bigdigit_count =
        (a_sig_digit_count + b_sig_digit_count + 1).div_ceil(RADIX_10p19_u64::DIGITS);
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
    let trailing_zeros = new_handle_insignificant_overflow(
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
        todo!()
    }

    *dest = product;
}

/// Store `a * b` into dest, to limited precision
pub(crate) fn multiply_slices_with_prec_into(
    dest: &mut WithScale<BigDigitVec>,
    a: BigDigitSlice,
    b: BigDigitSlice,
    prec: NonZeroU64,
    rounding: NonDigitRoundingData,
) {
    let a_base10: BigDigitVecP19 = a.into();
    let b_base10: BigDigitVecP19 = b.into();

    let mut product = Default::default();
    multiply_slices_with_prec_into_p19(
        &mut product,
        a_base10.as_digit_slice(),
        b_base10.as_digit_slice(),
        prec,
        rounding,
    );

    let WithScale { value: product_digits, scale: result_scale } = product;

    dest.scale = result_scale;
    dest.value = product_digits.into();
}

/// do calculation to determine if insignificant digits of 'a * b' are all zero
/// (used when rounding)
///
/// a * b has already been multiplied from the
///
#[allow(unused_variables)]
fn check_trailing_zeros(
    trailing: &[u8],
    a: BigDigitSlice,
    a_prec: usize,
    b: BigDigitSlice,
    b_prec: usize,
) -> bool {
    // classify as insignificant and significant big-digit slices
    let (a_insig, a_sig) = a.digits.split_at(a_prec);
    let (b_insig, b_sig) = b.digits.split_at(b_prec);

    // location of first non-zero digit
    let a_fnz = a_insig.iter().position(|&d| d != 0).unwrap_or(a_insig.len());
    let b_fnz = b_insig.iter().position(|&d| d != 0).unwrap_or(b_insig.len());

    // trim trailing zeros
    let (_, a_insig) = a_insig.split_at(a_fnz);
    let (_, b_insig) = b_insig.split_at(b_fnz);

    match (a_insig.is_empty(), b_insig.is_empty()) {
        (true, true) => {
            // there is nothing left to multiply, just go by insignificant digits
            return trailing.iter().all(|&d| d == 0);
        }
        (false, false) => {}
        _ => todo!(),
    }

    // product at zero
    let p0 = a_insig[0] * b_insig[0];
    dbg!(p0);

    todo!();
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
