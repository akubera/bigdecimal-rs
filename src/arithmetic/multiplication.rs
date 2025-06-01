//! Routines for multiplying numbers
//!
#![allow(dead_code)]

use stdlib::num::NonZeroU64;
use num_traits::AsPrimitive;

use crate::*;
use crate::rounding::NonDigitRoundingData;

use crate::bigdigit::{
    radix::{RadixType, RADIX_u64, RADIX_10_u8},
    endian::{Endianness, LittleEndian, BigEndian},
    digitvec::{DigitVec, DigitSlice},
};

type BigDigitVec = DigitVec<RADIX_u64, LittleEndian>;
type BigDigitVecBe = DigitVec<RADIX_u64, BigEndian>;
type BigDigitSlice<'a> = DigitSlice<'a, RADIX_u64, LittleEndian>;

type SmallDigitVec = DigitVec<RADIX_10_u8, LittleEndian>;


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

pub(crate) fn multiply_at_idx_into<R: RadixType>(
    dest: &mut DigitVec<R, LittleEndian>,
    a: DigitSlice<R, LittleEndian>,
    b: DigitSlice<R, LittleEndian>,
    idx: usize,
) {
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

    let a_vec: BigDigitVec = a.magnitude().into();
    let b_vec: BigDigitVec = b.magnitude().into();

    let mut digit_vec_scale = WithScale::default();
    multiply_slices_with_prec_into(
        &mut digit_vec_scale,
        a_vec.as_digit_slice(),
        b_vec.as_digit_slice(),
        ctx.precision(),
        rounding_data
    );

    WithScale {
        scale: -digit_vec_scale.scale,
        value: digit_vec_scale.value.into_bigint(sign),
    }
}

/// Store `a * b` into dest, to limited precision
pub(crate) fn multiply_slices_with_prec_into(
    dest: &mut WithScale<BigDigitVec>,
    a: BigDigitSlice,
    b: BigDigitSlice,
    prec: NonZeroU64,
    rounding: NonDigitRoundingData
) {
    if a.len() < b.len() {
        // ensure a is the longer of the two digit slices
        return multiply_slices_with_prec_into(dest, b, a, prec, rounding);
    }
    debug_assert_ne!(a.len(), 0);
    debug_assert_ne!(b.len(), 0);

    // expand 'result' into separate variables
    let WithScale { value: dest, scale: trimmed_digits } = dest;

    // we need at least this many bigdigits to resolve 'prec' base-10 digits
    let min_bit_count = prec.get() as f64 * LOG2_10;
    let min_bigdigit_count = (min_bit_count / 64.0).ceil() as usize;

    // require two extra big digits, for carry safety/rounding
    let requested_bigdigit_count = min_bigdigit_count + 2;

    // maximum number of big-digits in the output
    let product_bigdigit_count = a.len() + b.len();

    let a_start;
    let b_start;
    let bigdigits_to_trim = product_bigdigit_count.saturating_sub(requested_bigdigit_count);
    if bigdigits_to_trim == 0 {
        // we've requested more digits than we have, use the whole thing
        a_start = 0;
        b_start = 0;
    } else {
        // product has fewer digits than the result requires: skip some
        // the least significant bigdigits in a and b
        a_start = bigdigits_to_trim.saturating_sub(b.len() - 1);
        b_start = b.len().saturating_sub(requested_bigdigit_count);
    };

    // only multiply the relevant significant digits
    let a_sig = a.trim_insignificant(a_start);
    let b_sig = b.trim_insignificant(b_start);
    debug_assert_ne!(a_sig.len(), 0);
    debug_assert_ne!(b_sig.len(), 0);

    // fill dest with as many zeros as we will need
    dest.clear();
    dest.resize(a_sig.len() + b_sig.len());

    // perform dest = a_sig * b_sig
    multiply_at_idx_into(dest, a_sig, b_sig, 0);

    // number of ignorable bigdigits in dest
    let dest_insig_count = dest.len().saturating_sub(requested_bigdigit_count);

    // TODO: don't rely on bigint to do the shifting
    let mut int = BigUint::from(&*dest);
    int <<= (bigdigits_to_trim - dest_insig_count) * 64;

    // split shifted integer into base-10 digits
    let mut int_digits = SmallDigitVec::from(&int);

    // round the shifted digits
    let (rounded_int_digits, trimmed_digit_count) = int_digits.round_at_prec_inplace(prec, rounding);
    debug_assert!(
        rounded_int_digits.len() == prec.get() as usize
        || (trimmed_digit_count == 0 && rounded_int_digits.len() < prec.get() as usize));

    // fill dest with rounded digits
    rounded_int_digits.fill_vec_u64(dest);
    *trimmed_digits -= trimmed_digit_count as i64;
}


/// split u64 into high and low bits
fn split_u64(x: u64) -> (u64, u64) {
    x.div_rem(&(1<<32))
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
    a: u64,
    b: u64,
    z: u64,
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
