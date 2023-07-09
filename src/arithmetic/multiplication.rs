//! Routines for multiplying numbers
//!
#![allow(dead_code)]

use num_integer::Integer;
use num_traits::AsPrimitive;
use crate::stdlib;

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

/// square multiply 1
pub(crate) fn _multiply_1_u64_into_u32(dest: &mut [u32], mut idx: usize, a: u64) {
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
    dest: &mut [u32], mut idx: usize, a: u64, b: u64
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
    dest: &mut [u32], mut idx: usize, a: u64, b: u64, z: u64
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


pub(crate) fn multiply_thrup_spread_into(dest: &mut [u32], idx0: usize, a: u32, b: u32, z: u32) {
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


pub(crate) fn multiply_thrup_spread_into_wrapped(dest: &mut [u32], idx0: usize, a: u32, b: u32, z: u32) {
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
    z: u32
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
        carry = c as u64;
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
    dbg!(wrap, idx);

    idx = (idx + 1) % wrap;
    let (mut carry, r3) = split_u64(dest[idx] as u64 + carry + bzh * 2);
    dest[idx] = r3 as u32;

    while carry != 0 {
        idx = (idx + 1) % wrap;
        let (c, overflow) = split_u64(dest[idx] as u64 + carry);
        dest[idx] = overflow as u32;
        carry = c as u64;
    }
}

#[cfg(test)]
mod test_multiply_quad_spread_into {
    use super::*;

    #[test]
    fn case_25597123371_684026673_1163340730_1823138616() {
        let a = 2559712337;
        let b = 684026673;
        let y = 1163340730;
        let z = 1823138616;

        let mut result = vec![0; 8];

        multiply_quad_spread_into(&mut result, 2, a, b, y, z);
        assert_eq!(&result, &[0, 0, 3001179060, 4203670869, 1059648540, 580714756, 0, 0]);
    }

    #[test]
    fn case_25597123371_684026673_1163340730_1823138616_wrapping() {
        let a = 2559712337;
        let b = 684026673;
        let y = 1163340730;
        let z = 1823138616;

        let mut result = vec![0; 8];

        multiply_quad_spread_into_wrapping(&mut result, 6, a, b, y, z);
        assert_eq!(&result, &[1059648540, 580714756, 0, 0, 0, 0, 3001179060, 4203670869]);
    }

    #[test]
    fn case_4294967296() {
        let a = 4294967295;
        let b = 4294967295;
        let y = 4294967295;
        let z = 4294967295;

        let mut result = vec![0; 6];

        multiply_quad_spread_into(&mut result, 1, a, b, y, z);
        assert_eq!(&result, &[0, 2, 0, 4294967292, 4294967295, 1]);
    }
}
