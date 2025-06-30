//! Routines for multiplying numbers
//!
#![allow(dead_code)]
#![allow(unreachable_code)]
#![allow(unused_variables)]

use num_traits::AsPrimitive;

use stdlib::num::NonZeroU64;

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
    dest.scale = a.scale + b.scale + digit_vec_scale.scale;
}


pub(crate) fn multiply_at_idx_into<R: RadixType>(
    dest: &mut DigitVec<R, LittleEndian>,
    a: DigitSlice<R, LittleEndian>,
    b: DigitSlice<R, LittleEndian>,
    idx: usize,
) {
    dbg!(&a);
    dbg!(&b);
    debug_assert!(dbg!(a.len()) + dbg!(b.len()) <= dbg!(dest.len()) + dbg!(idx));
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

    // minimum possible length of each digit, given length of bigdigit vecs
    let min_a_digit_count = (a.len() - 1) * R::DIGITS + 1;
    let min_b_digit_count = (b.len() - 1) * R::DIGITS + 1;
    let pessimistic_product_digit_count = min_a_digit_count + min_b_digit_count;

    // require more digits of precision for overflow and rounding
    // max number of digits produced by adding all bigdigits at any
    // particular "digit-index" i of the product
    //  log10( Σ a_m × b_n (∀ m+n=i) )
    let max_digit_sum_width = (2.0 * (R::max() as f32).log10() + (b.len() as f32).log10()).ceil() as usize;
    let bigdigits_to_trim = pessimistic_product_digit_count
                                .saturating_sub(prec.get() as usize + 1)
                                .div_ceil(RADIX_10p19_u64::DIGITS)
                                .saturating_sub(max_digit_sum_width.div_ceil(RADIX_10p19_u64::DIGITS));

    let a_start;
    let b_start;
    if bigdigits_to_trim == 0 {
        // we've requested more digits than product will produce, don't trim any digits
        a_start = 0;
        b_start = 0;
    } else {
        // the idexes of the least significant bigdigits in a and b which may contribute
        // to the significant digits in the product
        a_start = bigdigits_to_trim.saturating_sub(b.len());
        b_start = bigdigits_to_trim.saturating_sub(a.len());
    }

    *result_scale -= (R::DIGITS * (a_start + b_start)) as i64;

    let a_sig = a.trim_insignificant(a_start);
    let b_sig = b.trim_insignificant(b_start);

    let a_sig_digit_count = a_sig.count_decimal_digits();
    let b_sig_digit_count = b_sig.count_decimal_digits();

    let mut product = BigDigitVecP19::new();
    product.resize((a_sig_digit_count + b_sig_digit_count + 1).div_ceil(RADIX_10p19_u64::DIGITS) + 1);
    multiply_at_idx_into(&mut product, a_sig, b_sig, 0);
    product.remove_leading_zeros();

    let product_digit_count = product.count_decimal_digits();
    debug_assert!(a_sig_digit_count + b_sig_digit_count - product_digit_count <= 1);
    dbg!(pessimistic_product_digit_count, product_digit_count + (R::DIGITS * bigdigits_to_trim));
    // debug_assert!(pessimistic_product_digit_count <= product_digit_count + (R::DIGITS * bigdigits_to_trim));

    let insignificant_product_is_zero = || {
        a.digits.iter().take(a_start).all(Zero::is_zero)
        && b.digits.iter().take(b_start).all(Zero::is_zero)
    };

    let digits_to_remove = product_digit_count.saturating_sub(prec.get() as usize);
    if digits_to_remove == 0 {
        debug_assert_eq!(a_start, 0);
        debug_assert_eq!(b_start, 0);

        // no need to trim the results, everything was significant;
        *dest = product;
        return;
    }

    // shifting the scale to the left
    *result_scale -= digits_to_remove as i64;

    // count number of bigdigits and digits are left
    let (insig_bd_count, insig_d_count) = digits_to_remove.div_rem(&RADIX_10p19_u64::DIGITS);

    let insig_rounding_data;
    if insig_d_count == 0 {
        debug_assert_ne!(insig_bd_count, 0);

        // we are rounding on a big-digit boundary
        let shifter = ten_to_the_u64((RADIX_10p19_u64::DIGITS - 1) as u8);
        let (insig_digit, insig_digits) = product.digits.get(insig_bd_count - 1)
                                                        .copied()
                                                        .unwrap_or(0)
                                                        .div_rem(&shifter);
        insig_rounding_data = InsigData::from_digit_and_lazy_trailing_zeros(
                rounding, insig_digit as u8, || {
                    insig_digits == 0 && insignificant_product_is_zero()
                // && product.digits[..bigdigits_to_remove - 1].iter().all(|&d| d == 0)
            });

        let sig_digit = product.digits[insig_bd_count] % 10;
        let rounded_digit = insig_rounding_data.round_digit(sig_digit as u8);

        dest.digits.push(product.digits[insig_bd_count] - sig_digit + rounded_digit as u64);
        if dest.digits[0] < radix {
            dest.digits.extend_from_slice(&product.digits[insig_bd_count + 1..]);
            return;
        }

        // handle overflow case
        dest.digits[0] -= RADIX_10p19_u64::RADIX as u64;

        if let Some(pos) = product.digits.iter().skip(insig_bd_count).position(|&d| d < radix) {
            let d = product.digits[pos + insig_bd_count + 1] + 1;
            dest.digits.resize(1 + pos, 0);
            dest.digits.push(d);
            dest.digits.extend_from_slice(&product.digits[insig_bd_count + pos + 2..]);
            return;
        }

        todo!("NEEDS TESTS");
        dest.digits.resize(1 + product.digits.len() - insig_bd_count, 0);

        // if dest.digits[0] >= R::RADIX as u64 {
        // }
    } else {
        // let (sig, insig) = product.digits.split_at(insig_bd_count);
        let mut splitter = BigDigitSliceSplitterIter::<R>::from_slice_starting_bottom(
            &product.digits[insig_bd_count..],
            dbg!(insig_d_count),
        );

        let insig_bigdigit = splitter.next().unwrap();
        let top_digit_splitter = BigDigitSplitter::<R>::mask_high(1);
        let (insig_digit, insig_trailing) = top_digit_splitter.div_rem(insig_bigdigit);

        insig_rounding_data =
            InsigData::from_digit_and_lazy_trailing_zeros(rounding, insig_digit as u8, || {
                insig_trailing == 0
                    && product.digits[..insig_bd_count].iter().all(Zero::is_zero)
                    && insignificant_product_is_zero()
            });

        let bigdigit = splitter.next().unwrap();
        let sig_digit0 = bigdigit % 10;
        let rounded_digit = insig_rounding_data.round_digit(sig_digit0 as u8);
        let r0 = bigdigit - sig_digit0 + rounded_digit as u64;

        let shifted_r0 = u128::from(r0).wrapping_sub(R::RADIX);

        // shifted_r0 is greater than RADIX if subtraction
        // wrapped around, meaning there was no carry
        if shifted_r0 >= R::RADIX {
            dest.digits.push(r0);
            dest.digits.extend(splitter);
            return;
        }
        dest.digits.push(shifted_r0 as u64);
        loop {
            match splitter.next() {
                None => {
                    break;
                }
                Some(d) if d == R::max() => {
                    dest.digits.push(0);
                }
                Some(d) => {
                    debug_assert!(d as u128 + 1 < R::RADIX);
                    dest.digits.push(d + 1);
                    dest.digits.extend(splitter);
                    return;
                }
            }
        }
    }
    // dest.extend_adding_with_carry(splitter, &mut carry);
    todo!("handle overflow");
    return;

    // match dbg!(product_digit_count).saturating_sub(prec.get() as usize) {
    //     0 => {
    //         debug_assert_eq!(a_start, 0);
    //         debug_assert_eq!(b_start, 0);

    //         todo!("needs test");
    //         // no need to trim the results, we're done
    //         return;
    //     }
    //     // we are rounding on a big-digit boundary
    //     digits_to_remove if digits_to_remove % RADIX_10p19_u64::DIGITS == 0 => {
    //         debug_assert_ne!(dbg!(digits_to_remove), 0);
    //         let bigdigits_to_remove = digits_to_remove / RADIX_10p19_u64::DIGITS;
    //         debug_assert_ne!(bigdigits_to_remove, 0);

    //         *result_scale += dbg!(digits_to_remove) as i64;

    //         // if digits_to_remove == 0 {
    //             // InsigData::from_digit_and_lazy_trailing_zeros(rounding 0, 0);
    //         // } else {
    //         // };

    //         dest.digits.push(product.digits[bigdigits_to_remove] - sig_digit + rounded_digit as u64);
    //         if dest.digits[0] < RADIX_10p19_u64::RADIX as u64 {
    //             dest.digits.extend_from_slice(&product.digits[bigdigits_to_remove + 1..]);
    //             // dest.digits.copy_within(bigdigits_to_remove + 1.., 1);
    //             // dest.digits.truncate(dest.digits.len() - bigdigits_to_remove);
    //             return;
    //         }

    //         // handle overflow case
    //         dest.digits[0] -= RADIX_10p19_u64::RADIX as u64;
    //         // dest.digits[bigdigits_to_remove]

    //         todo!();
    //     }
    //     digits_to_remove => {
    //         use super::bigdigit::alignment::BigDigitSplitter;
    //         use super::bigdigit::alignment::BigDigitSliceSplitterIter;
    //         type R = RADIX_10p19_u64;

    //         dbg!(&result_scale);
    //         *result_scale += dbg!(digits_to_remove) as i64;
    //         dbg!(result_scale);
    //         todo!();

    //         let (bigdigits_to_remove, digits_to_remove) = digits_to_remove.div_rem(&RADIX_10p19_u64::DIGITS);
    //         debug_assert_ne!(digits_to_remove, 0);

    //         let mut splitter = BigDigitSliceSplitterIter::<R>::from_slice_starting_bottom(
    //             &product.digits[bigdigits_to_remove..], digits_to_remove
    //         );

    //         let insig_bigdigit = splitter.next().unwrap();
    //         let top_digit_splitter = BigDigitSplitter::<R>::mask_high(1);
    //         let (insig_digit, insig_trailing) = top_digit_splitter.div_rem(insig_bigdigit);

    //         let insig_rounding_data = InsigData::from_digit_and_lazy_trailing_zeros(
    //             rounding, insig_digit as u8, || {
    //                 insig_trailing == 0 && product.digits[..bigdigits_to_remove].iter().all(Zero::is_zero)
    //             }
    //         );

    //         let bigdigit = splitter.next().unwrap();
    //         let sig_digit0 = bigdigit % 10;
    //         let rounded_digit = insig_rounding_data.round_digit(sig_digit0 as u8);
    //         let r0 = bigdigit - sig_digit0 + rounded_digit as u64;

    //         let shifted_r0 = u128::from(r0).wrapping_sub(R::RADIX);

    //         // shifted_r0 is greater than RADIX if subtraction
    //         // wrapped around, meaning there was no carry
    //         if shifted_r0 >= R::RADIX {
    //             dest.digits.push(r0);
    //             dest.digits.extend(splitter);
    //             dbg!(&dest.digits);
    //             return;
    //         }

    //         dest.digits.push(shifted_r0.as_());
    //         while let Some(next_digit) = splitter.next() {
    //             if R::is_max(next_digit) {
    //                 dest.digits.push(0);
    //                 continue;
    //             }
    //             dest.digits.push(next_digit + 1);
    //             dest.digits.extend(splitter);
    //             return;
    //         }

    //         // handle overflow :-(
    //         todo!("HANDLE OVERFLOW");

    //         // let boundary_digit = dest.digits[bigdigits_to_remove as usize];
    //         // let (shifted_boundary_digit, insig_digits) = boundary_digit.div_rem(&shifter);

    //         // dbg!(shifted_boundary_digit);
    //         // let (sig_digits, insig_digit)  = shifted_boundary_digit.div_rem(&10);

    //         // let rounding_data = InsigData::from_digit_and_lazy_trailing_zeros(
    //         //     rounding, insig_digit as u8, || {
    //         //         insig_digits == 0 && dest.digits[..bigdigits_to_remove].iter().all(|&d| d == 0)
    //         //     }
    //         // );

    //         // let sig_digit = sig_digits % 10;
    //         // let rounded_digit = rounding_data.round_digit(sig_digit as u8);
    //         // dest.digits[0] = sig_digits - sig_digit as u64 + rounded_digit as u64;
    //         // let mut carry = 0;

    //         // for i in 1.. {
    //         //     let (hi, lo) = bigdigits_to_remove+i
    //         // }

    //     //     if dest[0] < RADIX_10p19_u64::RADIX {
    //     //         dest.copy_within(.., 1);
    //     //     }

    //     //     if dest[0] >= RADIX_10p19_u64::RADIX {
    //     //         // match dest.digits.iter().skip(bigdigits_to_remove + 1).pos(|&d| d != RADIX_10p19_u64::RADIX - 1) {
    //     //         //     Some(pox
    //     //         // }
    //     //         // carry = 1;
    //     //         // dest[0] -= RADIX_10p19_u64::RADIX;
    //     //         todo!();
    //     //    }
    //         todo!();
    //     }
    // }

    // let digits_removed = dest.round_at_prec_inplace(prec);
    // *trimmed_digits += digits_removed;
    // todo!();

    // dbg!(prec.get());
    // let (full_count, partial_count) = div_rem(prec.get(), 19);
    // dbg!(full_count, partial_count);
    // use num_integer::div_rem;
    // use crate::arithmetic::decimal::count_digits_u64;

    // let insig_data = InsigData::from_digit_and_lazy_trailing_zeros(rounding, insig_digit, || {
    //     check_trailing_zeros(trailing, a, a.len() - a_sig.len(), b, b.len() - b_sig.len())
    // });

    // let digits_removed = dest.digits.round_at_prec_inplace(prec, rounding);
    // dest.scale -= digits_removed;

    // let (&sig_digit, b) = dest.digits.split_last().unwrap();
    // let top_digit_cout = count_digits_u64(sig_digit) as u64;
    // match top_digit_count.checked_sub(partial_count) {
    //     Some(digits_to_remove) => {
    //         dbg!(digits_to_remove);
    //         let shifter = ten_to_the_u64(digits_to_remove as u8);
    //         dbg!(shifter);
    //         dbg!(top_digit_count);
    //         dbg!(sig_digit / digits_to_remove);
    //     }
    //     None => {
    //     }
    // }
    // // if top_digit_count < partial_count as usize {
    // //     dbg!(partial_count - top_digit_count);
    // // }
    // dbg!(top_digit_count);

    // let ab = (a_sig.digits[0] as u128) * (b_sig.digits[0] as u128);
    // let (carry, y) = div_rem(ab, RADIX_10p19_u64::RADIX);
    // dbg!(carry, y);

    // let z = (a_sig.digits[1] as u128) * (b_sig.digits[0] as u128) + carry;
    // let (carry, y) = div_rem(z, RADIX_10p19_u64::RADIX);
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
    [(n >> 0).as_(), (n >> 32).as_(), (n >> 64).as_(), (n >> 96).as_()]
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
pub(crate) fn multiply_2_u64_into_u32(dest: &mut [u32], mut idx: usize, a: u64, b: u64) {
    let [aa0, aa1, aa2, aa3] = mul_split_u64_u64(a, a);
    let [ab0, ab1, ab2, ab3] = mul_split_u64_u64(a, b);
    let [bb0, bb1, bb2, bb3] = mul_split_u64_u64(b, b);

    let (carry, r0) = split_u64(dest[idx] as u64 + aa0 as u64);
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
    let (carry, r4) = split_u64(dest[idx] as u64 + carry + ab2 as u64 * 2 + bb0 as u64);
    dest[idx] = r4 as u32;

    idx += 1;
    let (carry, r5) = split_u64(dest[idx] as u64 + carry + ab3 as u64 * 2 + bb1 as u64);
    dest[idx] = r5 as u32;

    idx += 1;
    let (carry, r6) = split_u64(dest[idx] as u64 + carry + bb2 as u64);
    dest[idx] = r6 as u32;

    idx += 1;
    let (carry, r7) = split_u64(dest[idx] as u64 + carry + bb3 as u64);
    dest[idx] = r7 as u32;

    _apply_carry_u64(dest, idx + 1, carry);
}

/// dest += ((b<<64) + a) * ((z<<64) + y)
pub(crate) fn _multiply_into_4_u64(dest: &mut [u32], idx: usize, a: u64, b: u64, y: u64, z: u64) {
    let [ay0, ay1, ay2, ay3] = mul_split_u64_u64(a, y);
    let [az0, az1, az2, az3] = mul_split_u64_u64(a, z);
    let [by0, by1, by2, by3] = mul_split_u64_u64(b, y);
    let [bz0, bz1, bz2, bz3] = mul_split_u64_u64(b, z);

    let (carry, r0) = split_u64(dest[idx + 0] as u64 + (ay0 as u64) * 2);
    dest[idx + 0] = r0 as u32;

    let (carry, r1) = split_u64(dest[idx + 1] as u64 + carry + (ay1 as u64) * 2);
    dest[idx + 1] = r1 as u32;

    let (carry, r2) =
        split_u64(dest[idx + 2] as u64 + carry + (ay2 as u64 + az0 as u64 + by0 as u64) * 2);
    dest[idx + 2] = r2 as u32;

    let (carry, r3) =
        split_u64(dest[idx + 3] as u64 + carry + (ay3 as u64 + az1 as u64 + by1 as u64) * 2);
    dest[idx + 3] = r3 as u32;

    let (carry, r4) =
        split_u64(dest[idx + 4] as u64 + carry + (az2 as u64 + by2 as u64 + bz0 as u64) * 2);
    dest[idx + 4] = r4 as u32;

    let (carry, r5) =
        split_u64(dest[idx + 5] as u64 + carry + (az3 as u64 + by3 as u64 + bz1 as u64) * 2);
    dest[idx + 5] = r5 as u32;

    let (carry, r6) = split_u64(dest[idx + 6] as u64 + carry + (bz2 as u64) * 2);
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
pub(crate) fn _multiply_2_u64_into_u32(dest: &mut [u32], mut idx: usize, a: u64, b: u64) {
    let [aa0, aa1, aa2, aa3] = mul_split_u64_u64(a, a);
    let [ab0, ab1, ab2, ab3] = mul_split_u64_u64(a, b);
    let [bb0, bb1, bb2, bb3] = mul_split_u64_u64(b, b);

    let (carry, r0) = split_u64(dest[idx] as u64 + aa0 as u64);
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
    let (carry, r4) = split_u64(dest[idx] as u64 + carry + ab2 as u64 * 2 + bb0 as u64);
    dest[idx] = r4 as u32;

    idx += 1;
    let (carry, r5) = split_u64(dest[idx] as u64 + carry + ab3 as u64 * 2 + bb1 as u64);
    dest[idx] = r5 as u32;

    idx += 1;
    let (carry, r6) = split_u64(dest[idx] as u64 + carry + bb2 as u64);
    dest[idx] = r6 as u32;

    idx += 1;
    let (carry, r7) = split_u64(dest[idx] as u64 + carry + bb3 as u64);
    dest[idx] = r7 as u32;

    _apply_carry_u64(dest, idx + 1, carry);
}

/// Evaluate z * (a + b << 64) and store in dest at location idx
pub(crate) fn _multiply_3_u64_into_u32(dest: &mut [u32], mut idx: usize, a: u64, b: u64, z: u64) {
    let [az0, az1, az2, az3] = mul_split_u64_u64(a, z);
    let [bz0, bz1, bz2, bz3] = mul_split_u64_u64(b, z);

    let (carry, r0) = split_u64(dest[idx] as u64 + (az0 as u64) * 2);
    dest[idx] = r0 as u32;

    idx += 1;
    let (carry, r1) = split_u64(dest[idx] as u64 + carry + (az1 as u64) * 2);
    dest[idx] = r1 as u32;

    idx += 1;
    let (carry, r2) = split_u64(dest[idx] as u64 + carry + (az2 as u64 + bz0 as u64) * 2);
    dest[idx] = r2 as u32;

    idx += 1;
    let (carry, r3) = split_u64(dest[idx] as u64 + carry + (az3 as u64 + bz1 as u64) * 2);
    dest[idx] = r3 as u32;

    idx += 1;
    let (carry, r4) = split_u64(dest[idx] as u64 + carry + (bz2 as u64) * 2);
    dest[idx] = r4 as u32;

    idx += 1;
    let (carry, r5) = split_u64(dest[idx] as u64 + carry + (bz3 as u64) * 2);
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
mod test {
    use super::*;
    include!("multiplication.tests.rs");
}
