use num_bigint::Sign;
use num_integer::div_rem;
use std::ops::Neg;
use std::cmp::Ordering;

use crate::{
    BigDecimal,
    Context,
    RoundingMode,
};

use crate::bigdigit::{
    MAX_DIGITS_PER_BIGDIGIT,
    BIG_DIGIT_RADIX,
    BIG_DIGIT_RADIX_I64,
    BigDigitBase,
    BigDigitBaseSignedDouble,
    BigDigitVec,
    BigDigitBaseDouble,
    count_digits,
};

/// "lightweight" BigDecimal data
#[derive(Eq, Debug)]
pub(crate) struct DigitInfo {
    pub digits: BigDigitVec,
    pub sign: Sign,
    pub scale: i64,
}

impl PartialEq for DigitInfo {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl PartialOrd for DigitInfo {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for DigitInfo {
    fn cmp(&self, rhs: &DigitInfo) -> std::cmp::Ordering {
        let l_digit_count = count_digits(&self.digits);
        let r_digit_count = count_digits(&rhs.digits);

        let l_int_digits = l_digit_count as i64 + self.scale;
        let r_int_digits = r_digit_count as i64 + rhs.scale;

        let cmp_digits = |ldigits:&[u32], lscale:i64, rdigits: &[u32], rscale:i64| {
            let len_diff = ldigits.len() as i64 - rdigits.len() as i64;

            let digit_diff = len_diff * MAX_DIGITS_PER_BIGDIGIT as i64;
            let scale_diff = lscale - rscale;

            let (r_shift, l_shift) = match (lscale.cmp(&rscale), len_diff >= 0) {
                (Ordering::Equal, _) => {
                    (1, 1)
                },
                (Ordering::Greater, true) => {
                    (1, ten_to_pow!(dbg!(digit_diff + scale_diff)))
                },
                (Ordering::Greater, false) => {
                    (ten_to_pow!(dbg!(-digit_diff - scale_diff)), 1)
                }
                (Ordering::Less, true) => {
                    (ten_to_pow!(dbg!(digit_diff - scale_diff)), 1)
                }
                (Ordering::Less, false) => {
                    unreachable!();
                }
            };

            for (ld, rd) in ldigits.iter().rev().zip(rdigits.iter().rev()) {
                let l_val = ld * l_shift;
                let r_val = rd * r_shift;
                match l_val.cmp(&r_val) {
                    Ordering::Equal => continue,
                    ord => {
                        return ord;
                    }
                };
            }

            return Ordering::Equal;
        };

        match (l_int_digits.cmp(&r_int_digits), self.sign, rhs.sign) {
            (_, Sign::Plus, Sign::Minus) | (_, Sign::Plus, Sign::NoSign) | (_, Sign::NoSign, Sign::Minus) => {
                Ordering::Greater
            },
            (_, Sign::Minus, Sign::Plus) | (_, Sign::NoSign, Sign::Plus) | (_, Sign::Minus, Sign::NoSign)=> {
                Ordering::Less
            },
            (Ordering::Equal, Sign::Plus, Sign::Plus) => {
                cmp_digits(&self.digits, self.scale, &rhs.digits, rhs.scale)
            }
            (Ordering::Equal, Sign::Minus, Sign::Minus) => {
                cmp_digits(&self.digits, self.scale, &rhs.digits, rhs.scale).reverse()
            }
            (ord, Sign::Plus, Sign::Plus) => {
                ord
            },
            (ord, Sign::Minus, Sign::Minus) => {
                ord.reverse()
            },
            (ord, Sign::NoSign, Sign::NoSign) => {
                unimplemented!()
            },
        }
    }
}

#[cfg(test)]
#[allow(non_snake_case)]
mod test_bigint_ord {
    use super::*;

    macro_rules! impl_test {
        ( - [$($a:literal),+] $($rest:tt)* ) => {
            impl_test!( ARGS Sign::Minus; $($a),*; ($($a)*) -> (); NAME case_neg_ ;; $($rest)* );
        };
        ( [$($a:literal),+] $($rest:tt)* ) => {
            impl_test!( ARGS Sign::Plus; $($a),*; ($($a)*) -> (); NAME case_ ;; $($rest)* );
        };
        ( ARGS $a_sign:expr; $($a:literal),* ; ($a0:literal $($ar:literal)*) -> ($($an:literal)*); NAME $($names:expr)* ;; $($rest:tt)*) => {
            impl_test!( ARGS $a_sign; $($a),*; ($($ar)*) -> ($a0 $($an)*); NAME $($names)* ;; $($rest)* );
        };
        ( ARGS $a_sign:expr; $($a:literal),*; () -> ($($an:literal)*); NAME $($names:expr)* ;; E -$a_scale:literal $($rest:tt)*) => {
            impl_test!( ARGS $a_sign; $($a),*; -$a_scale; NAME $($names)* $($an)* E_neg_ $a_scale ;; $($rest)* );
        };
        ( ARGS $a_sign:expr; $($a:literal),*; () -> ($($an:literal)*); NAME $($names:expr)* ;; E $a_scale:literal $($rest:tt)*) => {
            impl_test!( ARGS $a_sign; $($a),*; $a_scale; NAME $($names)* $($an)* E $a_scale ;; $($rest)* );
        };
        ( ARGS $a_sign:expr; $($a:literal),*; $a_scale:literal; NAME $($names:expr)* ;; < $($rest:tt)*) => {
            impl_test!( ARGS $a_sign; $($a),*; $a_scale; < ; NAME $($names)* _lt_ ;; $($rest)* );
        };
        ( ARGS $a_sign:expr; $($a:literal),*; $a_scale:literal; NAME $($names:expr)* ;; == $($rest:tt)*) => {
            impl_test!( ARGS $a_sign; $($a),*; $a_scale; == ; NAME $($names)* _eq_ ;; $($rest)* );
        };
        ( ARGS $a_sign:expr; $($a:literal),*; $a_scale:literal; NAME $($names:expr)* ;; > $($rest:tt)*) => {
            impl_test!( ARGS $a_sign; $($a),*; $a_scale; > ; NAME $($names)* _gt_ ;; $($rest)* );
        };
        ( ARGS $a_sign:expr; $($a:literal),*; $a_scale:literal; $op:tt; NAME $($names:expr)* ;; [$($b:literal),+]  $($rest:tt)*) => {
            impl_test!( ARGS $a_sign; $($a),*; $a_scale; $op; Sign::Plus; $($b),*; ($($b)*)-> (); NAME $($names)* ;; $($rest)* );
        };
        ( ARGS $a_sign:expr; $($a:literal),*; $a_scale:literal; $op:tt; NAME $($names:expr)* ;; - [$($b:literal),+]  $($rest:tt)*) => {
            impl_test!( ARGS $a_sign; $($a),*; $a_scale; $op; Sign::Minus; $($b),*; ($($b)*) -> (); NAME $($names)* neg_ ;; $($rest)* );
        };
        ( ARGS $a_sign:expr; $($a:literal),*; $a_scale:literal; $op:tt; $b_sign:expr; $($b:literal),*; ($b0:literal $($br:literal)*) -> ($($bn:literal)*); NAME $($names:expr)* ;; $($rest:tt)*) => {
            impl_test!( ARGS $a_sign; $($a),*; $a_scale; $op; $b_sign; $($b),*; ($($br)*) -> ($b0 $($bn)*); NAME $($names)* ;; $($rest)* );
        };
        ( ARGS $a_sign:expr; $($a:literal),*; $a_scale:literal; $op:tt; $b_sign:expr; $($b:literal),*; () -> ($($bn:literal)*); NAME $($names:expr)* ;; $($rest:tt)*) => {
            impl_test!( ARGS $a_sign; $($a),*; $a_scale; $op; $b_sign; $($b),*; NAME $($names)* $($bn)* ;; $($rest)* );
        };
        ( ARGS $a_sign:expr; $($a:literal),*; $a_scale:literal; $op:tt; $b_sign:expr; $($b:literal),*; NAME $($names:expr)* ;; E -$b_scale:literal $($rest:tt)*) => {
            impl_test!( ARGS $a_sign; $($a),*; $a_scale; $op; $b_sign; $($b),*; -$b_scale; NAME $($names)* E_neg_ $b_scale ;; $($rest)* );
        };
        ( ARGS $a_sign:expr; $($a:literal),*; $a_scale:literal; $op:tt; $b_sign:expr; $($b:literal),*; NAME $($names:expr)* ;; E $b_scale:literal $($rest:tt)*) => {
            impl_test!( ARGS $a_sign; $($a),*; $a_scale; $op; $b_sign; $($b),*; $b_scale; NAME $($names)* E $b_scale ;; $($rest)* );
        };
        ( ARGS $a_sign:expr; $($a:literal),*; $a_scale:literal; $op:tt; $b_sign:expr; $($b:literal),*; $b_scale:literal; NAME $($names:expr)* ;; $($rest:tt)*) => {
            paste! {
                #[test]
                fn [< $($names)* >]() {
                    let a = DigitInfo {
                        digits: digit_vec![$($a),*],
                        sign: $a_sign,
                        scale: $a_scale,
                    };

                    let b = DigitInfo {
                        digits: digit_vec![$($b),*],
                        sign: $b_sign,
                        scale: $b_scale,
                    };

                    assert!(a $op b);
                }
            }
        };
    }

    impl_test!([123] E 0 < [125] E 0);
    impl_test!(-[123] E 0 < [123] E 0);
    impl_test!([123] E 0 > -[123] E 0);

    impl_test!([123] E 2 > [123] E 0);

    impl_test!([17033, 19077] E 0 < [13341, 20122] E 0);

    impl_test!([115713341, 68220122] E -2 == [115713341, 68220122] E -2);

    impl_test!([3000] E 0 == [3] E 3);
    impl_test!([9] E 9 == [000000000, 9] E 0);
    impl_test!([350036458, 1783004] E -12 < [350036458, 1783005] E -12);
    impl_test!([122371833, 19071706] E -4 > [254662] E -3);
    impl_test!(-[122371833, 19071706] E -4 < [233291] E -30);
    impl_test!([269635621, 1640082] E -13 < [646057227, 467896899, 161899066, 5] E -25);

    /// left-scale < right-scale & left-len < right-len
    // impl_test!([199454801, 754390613, 956632344] E -20 > [905394148, 283440546, 029359101, 1] E -4);

    impl_test!([323447543, 9566] E 11 > [905394148, 283440546, 029359101, 1] E -4);
}

impl From<&DigitInfo> for BigDecimal {
    fn from(digit_info: &DigitInfo) -> Self {
        let v = crate::bigdigit::convert_to_base_u32_vec(&digit_info.digits);
        let int_val = num_bigint::BigInt::new(digit_info.sign, v);
        return BigDecimal {
            int_val: int_val,
            scale: digit_info.scale,
            context: Context::default(),
        };
    }
}

impl From<&BigDecimal> for DigitInfo {
    fn from(decimal: &BigDecimal) -> Self {
        let digits = crate::bigdigit::to_bigdigit_vec(
            decimal.int_val.iter_u64_digits(),
            std::u64::MAX as u128 + 1
        );
        return DigitInfo {
            digits: digits,
            sign: decimal.sign(),
            scale: decimal.scale,
        };
    }
}

impl From<&::num_bigint::BigInt> for DigitInfo {
    fn from(int_value: &::num_bigint::BigInt) -> Self {
        let digits = crate::bigdigit::to_bigdigit_vec(
            int_value.iter_u64_digits(),
            std::u64::MAX as u128 + 1
        );
        return DigitInfo {
            digits: digits,
            sign: int_value.sign(),
            scale: 0,
        };
    }
}


#[cfg(test)]
mod test_digitinfo_tofrom {
    use super::*;
    use std::str::FromStr;

    #[test]
    fn case_193_14() {
        let bigdec = BigDecimal::from_str("193.14").unwrap();
        let digit_info = DigitInfo::from(&bigdec);
        assert_eq!(&digit_info.digits, &[19314]);
        let new_dec = BigDecimal::from(&digit_info);
        assert_eq!(&bigdec, &new_dec);
    }

    #[test]
    fn case_928133_84283472938472383742934() {
        let bigdec = BigDecimal::from_str("-928133.84283472938472383742934").unwrap();
        let digit_info = DigitInfo::from(&bigdec);
        assert_eq!(&digit_info.digits, &[383742934, 472938472, 813384283, 92]);
        let new_dec = BigDecimal::from(&digit_info);
        assert_eq!(&bigdec, &new_dec);
    }
}


#[inline(always)]
fn negate_all_digits(mut v: Vec<i32>) -> Vec<u32> {
    for d in v.iter_mut() {
        debug_assert!(*d < 0);
        *d = d.abs();
    }

    convert_to_base_u32_vec(v)
}

fn convert_to_base_u32_vec(v: Vec<i32>) -> Vec<u32> {
    unsafe {
        debug_assert!(v.iter().all(|&d| d >= 0));
        std::mem::transmute::<Vec<i32>, Vec<u32>>(v)
    }
}

pub(crate) fn subtract_big_decimals(a: &BigDecimal, b: &BigDecimal) -> BigDecimal {
    use Sign::*;

    let a_info = DigitInfo::from(a);
    let b_info = DigitInfo::from(b);

    let mut result = DigitInfo {
        digits: bigdigit_vec![],
        sign: Sign::NoSign,
        scale: 0,
    };

    match (a_info.sign, b_info.sign) {
        (Plus, Plus) | (Minus, Minus) => {
            subtract_into(
                &a_info.digits,
                a_info.scale,
                &b_info.digits,
                b_info.scale,
                &a.context,
                &mut result,
            );
            BigDecimal::from(&result)
        },
        (Plus, Minus) | (Minus, Plus) => {
            crate::arithmetic::addition::add_digit_vecs_into(
                &a_info.digits,
                &b_info.digits,
                &mut result.digits
            );
            result.sign = a_info.sign;
            BigDecimal::from(&result)
        },
        (_, NoSign) => {
            a.clone()
        }
        (NoSign, _) => {
            b.neg()
        }
    }
}

pub(crate) fn subtract_big_numbers(a: &BigDecimal, b: &num_bigint::BigInt) -> BigDecimal {
    let a_vec = BigDigitVec::from(a);
    let b_info = DigitInfo::from(b);

    let mut result = DigitInfo {
        digits: bigdigit_vec![],
        sign: Sign::NoSign,
        scale: 0,
    };

    // subtract_into(
    //     &a_vec,
    //     a.scale,
    //     &b_info.digits,
    //     0,
    //     &a.context,
    //     &mut result,
    // );

    return BigDecimal::from(&result);
}

pub fn subtract_jot_from(
    d: &BigDecimal, ctx: &Context,
) -> BigDecimal {
    let mut result = DigitInfo {
        digits: bigdigit_vec![],
        sign: Sign::NoSign,
        scale: 0,
    };

    let digit_info = DigitInfo::from(d);
    subtract_jot_into(&digit_info, ctx, &mut result);
    return (&result).into();
}

/// Subtract insignificant positive number (close to zero) from a,
/// correctly applying rounding rules
///
pub(crate) fn subtract_jot_into(
    a: &DigitInfo,
    context: &Context,
    result: &mut DigitInfo,
) {
    use Sign::*;
    use RoundingMode::*;
    use std::cmp::Ordering::*;

    let a_digit_count = count_digits(&a.digits);

    let (index, shift_pow) = num_integer::div_mod_floor(
        a_digit_count as i64, context.precision as i64
    );
    dbg!(a_digit_count, context.precision, index, shift_pow + 1);

    let rounding_point_within_digits = a_digit_count > context.precision as usize;
    let rounding_point_on_digit_edge = a_digit_count == context.precision as usize;
    let rounding_point_right_of_all_digits = a_digit_count < context.precision as usize;

    dbg!(rounding_point_within_digits);
    dbg!(rounding_point_on_digit_edge);
    dbg!(rounding_point_right_of_all_digits);

    if rounding_point_within_digits {
        let rounding_point = a_digit_count as u64 - context.precision;
        dbg!(rounding_point);
        let (rounding_index, rounding_offset) = div_rem(rounding_point as usize, MAX_DIGITS_PER_BIGDIGIT as usize);
        dbg!(rounding_index, rounding_offset);

        let rounding_big_digit = a.digits[rounding_index];
        if rounding_offset == 0 {
            unimplemented!();
        } else {
            let trailing_mask = ten_to_pow!(rounding_offset);
            dbg!(trailing_mask);
            let masked_digit = rounding_big_digit % (trailing_mask * 10);
            let (left_digit, trailing_digits) = div_rem(masked_digit, trailing_mask);
            let right_digit = trailing_digits / trailing_mask;
            dbg!(rounding_big_digit, left_digit, right_digit, trailing_digits);

            let all_trailing_zeros = trailing_digits == 0 && a.digits.iter().take(rounding_index).all(|&d| d == 0);
            dbg!(all_trailing_zeros);
            dbg!(left_digit, right_digit, all_trailing_zeros, a.sign, context.rounding_mode);
            match (left_digit, right_digit, all_trailing_zeros, a.sign, context.rounding_mode) {
                (l, _, true, Plus, Floor) | (l, _, true, Plus, Down) => {
                    dbg!(masked_digit);
                    let mut carry = 0;
                    for &d in a.digits.iter().skip(rounding_index) {
                        let (hi, lo) = div_rem(d, trailing_mask as u32);
                        dbg!(hi, lo);
                        result.digits.push(lo * 10 + carry);
                        dbg!(&result.digits);
                        // d.push(hi);
                    }
                    // let digits =
                    // result.digits.extend(a.digits)
                    unimplemented!();
                }
                /*
                (0, r, true) => {
                     crate::context::round_digits( );
                }
                (l, 0, true) => {
                }
                (l, r, true) => {
                }
                (l, r, false) => {
                }
                */
                _ => {
                    unimplemented!();
                }
            }

            if !all_trailing_zeros {
                dbg!("");
            } else if right_digit == 0 {
                dbg!("");
            }
        }
    }


    match (a.sign, context.rounding_mode) {
        (NoSign, _) => { unreachable!() }
        (Plus, Up) | (Plus, Ceiling) => { unimplemented!() }
        (Plus, Down) | (Plus, Floor)  => { unimplemented!() }
        (Plus, HalfDown) | (Plus, HalfUp) | (Plus, HalfEven) => { unimplemented!() }
        (Minus, Up) | (Minus, Floor) => { unimplemented!() }
        (Minus, Down) | (Minus, Ceiling)  => { unimplemented!() }
        (Minus, HalfDown) | (Minus, HalfUp) | (Minus, HalfEven) => { unimplemented!() }
    }


    // dbg!(sign)

    // offset, shift_pow)

    match index.cmp(&(a.digits.len() as i64)) {
        // index within
       Less => {
        let index = index as usize;
        let d =  a.digits[index] % ten_to_pow!(shift_pow);
        dbg!(d);
       }
       Equal => {
          a.digits[0] % 10;
       }
       Greater => {
       }
    }

    if a.digits.iter().all(|&d| d == 0) {
        result.digits = vec![0];
        return;
    }

    // crate::context::get_rounding_digit_pair(&a.digits, );

    dbg!(&a.digits);
    dbg!(&a.scale);

    // find index of first non-zero bigidigt
    let nz_index = a.digits.iter().position(|&d| d != 0).unwrap();

    // count non-trailing-zero big digits
    let nz_digit_count = count_digits(&a.digits[nz_index..]);

    dbg!(nz_index);
    dbg!(nz_digit_count);

    // could be negative - beware casting to usize if prec < nz_digit_count
    let additional_digits_required = context.precision as i64 - nz_digit_count as i64;
    let (new_digit_count, new_digit_offset) = num_integer::div_mod_floor(
    // let (new_digit_count, new_digit_offset) = num_integer::div_rem(
        additional_digits_required, MAX_DIGITS_PER_BIGDIGIT as i64
    );

    dbg!(additional_digits_required);
    dbg!(new_digit_count);
    dbg!(new_digit_offset);

    result.scale = a.scale - additional_digits_required + MAX_DIGITS_PER_BIGDIGIT as i64 * nz_index as i64;
    result.sign = a.sign;

    result.digits.clear();
    dbg!(a.sign, context.rounding_mode, (nz_digit_count as u64).cmp(&context.precision));
    match (a.sign, context.rounding_mode, (nz_digit_count as u64).cmp(&context.precision)) {
        (Plus, Up, Equal) | (Plus, Ceiling, Equal) => {
            result.digits.extend(a.digits.iter().skip(nz_index));
            // result.scale += (MAX_DIGITS_PER_BIGDIGIT * nz_index) as i64;
        }
        (Plus, Down, Equal) | (Plus, Floor, Equal) => {
            result.digits.extend(a.digits.iter().skip(nz_index));
            result.digits[0] -= 1;
            // result.scale += (MAX_DIGITS_PER_BIGDIGIT * nz_index) as i64;
        }
        // (Minus, Floor, Equal) => {
        //     let mut digits = a.digits.iter();

        //     let (mut carry, d_lo) = div_rem(digits.next().unwrap() + 1, BIG_DIGIT_RADIX as BigDigitBase);
        //     result.digits.push(d_lo);

        //     if carry == 0 {
        //         result.digits.extend(digits);
        //     }
        // },
        // (Minus, Up, Equal) |
        // (Minus, Up, Less) |
        // (Minus, Floor, Equal) |
        // (Minus, Floor, Less) => {
        //     let mut digits = a.digits.iter();
        //     dbg!(&digits);
        //     result.digits.extend(digits);
        //     /*
        //     let (mut carry, d_lo) = div_rem(digits.next().unwrap() + 1, BIG_DIGIT_RADIX as BigDigitBase);
        //     result.digits.push(d_lo);
        //     if carry == 0 {
        //     }
        //     */
        // }
        // (Minus, Up, Greater) | (Minus, Floor, Greater) if new_digit_offset == 0 => {
        //     // let mut digits = a.digits.iter().skip(nz_index);
        //     // let mut carry = 1;
        //     // for &digit in digits {
        //     //     let (dhi, dlo) = div_rem(digit, 1);
        //     //     result.digits.push(dlo * 1 + carry);
        //     //     carry = dhi;
        //     // }

        //     // if carry != 0 {
        //     //     result.digits.push(carry);
        //     // }
        // }
        (Minus, Floor, Equal) |
        (Minus, Floor, Less) => {
            if new_digit_offset == 0 {
                // result.digits.push(d0);
                // result.digits.extend(a.digits.iter().skip(nz_index+1));
                unimplemented!();
            } else {
                let (shift, mask) = crate::bigdigit::decimal_shift_and_mask(new_digit_offset as usize);

                let mut digits = a.digits.iter().skip(nz_index);
                let mut carry = 1;
                for &digit in digits {
                    let (dhi, dlo) = div_rem(digit, mask);
                    result.digits.push(dlo * shift + carry);
                    carry = dhi;
                }

                if carry != 0 {
                    result.digits.push(carry);
                }
            }
            // if nz_digit_count + 1 < MAX_DIGITS_PER_BIGDIGITS {
            //     result.digits.push(result.dig)
            // } else {
            // if new_digit_count == 0 {
            //     result.digits.push(1);
            // } else {
            //     result.digits.resize(new_digit_count, 0);
            //     result.digits[0] = 1;
            // }}
            // result
        }
        // (Minus, Floor, Greater) => {
        //     // Greater means we have more digits than precision

        //     let new_digit_count = -(new_digit_count + 1);
        //     dbg!(new_digit_count);

        //     let round_point = a_digit_count - context.precision as usize;
        //     dbg!(round_point);

        //     let (shift, mask) = crate::bigdigit::decimal_shift_and_mask(new_digit_offset as usize);
        //     dbg!(shift);
        //     dbg!(mask);

        //     if a.digits[0] < (BIG_DIGIT_RADIX - 1) as BigDigitBase {
        //         dbg!(&a.digits);

        //         let round_info = crate::context::RoundingInfo::from(&a.digits, round_point);
        //         // let mut carry = round_info.get_rounded_digit(context.rounding_mode, a.sign);
        //         let mut carry = 1;

        //         let next_digit = a.digits[0];
        //         let d0 = a.digits[0] / mask;
        //         // let (d0_hi, d_lo) = div_rem(next_digit, mask);
        //         dbg!(d0);
        //         dbg!(carry);
        //         dbg!(shift);
        //         dbg!(d0 + carry as BigDigitBase);
        //         result.digits.push(d0 + carry as BigDigitBase);
        //     } else {
        //         dbg!(&a.digits);
        //         let round_info = crate::context::RoundingInfo::from(&a.digits, context.precision as usize);
        //         let rounded_digit = round_info.get_rounded_digit(context.rounding_mode, a.sign);
        //         dbg!(rounded_digit);
        //         result.digits.push(rounded_digit as BigDigitBase);
        //     }


        //     // new_digit_count, new_digit_offset
        //     dbg!(&a.digits);


        //     let (d0_hi, d0_lo) = div_rem(a.digits[0] + 1, BIG_DIGIT_RADIX as u32);
        //     dbg!(d0_hi);
        //     dbg!(d0_lo);
        //     //  / mask;

        //     // dbg!(d0 + 1);

        //     result.scale += additional_digits_required;
        //     // result.digits.push(d0 + 1);
        // }
        // (Minus, Floor, Greater) => {
        //     if new_digit_offset == 0 {
        //         // result.digits.push(d0);
        //         // result.digits.extend(a.digits.iter().skip(nz_index+1));
        //         unimplemented!();
        //     } else {
        //         let (shift, mask) = crate::bigdigit::decimal_shift_and_mask(new_digit_offset as usize);
        //     }

        // }
        // (Minus, Up, Greater) => {
        //     let round_point = a_digit_count - context.precision as usize;
        //     dbg!(round_point);

        //     let (skip, offset) = div_rem(round_point, MAX_DIGITS_PER_BIGDIGIT);

        //     let mut digits = a.digits.iter().skip(skip);

        //     let trailing_zero = a.digits.iter().take(skip).all(|&d| d == 0);

        //     let round_info = crate::context::RoundingInfo::from(&a.digits, round_point);
        //     let round_digit = round_info.get_rounded_digit(context.rounding_mode, a.sign) as BigDigitBase;
        //     dbg!(round_digit);

        //     let digit0 = digits.next().unwrap();
        //     dbg!(digit0);
        //     dbg!(result.scale);

        //     if offset == 0 {
        //         let digit0 = digit0 - (digit0 % 10) + round_digit;
        //         dbg!(digit0);
        //         result.digits.push(digit0);
        //         result.digits.extend(digits);
        //     } else {
        //         let (shift, mask) = crate::bigdigit::decimal_shift_and_mask(
        //             offset as usize
        //         );
        //         let digit0_shifted = digit0 / shift;
        //         let mut carry = digit0_shifted - (digit0_shifted % 10) + round_digit;
        //         for &digit in digits {
        //             let (d_hi, d_lo) = div_rem(digit, shift);
        //             result.digits.push(d_lo * mask + carry);
        //             carry = d_hi;
        //         }

        //         if carry != 0 {
        //             result.digits.push(carry);
        //         }
        //     }
        // }
        (_, _, Greater) => {
            let round_point = a_digit_count - context.precision as usize;
            dbg!(round_point);

            let (skip, offset) = div_rem(round_point, MAX_DIGITS_PER_BIGDIGIT);

            let mut digits = a.digits.iter().skip(skip);

            let trailing_zero = a.digits.iter().take(skip).all(|&d| d == 0);

            let round_info = crate::context::RoundingInfo::from(&a.digits, round_point);
            let round_digit = round_info.get_rounded_digit(context.rounding_mode, a.sign) as BigDigitBase;
            dbg!(round_digit);

            let digit0 = digits.next().unwrap();
            dbg!(digit0);
            dbg!(result.scale);

            if offset == 0 {
                let digit0 = digit0 - (digit0 % 10) + round_digit;
                dbg!(digit0);
                result.digits.push(digit0);
                result.digits.extend(digits);
            } else {
                let (shift, mask) = crate::bigdigit::decimal_shift_and_mask(
                    offset as usize
                );
                let digit0_shifted = digit0 / shift;
                let mut carry = digit0_shifted - (digit0_shifted % 10) + round_digit;
                for &digit in digits {
                    let (d_hi, d_lo) = div_rem(digit, shift);
                    result.digits.push(d_lo * mask + carry);
                    carry = d_hi;
                }

                if carry != 0 {
                    result.digits.push(carry);
                }
            }
        }
        (Plus, Down, Less) |
        (Plus, Down, Equal) |
        (Plus, Floor, Less) |
        (Plus, Floor, Equal) => {

            // fill required digits with maximum nines (999999999)
            result.digits.resize(new_digit_count as usize, (BIG_DIGIT_RADIX - 1) as BigDigitBase);

            // decrement first non zero digit to "round-down"
            let d0 = a.digits[nz_index] - 1;

            if new_digit_offset == 0 {
                result.digits.push(d0);
                result.digits.extend(a.digits.iter().skip(nz_index+1));
            } else {
                // examine implementations here
                // https://rust.godbolt.org/z/o8xj1zxbY

                let (shift, mask) = crate::bigdigit::decimal_shift_and_mask(new_digit_offset as usize);

                // init to nine filler for first iteration
                // eg: 100 -> 99, 100000 -> 99999
                let mut carry = shift - 1;

                // closure to push digits into result (mutates carry)
                let mut push_digit = |&next_digit| {
                    let (d_hi, d_lo) = div_rem(next_digit, mask);
                    result.digits.push((d_lo * shift) + carry);
                    carry = d_hi;
                };

                // push d0, then remaining digits
                push_digit(&d0);
                a.digits.iter().skip(nz_index+1).for_each(push_digit);

                if carry != 0 {
                    result.digits.push(carry);
                }
            }
        }
        (Minus, Ceiling, Less) |
        (Minus, Down, Less) |
        (Minus, Floor, Less) |
        (Minus, HalfUp, Less) |
        (Minus, Up, Less)  => {
            if new_digit_offset == 0 {
                result.digits.extend(a.digits.iter().skip(nz_index));
            } else {
                let (shift, mask) = crate::bigdigit::decimal_shift_and_mask(new_digit_offset as usize);

                let mut carry = 0;
                dbg!(shift);
                dbg!(mask);
                for &next_digit in a.digits.iter().skip(nz_index) {
                    let (d_hi, d_lo) = div_rem(next_digit, mask);
                    result.digits.push((d_lo * shift) + carry);
                    carry = d_hi;
                }

                if carry != 0 {
                    result.digits.push(carry);
                }
            }
        }
        (Minus, _, Less) |
        (Minus, _, Equal) |
        (Plus, _, Less) |
        (Plus, _, Equal) |
        (Minus, HalfDown, Less) |
        (Minus, HalfDown, Equal) |
        (Minus, HalfEven, Equal) |
        (Minus, Floor, Equal) |
        (Minus, Floor, Less) |
        (Minus, Up, Equal) |
        (Plus, Up, Less) |
        (Plus, Up, Equal) |
        (Plus, Ceiling, Less) => {
            if new_digit_offset == 0 {
                result.digits.extend(a.digits.iter().skip(nz_index));
            } else {
                let (shift, mask) = crate::bigdigit::decimal_shift_and_mask(new_digit_offset as usize);

                let mut carry = 0;
                for &next_digit in a.digits.iter().skip(nz_index) {
                    let (d_hi, d_lo) = div_rem(next_digit, mask);
                    result.digits.push((d_lo * shift) + carry);
                    carry = d_hi;
                }

                if carry != 0 {
                    result.digits.push(carry);
                }
            }
        }
        (NoSign, _, _) => {
            unreachable!();
        }
        // _ => {
        //     unreachable!();
        // }
    }
}


#[cfg(test)]
#[allow(non_snake_case)]
mod test_subtract_jot {
    use super::*;

    macro_rules! impl_test {
        ( - [$($a:literal),+] $($rest:tt)* ) => {
            impl_test!(name=[case_neg] a=[$($a)* ; Sign::Minus] a_name=[$($a)* ->] :: $($rest)*);
        };
        ( [$($a:literal),+] $($rest:tt)* ) => {
            impl_test!(name=[case] a=[$($a)* ; Sign::Plus] a_name=[$($a)* ->] :: $($rest)*);
        };
            (name=[$($name:expr)*] a=[$($a:tt)+] a_name=[$a0:literal $($ar:literal)* -> $($an:literal)*] :: $($rest:tt)*) => {
                impl_test!(name=[$($name)*] a=[$($a)*] a_name=[$($ar)* -> $a0 $($an)*] :: $($rest)*);
            };
            (name=[$($name:expr)*] a=[$($a:tt)+] a_name=[-> $($an:literal)+] :: $($rest:tt)*) => {
                impl_test!(name=[$($name)* $($an)*] a=[$($a)*] :: $($rest)*);
            };
        (name=[$($name:expr)*] a=[$($a:tt)+] :: E - $a_scale:literal $($rest:tt)*) => {
            impl_test!(name=[$($name)* e_neg $a_scale] a=[$($a)* ; -$a_scale] :: $($rest)*);
        };
        (name=[$($name:expr)*] a=[$($a:tt)+] :: E + $a_scale:literal $($rest:tt)*) => {
            impl_test!(name=[$($name)* e $a_scale] a=[$($a)* ; $a_scale] :: $($rest)*);
        };
        (name=[$($name:expr)*] a=[$($a:tt)+] :: = - $($rest:tt)*) => {
            // ignore the -
            impl_test!(name=[$($name)*] a=[$($a)+] :: = $($rest)*);
        };
        (name=[$($name:expr)*] a=[$($a:tt)+] :: = [$($r:literal),+] E+$r_scale:literal $($rest:tt)*) => {
            impl_test!(name=[$($name)*] a=[$($a)*] r=[$($r)*; $r_scale] :: $($rest)*);
        };
        (name=[$($name:expr)*] a=[$($a:tt)+] :: = [$($r:literal),+] E $r_scale:literal $($rest:tt)*) => {
            impl_test!(name=[$($name)*] a=[$($a)*] r=[$($r)*; $r_scale] :: $($rest)*);
        };
        (name=[$($name:expr)*] a=[$($a:tt)+] r=[$($r:tt)+] :: ; prec=$prec:literal round=$round_mode:expr) => {
            impl_test!(name=[$($name)* _prec_ $prec _round_ $round_mode ] a=[$($a)*] r=[$($r)*] prec=$prec round=$round_mode ;;);
        };
        (name=[$($name:expr)*] a=[$($a:tt)+] r=[$($r:tt)+] prec=$prec:literal round=$round_mode:expr ;;) => {
            paste!{
                #[test]
                fn [< $($name)* >]() {
                    impl_test!(a=[$($a)*] r=[$($r)*] prec=$prec round=RoundingMode::$round_mode)
                }
            }

        };
        (a=[$($a_digits:literal)+ ; $a_sign:path ; $a_scale:literal] r=[$($r_digits:literal)+ ; $r_scale:literal] prec=$prec:literal round=$rounding_mode:expr ) => {{
            let ctx = Context {
                precision: $prec,
                rounding_mode: $rounding_mode,
            };

            let mut result = DigitInfo {
                digits: bigdigit_vec![],
                sign: Sign::NoSign,
                scale: 0,
            };

            let a = DigitInfo {
                digits: digit_vec![$($a_digits),*],
                scale: $a_scale,
                sign: $a_sign,
            };

            subtract_jot_into(
                &a,
                &ctx,
                &mut result
            );

            assert_eq!(&result.digits, &[$($r_digits),*]);
            assert_eq!(result.scale, $r_scale);
            assert_eq!(result.sign, $a_sign);
        }};
    }

    /*
    impl_test!([123456]E-4 = [123455]E-4 ; prec=6 round=Down);
    impl_test!([123456]E-4 = [1234559]E-5 ; prec=7 round=Down);
    impl_test!([123456]E-4 = [12345599]E-6 ; prec=8 round=Down);
    impl_test!([123456]E-4 = [999999999, 123455999]E-16 ; prec=18 round=Down);
    impl_test!([482095363, 15564435]E-7 = [095362999, 564435482, 15]E-10 ; prec=20 round=Down);

    impl_test!([123456]E-4 = [123455]E-4 ; prec=6 round=Floor);

    impl_test!([123456]E-4 = [123456]E-4 ; prec=6 round=Up);
    impl_test!([123456]E-4 = [1234560]E-5 ; prec=7 round=Up);
    impl_test!([123456]E-4 = [234560000, 1]E-8 ; prec=10 round=Up);
    impl_test!([123456]E-4 = [234560000, 1]E-8 ; prec=10 round=Ceiling);

    // impl_test!(-[123456999]E-4 = -[12345700]E-4 ; prec=8 round=Floor);
    // impl_test!(-[123456999]E-4 = -[12345700]E-4 ; prec=8 round=Floor);
    // impl_test!(-[999999999, 99]E-5 = -[10000000]E-1 ; prec=8 round=Floor);

    impl_test!([837502522, 829135874, 224742278, 1]E-15 = [122474227]E+4; prec=9 round=Down);
    impl_test!([837502522, 829135874, 224742278, 1]E-15 = [122474228]E+4; prec=9 round=Up);
    impl_test!([837502522, 829135874, 224742278, 1]E-15 = [742278830, 1224]E+0; prec=13 round=Up);
    impl_test!([837502522, 829135874, 224742278, 1]E-15 = [227882913, 122474]E-2; prec=15 round=Floor);

    impl_test!(-[117715206, 883811998, 4352442]E-23 = -[288381199, 435244]E-13; prec=15 round=Down);
    impl_test!(-[117715206, 883811998, 4352442]E-23 = -[883811998, 4352442]E-14; prec=16 round=Down);
    impl_test!(-[117715206, 883811998, 4352442]E-23 = -[883811999, 4352442]E-14; prec=16 round=Floor);
    impl_test!(-[117715206, 883811998, 4352442]E-23 = -[883811999, 4352442]E-14; prec=16 round=Up);

    impl_test!([000000000, 103592800, 3120462]E-14 = [103592800, 3120462]E-5; prec=16 round=Up);
    impl_test!([000000000, 103592800, 3120462]E-14 = [103592799, 3120462]E-5; prec=16 round=Down);
    impl_test!([000000000, 103592800, 3120462]E-14 = [621035928, 31204]E-3; prec=14 round=HalfDown);
    impl_test!([000000000, 103592800, 3120462]E-14 = [592800000, 120462103, 3]E-8; prec=19 round=Ceiling);

    impl_test!(-[854596516, 540961549, 7]E-2 = -[409615499, 75]E+6; prec=11 round=Up);
    impl_test!(-[854596516, 540961549, 7]E-2 = -[985459652, 754096154]E-1; prec=18 round=Up);
    // impl_test!(-[854596516, 540961549, 7]E-2 = -[854596517, 540961549, 7]E-2; prec=19 round=Up);

    impl_test!(-[317000000, 579965949, 35]E-8 = -[355799660]E+3; prec=9 round=Floor);
    impl_test!(-[317000000, 579965949, 35]E-8 = -[355799660]E+3; prec=9 round=Up);
    impl_test!(-[317000000, 579965949, 35]E-8 = -[355799659]E+3; prec=9 round=Down);
    impl_test!(-[317000000, 579965949, 35]E-8 = -[355799659]E+3; prec=9 round=HalfUp);
    impl_test!(-[317000000, 579965949, 35]E-8 = -[355799659]E+3; prec=9 round=HalfEven);
    impl_test!(-[317000000, 579965949, 35]E-8 = -[355799659]E+3; prec=9 round=Ceiling);

    impl_test!(-[317000000, 579965949, 35]E-8 = -[557996594, 3]E+2; prec=10 round=Down);
    impl_test!(-[317000000, 579965949, 35]E-8 = -[557996595, 3]E+2; prec=10 round=HalfUp);
    impl_test!(-[317000000, 579965949, 35]E-8 = -[557996595, 3]E+2; prec=10 round=HalfEven);
    impl_test!(-[317000000, 579965949, 35]E-8 = -[557996594, 3]E+2; prec=10 round=Ceiling);
    impl_test!(-[317000000, 579965949, 35]E-8 = -[557996595, 3]E+2; prec=10 round=Floor);
    impl_test!(-[317000000, 579965949, 35]E-8 = -[557996595, 3]E+2; prec=10 round=Up);

    impl_test!(-[317000000, 579965949, 35]E-8 = -[579965949, 35]E+1; prec=11 round=Down);
    impl_test!(-[317000000, 579965949, 35]E-8 = -[579965949, 35]E+1; prec=11 round=HalfUp);
    impl_test!(-[317000000, 579965949, 35]E-8 = -[579965949, 35]E+1; prec=11 round=HalfEven);
    impl_test!(-[317000000, 579965949, 35]E-8 = -[579965949, 35]E+1; prec=11 round=Ceiling);
    impl_test!(-[317000000, 579965949, 35]E-8 = -[579965950, 35]E+1; prec=11 round=Floor);
    impl_test!(-[317000000, 579965949, 35]E-8 = -[579965950, 35]E+1; prec=11 round=Up);
    */

    impl_test!([200002000]E-8 = [200002]E-4; prec=6 round=Floor);
    // impl_test!(-[317000000, 579965949, 35]E-8 = -[799659494, 355]E-0; prec=12 round=Floor);
    // impl_test!(-[317000000, 579965949, 35]E-8 = -[493170001, 255799659]E-6; prec=18 round=Floor);
    // // impl_test!(-[317000000, 579965949, 35]E-8 = -[557996594, 3]E+2; prec=10 round=Floor);
    // impl_test!(-[317000000, 579965949, 35]E-8 = -[931700001, 557996594, 3]E-7; prec=19 round=Floor);
    // impl_test!(-[317000000, 579965949, 35]E-8 = -[317000001, 579965949, 35]E-8; prec=20 round=Floor);
    // impl_test!(-[317000000, 579965949, 35]E-8 = -[170000001, 799659493, 355]E-9; prec=21 round=Floor);

    // impl_test!(-[403434392, 508220146, 277568563, 784063985, 776617144, 317903140, 579965949, 35]E-36 = -[508220146, 277568563, 784063985, 776617144, 317903140, 579965949, 35]E-27; prec=75 round=Floor);

    // impl_test!(-[000000000, 854596516, 540961549, 7]E-11 = -[545965161, 409615498, 75]E-3; prec=19 round=Floor);
    // impl_test!(-[854596516, 540961549, 7]E-2 = -[545965161, 409615498, 75]E-3; prec=20 round=Floor);
    // impl_test!(-[854596516, 540961549, 7]E-2 = -[545965161, 409615498, 75]E-3; prec=20 round=Up);
    // impl_test!(-[854596516, 540961549, 7]E-2 = -[545965160, 409615498, 75]E-3; prec=20 round=HalfUp);
    // impl_test!(-[854596516, 540961549, 7]E-2 = -[545965160, 409615498, 75]E-3; prec=20 round=Down);
    // impl_test!(-[854596516, 540961549, 7]E-2 = -[545965160, 409615498, 75]E-3; prec=20 round=Ceiling);

    // impl_test!(-[854596516, 540961549, 7]E-2 = -[459651601, 096154985, 754]E-4; prec=21 round=Up);

    // impl_test!(-[854596516, 540961549, 7]E-2 = -[985459652, 754096154]E-1; prec=12 round=Up);

    // impl_test!([034772202, 292742408, 054200776, 013946389, 1129]E+29 = [1]E+10; prec=1 round=HalfUp);
    // impl_test!([034772202, 292742408, 054200776, 013946389, 1129]E+29 = [2]E+10; prec=1 round=Up);

    // impl_test!([117715206, 883811998, 4352442]E-23 = []E-13; prec=15 round=Floor);
    // impl_test!(-[032881694, 647539724]E-9 = -[240328816, 6475397]E-7; prec=16 round=Down);

    // impl_test!(-[123456]E-4 = -[1234560]E-5 ; prec=6 round=Up);

    // impl_test!([100]E+0 = [9999999]E-5 ; prec=7 round=Down);
    // impl_test!([100000]E+2 = [99999]E-1 ; prec=5 round=Down);

    // impl_test!([100000]E 2 - [4834]E-9 = [100000] E 2; prec=5 round=Up);
    // impl_test!([132194634] E 10 - [599364822, 2005607]E -15 = [132194634] E 10; prec=12);
    // impl_test!([132194634] E 10 - [599364822, 2005607]E -15 = [194633999, 132] E 7; prec=12 round=Down);
    // impl_test!([1]E 100 - [1]E 1 = [1] E 100; prec=8 round=HalfUp);
    // impl_test!(name=[case_ 1] a=1 b=1 a_scale=1 b_scale=1 prec=8);



}


#[inline]
fn subtract_a_small_number(
    a_digits: &[BigDigitBase],
    a_scale: i64,
    b_digits: &[BigDigitBase],
    b_scale: i64,
    context: &Context,
    result: &mut DigitInfo,
) {
    let a_digit_count = count_digits(&a_digits);
    let b_digit_count = count_digits(&b_digits);
    // if b_scale {
    // }

    let a_end_digit_loc = a_scale;
    let b_start_digit_loc = b_digit_count as i64 - b_scale;

    println!("{}", b_start_digit_loc);

    // a_end_digit_loc
    if b_start_digit_loc < context.precision as i64 {
    }

    result.sign = Sign::Plus;

    match context.rounding_mode {
        RoundingMode::Down | RoundingMode::Floor => {
            result.digits.push(a_digits[0] - 1);
            result.scale = a_scale - 1;
        }

        _ => {
            result.digits.extend_from_slice(a_digits);
            result.scale = a_scale;
        }
    }
    // result.sign = Sign::Plus;
    // context.round
    // let new_digits = crate::arithmetic::rounding::round(
    //     a_digits, a_scale, context.precision as i64, context.rounding_mode
    // );
    // swap(result.digits, new_digits);
}

#[cfg(test)]
#[allow(non_snake_case)]
mod test_subtract_a_small_number {
    use super::*;

    macro_rules! impl_test {
        // ( [$($a:literal),+] E - $a_scale:literal - [$($b:literal),+] E - $b_scale:literal ; $($rest:tt)*) => {
        ( [$($a:literal),+] $($rest:tt)* ) => {
            impl_test!(a=$($a)* a_name=($($a)*) -> () :: $($rest)*);
        };
            (a=$($a:literal)+ a_name=($a0:literal $($ar:literal)*) -> ($($an:literal)*) :: $($rest:tt)*) => {
                impl_test!(a=$($a)* a_name=($($ar)*) -> ($a0 $($an)*) :: $($rest)*);
            };
            (a=$($a:literal)+ a_name=() -> ($($an:literal)+) :: $($rest:tt)*) => {
                impl_test!(name=[case_ $($an)*] a=$($a)* :: $($rest)*);
            };
        (name=[$($name:expr)*] a=$($a:literal)+ :: E - $a_scale:literal - [$($b:literal),+] $($rest:tt)*) => {
            impl_test!(name=[$($name)* e_neg $a_scale] a=$($a)* b=$($b)* a_scale=-$a_scale b_name=($($b)*) -> () :: $($rest)*);
        };
        (name=[$($name:expr)*] a=$($a:literal)+ :: E $a_scale:literal - [$($b:literal),+] $($rest:tt)*) => {
            impl_test!(name=[$($name)* e $a_scale]     a=$($a)* b=$($b)*  a_scale=$a_scale b_name=($($b)*) -> () :: $($rest)*);
        };
            (name=[$($name:expr)*] a=$($a:literal)+ b=$($b:literal)* a_scale=$a_scale:literal b_name=($b0:literal $($br:literal)*) -> ($($bn:literal)*) :: $($rest:tt)*) => {
                impl_test!(name=[$($name)*] a=$($a)* b=$($b)* a_scale=$a_scale b_name=($($br)*) -> ($b0 $($bn)*) :: $($rest)*);
            };
            (name=[$($name:expr)*] a=$($a:literal)+ b=$($b:literal)* a_scale=$a_scale:literal b_name=() -> ($($bn:literal)*) :: $($rest:tt)*) => {
                impl_test!(name=[$($name)* __ $($bn)*] a=$($a)* b=$($b)* a_scale=$a_scale :: $($rest)*);
            };
        (name=[$($name:expr)*] a=$($a:literal)+ b=$($b:literal)* a_scale=$a_scale:literal :: E - $b_scale:literal $($rest:tt)*) => {
            impl_test!(name=[$($name)* e_neg $b_scale ] a=$($a)* b=$($b)* a_scale=$a_scale b_scale=-$b_scale :: $($rest)*);
        };
        (name=[$($name:expr)*] a=$($a:literal)+ b=$($b:literal)* a_scale=$a_scale:literal :: E $b_scale:literal $($rest:tt)*) => {
            impl_test!(name=[$($name)* e $b_scale ] a=$($a)* b=$($b)* a_scale=$a_scale b_scale=$b_scale :: $($rest)*);
        };
        (name=[$($name:expr)*] a=$($a:literal)+ b=$($b:literal)* a_scale=$a_scale:literal b_scale=$b_scale:literal :: = [$($c:literal),+] E $c_scale:literal $($rest:tt)*) => {
            impl_test!(name=[$($name)*] a=$($a)* b=$($b)* c=$($c)* a_scale=$a_scale b_scale=$b_scale c_scale=$c_scale :: $($rest)* );

        };
        (name=[$($name:expr)*] a=$($a:literal)+ b=$($b:literal)+ c=$($c:literal)+ a_scale=$a_scale:literal b_scale=$b_scale:literal c_scale=$c_scale:literal :: ; prec=$prec:literal $($rest:tt)*) => {
            impl_test!(name=[$($name)* _prec_ $prec] a=$($a)* b=$($b)* c=$($c)* a_scale=$a_scale b_scale=$b_scale c_scale=$c_scale prec=$prec :: $($rest)* );
        };
        (name=[$($name:expr)*] a=$($a:literal)+ b=$($b:literal)* c=$($c:literal)+ a_scale=$a_scale:literal b_scale=$b_scale:literal c_scale=$c_scale:literal prec=$prec:literal :: ) => {
            impl_test!(name=[$($name)*] a=$($a)* b=$($b)* c=$($c)* a_scale=$a_scale b_scale=$b_scale c_scale=$c_scale prec=$prec :: round=HalfEven);
        };
        (name=[$($name:expr)*] a=$($a:literal)+ b=$($b:literal)* c=$($c:literal)+ a_scale=$a_scale:literal b_scale=$b_scale:literal c_scale=$c_scale:literal prec=$prec:literal :: round=$round_mode:ident) => {
            impl_test!(name=[$($name)* _round_ $round_mode] a=$($a)* b=$($b)* c=$($c)* a_scale=$a_scale b_scale=$b_scale c_scale=$c_scale prec=$prec round=RoundingMode::$round_mode ;; );
        };
        (name=[$($name:expr)*] a=$($a:literal)+ b=$($b:literal)* c=$($c:literal)+ a_scale=$a_scale:literal b_scale=$b_scale:literal c_scale=$c_scale:literal prec=$prec:literal round=$rounding:expr ;; ) => {
            paste!{
                #[test]
                fn [< $($name)* >]() {
                    impl_test!(a=$($a)* b=$($b)* c=$($c)* a_scale=$a_scale b_scale=$b_scale c_scale=$c_scale prec=$prec round=$rounding)
                }
            }

        };
        (a=$($a:literal)+ b=$($b:literal)+ c=$($c:literal)+ a_scale=$a_scale:literal b_scale=$b_scale:literal c_scale=$c_scale:literal prec=$prec:literal round=$round:expr ) => {{

            let ctx = Context {
                precision: $prec,
                rounding_mode: $round,
            };

            let mut result = DigitInfo {
                digits: bigdigit_vec![],
                sign: Sign::NoSign,
                scale: 0,
            };

            subtract_a_small_number(
                &[$($a),*], $a_scale,
                &[$($b),*], $b_scale,
                &ctx,
                &mut result
            );

            assert_eq!(&result.digits, &[$($c),*]);
            assert_eq!(result.scale, $c_scale);
            assert_eq!(result.sign, Sign::Plus);
        }};
    }

    impl_test!([100000]E 2 - [4834]E-9 = [99999] E 1; prec=5 round=Down);
    impl_test!([100000]E 2 - [4834]E-9 = [100000] E 2; prec=5 round=Up);
    impl_test!([132194634] E 10 - [599364822, 2005607]E -15 = [132194634] E 10; prec=12);
    impl_test!([132194634] E 10 - [599364822, 2005607]E -15 = [194633999, 132] E 7; prec=12 round=Down);
    impl_test!([1]E 100 - [1]E 1 = [1] E 100; prec=8 round=HalfUp);
    // impl_test!(name=[case_ 1] a=1 b=1 a_scale=1 b_scale=1 prec=8);



}


/// Subtract a:(digits, scale) - b:(digits, scale) with prec
/// precision and store in result
///
#[inline]
pub(crate) fn subtract_into(
    a_digits: &[BigDigitBase],
    a_scale: i64,
    b_digits: &[BigDigitBase],
    b_scale: i64,
    context: &Context,
    result: &mut DigitInfo,
) {
    let prec = std::num::NonZeroU32::new(context.precision as u32).unwrap();

    let b_digit_count = count_digits(&b_digits);

    if (a_scale - (b_digit_count as i64 - b_scale)) < context.precision as i64 {
        subtract_a_small_number(
            a_digits, a_scale, b_digits, b_scale, context, result
        );
        return;
    }

    if a_scale == b_scale {
        _subtract_aligned_digits(a_digits, b_digits, prec, result);
        result.scale = a_scale;
        return;
    }

    let scale_diff = a_scale - b_scale;
    let delta_scale_abs = scale_diff.abs() as usize;

    dbg!(delta_scale_abs);
    dbg!(scale_diff);

    let (skip, offset) = num_integer::div_rem(delta_scale_abs, MAX_DIGITS_PER_BIGDIGIT);
    match std::num::NonZeroUsize::new(offset) {
        Some(offset) => _subtract_unaligned_digits(a_digits, b_digits, scale_diff, skip, offset, prec, result),
        None => unimplemented!("handle aligned digits?"),
    }

    dbg!(scale_diff);
    dbg!(skip);
    dbg!( offset);

    result.scale = a_scale.min(b_scale);
    result.sign = Sign::Plus;
    return;
    /*

        let a_int_digits = a_digit_count as i64 + a_scale;
        let b_int_digits = b_digit_count as i64 + b_scale;

        if a_int_digits < b_int_digits {
            subtract_into(b_digits, b_scale, a_digits, a_scale, prec, result);
            result.sign = result.sign.neg();
            result.scale = a_scale;
            return;
        }

        match (a_scale.cmp(&b_scale), a_digit_count.cmp(&b_digit_count)) {
            (Ordering::Less, Ordering::Less) => {}
            _ => unimplemented!(),
        }

        dbg!(a_int_digits, b_int_digits);

        let delta_scale = a_scale - b_scale;
        let delta_scale_abs = delta_scale.abs() as u32;
        let mask = to_power_of_ten(delta_scale_abs - 1);
        let shift = mask * 10;

        match delta_scale.cmp(&0) {
            Ordering::Equal => {
                unimplemented!();
            }
            Ordering::Greater => {
                // dbg!(diff);
                let mut carry = false;
                for i in 0..1 {
                    let a_shifted = a_digits[0] as BigDigitBaseDouble * shift as BigDigitBaseDouble;
                    let (a_hi, a_lo) = div_rem(a_shifted, BIG_DIGIT_RADIX);
                    dbg!(a_digits[0], a_hi, a_lo);
                    let diff = a_lo as BigDigitBaseSignedDouble - b_digits[0] as BigDigitBaseSignedDouble;
                    if diff < 0 {
                        result
                            .digits
                            .push(((BIG_DIGIT_RADIX as BigDigitBaseSignedDouble) + diff) as BigDigitBase);
                        carry = true;
                    } else if carry && diff == 0 {
                        result
                            .digits
                            .push(((BIG_DIGIT_RADIX as BigDigitBaseSignedDouble) - 1) as BigDigitBase);
                    } else if carry && diff != 0 {
                        result.digits.push((diff - 1) as BigDigitBase);
                        carry = false;
                    } else {
                        result.digits.push(diff as BigDigitBase);
                    }
                }

                // if a_hi != 0 {
                //     unimplemented!();
                // }
                // if diff > 0 {
                //     result.sign = Sign::Plus;
                //     return;
                // }
                // dbg!(a_hi);
            }
            Ordering::Less => {
                unimplemented!();
            }
        }

        // if a_digits.len() == 1 && b_digits.len() == 1 && delta_scale_abs < MAX_DIGITS_PER_BIGDIGIT as u32 {
        //     let (a_hi, a_lo) = div_rem(a_digits[0], shift);
        //     let a_lo_shift = a_lo * shift;
        //     dbg!(a_lo))
        //     // let (b_hi, b_lo) = div_rem(b_digits[0], shift);
        //     // unimplemented!();
        // }

        let i = 0;

        let (hi, lo) = div_rem(a_digits[i], shift);
        let x = lo * shift;
        dbg!(a_digits[i], x, hi);

        // MAX_DIGITS

        // let scale_a => {
        //     delta_scale
        // };
        // if del   ta_scale

        // let abc = a_int_digits - b_int_digits;
    */
}

#[cfg(test)]
#[allow(non_snake_case)]
mod test_subtract_into {
    use super::*;

    macro_rules! impl_test {
        ( [$($a:literal),+] $($rest:tt)* ) => {
            impl_test!( ARGS $($a),*; ($($a)*) -> (); NAME case__ ;; $($rest)* );
        };
        ( ARGS $($a:literal),*; ($a0:literal $($ar:literal)*) -> ($($an:literal)*); NAME $($names:expr)* ;; $($rest:tt)*) => {
            impl_test!( ARGS $($a),*; ($($ar)*) -> ($a0 $($an)*); NAME $($names)* ;; $($rest)* );
        };
        ( ARGS $($a:literal),*; () -> ($($an:literal)*); NAME $($names:expr)* ;; E -$a_scale:literal $($rest:tt)*) => {
            impl_test!( ARGS $($a),*; -$a_scale; NAME $($names)* $($an)* _e_neg $a_scale ;; $($rest)* );
        };
        ( ARGS $($a:literal),*; () -> ($($an:literal)*); NAME $($names:expr)* ;; E $a_scale:literal $($rest:tt)*) => {
            impl_test!( ARGS $($a),*; $a_scale; NAME $($names)* $($an)* _e $a_scale ;; $($rest)* );
        };
        ( ARGS $($a:literal),*; $a_scale:literal; NAME $($names:expr)* ;; - [$($b:literal),+] $($rest:tt)*) => {
            impl_test!( ARGS $($a),*; $a_scale; $($b),*; ($($b)*) -> (); NAME $($names)* ;; $($rest)* );
        };
        ( ARGS $($a:literal),*; $a_scale:literal; $($b:literal),*; ($b0:literal $($br:literal)*) -> ($($bn:literal)*); NAME $($names:expr)* ;; $($rest:tt)*) => {
            impl_test!( ARGS $($a),*; $a_scale; $($b),*; ($($br)*) -> ($b0 $($bn)*); NAME $($names)* ;; $($rest)* );
        };
        ( ARGS $($a:literal),*; $a_scale:literal; $($b:literal),*; () -> ($($bn:literal)*); NAME $($names:expr)* ;; E -$b_scale:literal $($rest:tt)*) => {
            impl_test!( ARGS $($a),*; $a_scale; $($b),*; -$b_scale; NAME $($names)* __ $($bn)* _e_neg $b_scale ;; $($rest)* );
        };
        ( ARGS $($a:literal),*; $a_scale:literal; $($b:literal),*; () -> ($($bn:literal)*); NAME $($names:expr)* ;; E $b_scale:literal $($rest:tt)*) => {
            impl_test!( ARGS $($a),*; $a_scale; $($b),*; $b_scale; NAME $($names)* __ $($bn)* _e $b_scale ;; $($rest)* );
        };
        ( ARGS $($a:literal),*; $a_scale:literal; $($b:literal),*; $b_scale:literal; NAME $($names:expr)* ;; = - [$($d:literal),*] E $d_scale:literal $($rest:tt)*) => {
            impl_test!( ARGS $($a),*; $a_scale; $($b),*; $b_scale; Sign::Minus; $($d),*; $d_scale; NAME $($names)* ;; $($rest)* );
        };
        ( ARGS $($a:literal),*; $a_scale:literal; $($b:literal),*; $b_scale:literal; NAME $($names:expr)* ;; = [$($d:literal),*] E $d_scale:literal $($rest:tt)*) => {
            impl_test!( ARGS $($a),*; $a_scale; $($b),*; $b_scale; Sign::Plus; $($d),*; $d_scale; NAME $($names)* ;; $($rest)* );
        };
        ( ARGS $($a:literal),+; $a_scale:literal; $($b:literal),+; $b_scale:literal; $sign:expr; $($r:literal),+; $r_scale:literal; NAME $($name:expr)* ;; ) => {
            paste! {
                #[test]
                fn [< $($name)* >]() {
                    impl_test!( IMPL $($a)*; $a_scale; $($b)*; $b_scale; $sign; $($r)*; $r_scale; 19; )
                }
            }
        };
        (IMPL $($a:literal)*; $a_scale:literal; $($b:literal)*; $b_scale:literal; $sign:expr; $($r:literal)*; $rscale:literal; $prec:literal; ) => {{
            let a_digits = [$($a),*];
            let b_digits = [$($b),*];

            let mut output = DigitInfo {
                digits: digit_vec![],
                scale: 0,
                sign: Sign::NoSign,
            };

            $( assert!(($a as i128) < (BIG_DIGIT_RADIX as i128)); )*
            $( assert!(($b as i128) < (BIG_DIGIT_RADIX as i128)); )*
            $( assert!(($r as i128) < (BIG_DIGIT_RADIX as i128)); )*

            let ctx = Context {
                precision: $prec,
                rounding_mode: RoundingMode::HalfEven,
            };

            // std::num::NonZeroU32::new($prec).unwrap()
            // subtract_into(&a_digits, $a_scale, &b_digits, $b_scale, &ctx, &mut output);
            // sub

            dbg!(&output.sign, &output.digits);
            assert_eq!(&output.digits, &[$($r),*]);
            assert_eq!(output.sign, $sign);
            assert_eq!(output.scale, $rscale);
        }};
    }

    impl_test!([123]E 2 - [938]E 0 = -[93677]E 0);
    impl_test!([287]E 0 - [554]E 12 = -[999999713, 553999]E 0);
    impl_test!([719479559]E 2 - [947]E 6 = [710009559]E 2);
    impl_test!([7305274]E 2 - [633870639]E 21 = -[699084726, 6338]E 2);
    impl_test!([7305274]E 2 - [633870639]E 6 = -[699084726, 6338]E 2);
    impl_test!([401110279]E 0 - [271733004]E 0 = [129377275]E 0);
    impl_test!([2413893]E -7 - [907304782, 7137056]E -7 = - [904890889, 7137056]E -7);
    impl_test!([279982322, 3142305]E 20 - [8456861]E 20 = [271525461, 3142305]E 20 );
    impl_test!([712499514, 215065916, 733712324, 292]E -8 - [207657154, 921507228, 49]E -4 = [140959514, 142783840, 733213109, 292]E -8);
    // impl_test!([712499514, 215065916, 733712324, 292]E -8 - [207657154, 921507228, 49]E -4 = [140959514, 142783840, 733213109, 292]E -8);
    // impl_test!([712499514, 215065916, 733712324, 292]E -8 - [207657154, 921507228, 49]E -4 = [401409595, 91427838, 927332131, 2]E -8);

    impl_test!([62702530, 608163963, 110352346]E -6 - [627989360, 234532112, 586856646]E -14 = [392493193, 494782984, 103523465, 1]E -5);

    impl_test!([61954945]E 0 - [82116691]E -4 = [467333309, 619]E -4);
    // impl_test!([42026610]E 4 - [3187757]E -4 = [996812243, 4202660]E -4);

    impl_test!([90501172]E 2 - [5039448]E -8 = [994960552, 905011719]E -8);

    impl_test!([26632001]E 0 - [0, 109]E -11 = [0, 663199991, 2]E -11);
    impl_test!([89003121]E 0 - [0, 201]E -30 = [0, 663199991, 2]E -11);
}

#[inline]
pub(crate) fn sub_digit_vecs(a: &[BigDigitBase], b: &[BigDigitBase]) -> Vec<BigDigitBase> {
    let mut result = Vec::with_capacity(a.len().max(b.len()));
    sub_digit_vecs_into(a, b, &mut result);
    return result;
}

#[inline]
pub(crate) fn sub_digit_vecs_into(a: &[BigDigitBase], b: &[BigDigitBase], v: &mut Vec<BigDigitBase>) {
    if a.len() == 1 && b.len() == 1 {
        debug_assert!(a[0] >= b[0]);
        let diff = a[0] - b[0];
        v.push(diff);
        return;
    }

    // a is longer of the vectors
    let (a, b) = if a.len() >= b.len() { (a, b) } else { (b, a) };

    // add_digit_vecs_impl!(a + b => v; BIG_DIGIT_RADIX, BigDigitBase, BigDigitBaseDouble)
}

#[cfg(test)]
#[allow(overflowing_literals)]
#[allow(unreachable_patterns)]
mod test_sub_digit_vecs {
    use super::*;

    #[test]
    fn test_0_0() {
        let v = sub_digit_vecs(&[0], &[0]);
        assert_eq!(&v, &[0]);
    }

    #[test]
    fn test_10_0() {
        let v = sub_digit_vecs(&[10], &[0]);
        assert_eq!(&v, &[10]);
    }

    #[test]
    fn test_10_3() {
        let v = sub_digit_vecs(&[10], &[3]);
        assert_eq!(&v, &[7]);
    }
}

pub(crate) fn sub_small_int_digit_vec_into(a: i64, b: &DigitInfo, result: &mut DigitInfo) {
    debug_assert!(a.abs() < BIG_DIGIT_RADIX as i64);
    debug_assert!(b.digits.len() > 0);

    let DigitInfo {
        digits: b_digits,
        scale,
        sign,
    } = b;
    let sign = *sign;

    result.digits.clear();

    if *scale == 0 && b_digits.len() == 1 && a == b_digits[0] as i64 {
        result.sign = Sign::Plus;
        result.digits.push(0);
        result.scale = 0;
        return;
    }

    dbg!(a.cmp(&0), sign, *scale);
    match (a.cmp(&0), sign, *scale) {
        (_, Sign::NoSign, _) => {
            debug_assert!(b_digits.iter().all(|&d| d == 0));
            result.scale = 0;
            if a < 0 {
                result.sign = Sign::Minus;
                result.digits.push((-a) as BigDigitBase);
            } else {
                result.sign = Sign::Plus;
                result.digits.push(a as BigDigitBase);
            }
        }
        (Ordering::Equal, _, scale) => {
            result.digits.extend_from_slice(&b_digits);
            result.sign = sign.neg();
            result.scale = scale;
            return;
        }
        (Ordering::Less, Sign::Plus, 0) | (Ordering::Greater, Sign::Minus, 0) => {
            let (hi, lo) = div_rem(b_digits[0] as i64 + a.abs(), BIG_DIGIT_RADIX as i64);
            dbg!((hi, lo));
            result.digits.push(lo as BigDigitBase);

            let mut carry = hi as BigDigitBase;
            let mut i = 1;
            while carry > 0 {
                if i == b_digits.len() {
                    result.digits.push(carry);
                    break;
                }
                let (hi, lo) = div_rem(b_digits[i] + carry, BIG_DIGIT_RADIX as BigDigitBase);
                result.digits.push(lo);
                carry = hi;
                i += 1;
            }
            if i < b_digits.len() {
                result.digits.extend_from_slice(&b_digits[i..]);
            }
            dbg!(&result.digits);
            result.sign = sign.neg();
            result.scale = 0;
        }
        (Ordering::Greater, Sign::Plus, 0) => {
            result.sign = Sign::Minus;
            result.scale = 0;

            let diff = a - b_digits[0] as BigDigitBaseSignedDouble;
            dbg!(a, b_digits[0], diff);
            if diff <= 0 {
                result.digits.push((-diff) as BigDigitBase);
                result.digits.extend_from_slice(&b_digits[1..]);
                dbg!(&result.digits);
            } else if b_digits.len() > 1 {
                result
                    .digits
                    .push((BIG_DIGIT_RADIX as BigDigitBaseSignedDouble - diff) as BigDigitBase);
                dbg!(&result.digits);
                let mut i = 1;
                while b_digits[i] == 0 {
                    result.digits.push((BIG_DIGIT_RADIX - 1) as BigDigitBase);
                    i += 1;
                }
                let is_last_digit_trailing_zero = b_digits[i] > 1 || i + 1 != b_digits.len();
                if is_last_digit_trailing_zero {
                    result.digits.push(b_digits[i] - 1);
                    result.digits.extend_from_slice(&b_digits[i + 1..]);
                }
                dbg!(&result.digits);
            } else {
                result.sign = Sign::Plus;
                result.digits.push(diff as BigDigitBase);
            }
        }
        (Ordering::Less, Sign::Minus, 0) => {
            // let (hi, lo) = div_rem(digits[0] as i64 + a.abs(), BIG_DIGIT_RADIX as i64);
            result.sign = Sign::Minus;
            result.scale = 0;
            let diff = a + b_digits[0] as BigDigitBaseSignedDouble;
            dbg!(a, b_digits[0], diff);
            if diff <= 0 {
                result.digits.push((-diff) as BigDigitBase);
                result.digits.extend_from_slice(&b_digits[1..]);
                dbg!(&result.digits);
            } else if b_digits.len() > 1 {
                result
                    .digits
                    .push((BIG_DIGIT_RADIX as BigDigitBaseSignedDouble - diff) as BigDigitBase);
                dbg!(&result.digits);
                let mut i = 1;
                while b_digits[i] == 0 {
                    result.digits.push((BIG_DIGIT_RADIX - 1) as BigDigitBase);
                    i += 1;
                }
                result.digits.push(b_digits[i] - 1);
                result.digits.extend_from_slice(&b_digits[i + 1..]);
            } else {
                result.sign = Sign::Plus;
                result.digits.push(diff as BigDigitBase);
            }
        }
        (Ordering::Less, Sign::Plus, scale) | (Ordering::Greater, Sign::Minus, scale) if scale < 0 => {
            let (count, offset) = div_rem(-scale as usize, MAX_DIGITS_PER_BIGDIGIT);
            dbg!(count, offset);

            let mut a_digits = vec![0; count];
            let shift = 10_u32.pow(offset as u32) as BigDigitBaseDouble;
            let (a_hi, a_lo) = div_rem(a.abs() as BigDigitBaseDouble * shift, BIG_DIGIT_RADIX);

            a_digits.push(a_lo as BigDigitBase);
            a_digits.push(a_hi as BigDigitBase);

            dbg!(a, &a_digits, &b_digits, scale);
            // 10.powi(offset);

            crate::arithmetic::addition::add_digit_vecs_into(&a_digits[..], b_digits, &mut result.digits);
            result.sign = sign.neg();
            result.scale = scale;
        }
        (Ordering::Less, Sign::Plus, scale) | (Ordering::Greater, Sign::Minus, scale) if scale > 0 => {
            let (count, offset) = div_rem(scale as usize, MAX_DIGITS_PER_BIGDIGIT);
            dbg!(count, offset);
        }
        (Ordering::Greater, Sign::Minus, scale) => {
            crate::arithmetic::addition::add_digit_vecs_into(&[a as BigDigitBase], b_digits, &mut result.digits);
            result.sign = Sign::Plus;
            result.scale = scale;
        }
        (Ordering::Less, Sign::Plus, _scale) => {}
        (Ordering::Greater, Sign::Plus, _scale) => {}
        _ => unimplemented!(),
    };
}

/// Special case of subtracting vectors of digits
///
/// Note: result.digits is NOT cleared, so zeros or other values may
/// be prefixed before
#[inline]
fn _subtract_aligned_digits(
    a_digits: &[BigDigitBase],
    b_digits: &[BigDigitBase],
    prec: std::num::NonZeroU32,
    result: &mut DigitInfo,
) {
    dbg!(&prec);
    debug_assert!(a_digits[a_digits.len() - 1] != 0);
    debug_assert!(b_digits[b_digits.len() - 1] != 0);

    let a_len = a_digits.len();
    let b_len = b_digits.len();

    let digit_count = std::cmp::max(a_len, b_len);
    result.digits.reserve(result.digits.len() + digit_count);

    // handle case of subtracting a single big-digit
    if a_len > 1 && b_digits.len() == 1 {
        result.sign = Sign::Plus;

        let diff = a_digits[0] as i64 - b_digits[0] as i64;

        dbg!(dbg!(diff) >= 0, diff < BIG_DIGIT_RADIX_I64);

        match (diff >= 0, diff < BIG_DIGIT_RADIX_I64) {
            (true, true) => {
                result.digits.push(diff as BigDigitBase);
                result.digits.extend_from_slice(&a_digits[1..]);
            }
            (true, false) => {
                result.digits.push((diff - BIG_DIGIT_RADIX as i64) as BigDigitBase);

                let mut i = 1;
                while i < a_len && a_digits[i] == (BIG_DIGIT_RADIX as u32 - 1) {
                    result.digits.push(0);
                    i += 1;
                }
                if i == a_len {
                    // all a_digits were MAX, just carry the 1
                    result.digits.push(1);
                } else if i + 1 == a_len {
                    // increment last digit
                    result.digits.push(a_digits[i] + 1);
                } else {
                    // increment next digit and copy the rest
                    result.digits.push(a_digits[i] + 1);
                    result.digits.extend_from_slice(&a_digits[i + 1..]);
                }
            }
            (false, _) => {
                result.digits.push((BIG_DIGIT_RADIX as i64 + diff) as BigDigitBase);
                let mut i = 1;
                while a_digits[i] == 0 {
                    result.digits.push(BIG_DIGIT_RADIX as BigDigitBase - 1);
                    i += 1;
                }
                // skip trailing zero
                if !(i == a_digits.len() - 1 && a_digits[i] == 1) {
                    result.digits.push(a_digits[i] - 1);
                    result.digits.extend_from_slice(&a_digits[i + 1..]);
                }
            }
        }
        return;
    }

    let a_b_cmp = if a_len < b_len {
        Ordering::Less
    } else if b_len < a_len {
        Ordering::Greater
    } else {
        let mut i = a_len - 1;
        while i > 0 && a_digits[i] == b_digits[i] {
            i -= 1;
        }
        a_digits[i].cmp(&b_digits[i])
    };

    let (sign, g_digits, l_digits) = match a_b_cmp {
        Ordering::Equal => {
            result.digits.push(0);
            result.sign = Sign::NoSign;
            result.scale = 0;
            return;
        }
        Ordering::Greater => (Sign::Plus, a_digits, b_digits),
        Ordering::Less => (Sign::Minus, b_digits, a_digits),
    };

    result.sign = sign;
    dbg!(result.sign);

    let mut trailing_zero_count = 0;

    let mut carry = 0;
    for i in 0..l_digits.len() {
        let diff = g_digits[i] as i32 - l_digits[i] as i32 + carry;
        if diff == 0 {
            trailing_zero_count += 1;
        } else {
            trailing_zero_count = 0;
        }
        dbg!((i, diff));
        if diff < 0 {
            let d = (BIG_DIGIT_RADIX as i32 + diff) as BigDigitBase;
            dbg!(d);
            result.digits.push(d);
            carry = -1;
        } else {
            result.digits.push(diff as BigDigitBase);
            carry = 0;
        }
    }

    if g_digits.len() == l_digits.len() {
        assert_eq!(carry, 0);
    } else if carry == 0 {
        result.digits.extend_from_slice(&g_digits[l_digits.len()..]);
        trailing_zero_count = 0;
    } else if g_digits.len() == l_digits.len() + 1 && g_digits[l_digits.len()] == 1 {
        // do-nothing if carry is -1 and last digit is 1 (no trailing zero)
    } else {
        let mut i = l_digits.len();
        while g_digits[i] == 0 {
            i += 1;
            result.digits.push(BIG_DIGIT_RADIX as BigDigitBase - 1);
        }

        result.digits.push(g_digits[i] - 1);
        if i < g_digits.len() {
            result.digits.extend_from_slice(&g_digits[i + 1..]);
        }

        trailing_zero_count = 0;
    }

    if trailing_zero_count != 0 {
        result.digits.truncate(result.digits.len() - trailing_zero_count);
    }
    dbg!(l_digits);
    dbg!(g_digits);

    return;
    /*

    dbg!(&a_digits);
    dbg!(&b_digits);

    let mut diff_vec = Vec::with_capacity(digit_count);

    let mut all_negative = true;
    let mut all_positive = true;
    let mut negative_count = 0;
    let mut positive_count = 0;
    let mut zero_count = 0;
    let mut all_zero = true;
    let mut trailing_zeros = 0;

    let f = |d: &BigDigitBase| *d as i32;

    let ai = a_digits.iter().map(f).chain(iter::repeat(0));
    let bi = b_digits.iter().map(f).chain(iter::repeat(0));

    let mut carry = 0;
    for (a_d, b_d) in ai.zip(bi).take(digit_count) {
        let diff = a_d - b_d;
        // if diff < 0 {
        // }
        // diff_vec.push(diff);
        // all_negative = all_negative && diff < 0;
        // all_zero = all_zero && diff == 0;
    }

    for i in 0..digit_count {
        let a_d = if i < a_digits.len() { a_digits[i] } else { 0 };
        let b_d = if i < b_digits.len() { b_digits[i] } else { 0 };

        let diff = a_d as i32 - b_d as i32;
        diff_vec.push(diff);

        all_negative = all_negative && diff <= 0;
        all_positive = all_positive && diff >= 0;
        if diff <= 0 {
            negative_count += 1;
        }
        if diff >= 0 {
            positive_count += 1;
        }
        if diff == 0 {
            zero_count += 1;
        }
        all_zero = all_zero && diff == 0;
        if diff == 0 {
            trailing_zeros += 1;
        } else {
            trailing_zeros = 0;
        }
    }
    dbg!(&diff_vec, all_negative, all_positive, all_zero, positive_count, negative_count, zero_count);

    result.scale = 0;

    if all_zero {
        debug_assert!(zero_count == diff_vec.len());
        result.sign = Sign::Plus;
        result.digits.push(0);
        return;
    }

    // ignore trailing zeros
    let digit_count = diff_vec.len() - trailing_zeros;
    if trailing_zeros > 0 {
        diff_vec.truncate(digit_count);
    }
    let last_index = digit_count - 1;

    // the difference is negative if the highest order byte is negative
    if diff_vec[last_index] < 0 {
        result.sign = Sign::Minus;
    } else {
        result.sign = Sign::Plus;
    }
    */
}

/// Subtract slices of bigdigits with different digit boundaries
///
///
#[inline]
fn _subtract_unaligned_digits(
    a_digits: &[BigDigitBase],
    b_digits: &[BigDigitBase],
    scale_diff: i64,
    skip: usize,
    offset: std::num::NonZeroUsize,
    prec: std::num::NonZeroU32,
    result: &mut DigitInfo,
) {
    debug_assert!(scale_diff != 0);

    // they should not be aligned
    let offset = offset.get();
    dbg!(prec);

    dbg!(scale_diff < 0);

    let shift = ten_to_pow!(offset);
    let mask = ten_to_pow!(MAX_DIGITS_PER_BIGDIGIT as u32 - offset as u32);
    assert_eq!(shift * mask, BIG_DIGIT_RADIX as u32);

    // 'a' has more digits after decimal place
    if scale_diff < 0 {
        // let shift = ten_to_pow!(offset);
        // let mask = shift * 10;
        // assert_eq!(shift * mask, BIG_DIGIT_RADIX as u32);

        if skip > 0 {
            result.digits.extend_from_slice(&a_digits[..skip]);
        }

        let mut i = 0;
        // debug_assert!(b_digits.len() <= a_digits[skip..].len());

        let mut carry = 0;
        let mut sub_carry = 0;
        while i < b_digits.len() {
            let (b_hi, b_lo) = num_integer::div_rem(b_digits[i], mask);

            let next_a = a_digits[skip + i];
            let shifted_b = carry + b_lo * shift;

            let d = next_a as i32 - shifted_b as i32;
            dbg!(next_a, shifted_b, d);
            if d < 0 && sub_carry == 0 {
                sub_carry = -1;
                result.digits.push((BIG_DIGIT_RADIX as i32 + d) as BigDigitBase);
            } else if d < 0 {
                unimplemented!();
                // result.digits.push(BIG_DIGIT_RADIX + d);
            } else if d > 0 {
                result.digits.push((d + sub_carry) as BigDigitBase);
            } else {
                unimplemented!();
            }

            carry = b_hi;
            i += 1;
        }

        if i < a_digits.len() {
            let next_a = a_digits[skip + i];
            if sub_carry != 0 {
                unimplemented!();
            }
            debug_assert!((next_a - carry) > 0);
            result.digits.push((next_a - carry) as BigDigitBase);
            result.digits.extend_from_slice(&a_digits[skip + i + 1..]);
        }
    } else {
        dbg!(skip, shift, mask);

        // 'b' has more digits after decimal place
        let mut sub_carry = 0;
        // if skip == 1 {
        //     if b_digits[0] == 0 {
        //         result.digits.push(0);
        //     } else {
        //         let diff = BIG_DIGIT_RADIX as i32 - b_digits[0] as i32;
        //         result.digits.push(diff as BigDigitBase);
        //         sub_carry = 1;
        //     }
        // } else if skip > 0 {
        for i in 0..skip {
            match (b_digits[i], sub_carry) {
                (0, 0) => {
                    result.digits.push(0);
                }
                (0, _) => {
                    let diff = BIG_DIGIT_RADIX - 1 as BigDigitBaseDouble;
                    result.digits.push(diff as BigDigitBase);
                    sub_carry = 0;
                }
                (d, 0) => {
                    let diff = BIG_DIGIT_RADIX - d as BigDigitBaseDouble;
                    result.digits.push(diff as BigDigitBase);
                    sub_carry = 1;
                }
                (d, _) if d == (BIG_DIGIT_RADIX - 1) as u32 => {
                    let diff = BIG_DIGIT_RADIX - d as BigDigitBaseDouble;
                    result.digits.push(diff as BigDigitBase);
                    sub_carry = 0;
                }
                (d, _) => {
                    let diff = BIG_DIGIT_RADIX - d as BigDigitBaseDouble;
                    result.digits.push(diff as BigDigitBase);
                    sub_carry = 0;
                }
            }
        }

        if a_digits.len() <= b_digits[skip..].len() {}
        // result.digits.extend_from_slice(&b_digits[..skip]);
        // }

        dbg!(a_digits.len(), b_digits[skip..].len());
        debug_assert!(a_digits.len() <= b_digits[skip..].len());

        let mut i = 0;
        let mut carry = 0;
        while i < a_digits.len() {
            let (hi_a, lo_a) = div_rem(a_digits[i], mask);
            dbg!(hi_a, lo_a);

            let shifted_a = lo_a * shift + carry;
            dbg!(shifted_a);
            let diff = shifted_a as i32 - b_digits[i + skip] as i32;
            dbg!(diff);
            if diff >= 0 {
                result.digits.push(diff as u32);
            } else {
                result.digits.push((BIG_DIGIT_RADIX as i64 + diff as i64) as u32);
            }

            // dbg!(b_hi, b_lo, a_digits);

            // let next_a = a_digits[skip + i];
            // dbg!(next_a, carry, b_lo, shift);
            // let shifted_b = carry + b_lo * shift;

            // let d = next_a as i32 - shifted_b as i32;
            // dbg!(next_a, shifted_b, d);
            // if d < 0 && sub_carry == 0 {
            //     sub_carry = -1;
            //     result.digits.push((BIG_DIGIT_RADIX as i32 + d) as BigDigitBase);
            // } else if d < 0 {
            //     unimplemented!();
            //     // result.digits.push(BIG_DIGIT_RADIX + d);
            // } else if d > 0 {
            //     result.digits.push((d + sub_carry) as BigDigitBase);
            // } else {
            //     unimplemented!();
            // }

            carry = hi_a;
            i += 1;
        }

        if carry != 0 {
            result.digits.push(carry as BigDigitBase);
        }

        // if i < a_digits.len() {
        //     let next_a = a_digits[skip + i];
        //     if sub_carry != 0 {
        //         unimplemented!();
        //     }
        //     debug_assert!((next_a - carry) > 0);
        //     result.digits.push((next_a - carry) as BigDigitBase);
        //     result.digits.extend_from_slice(&a_digits[skip + i + 1..]);
        // }
    }

    // unimplemented!()
    // let mask = to_power_of_ten(lo) as i64;

    // dbg!(dbg!(scale_diff) % dbg!(MAX_DIGITS_PER_BIGDIGIT as i64));
}

#[inline]
pub(crate) fn sub_int_digit_vec_into(a: i64, b: &DigitInfo, prec: std::num::NonZeroU32, result: &mut DigitInfo) {
    debug_assert!(b.digits.len() > 0);
    debug_assert!(b.digits.iter().all(|&d| (d as BigDigitBaseDouble) < BIG_DIGIT_RADIX));

    let DigitInfo {
        digits: b_digits,
        scale,
        sign,
    } = b;
    let b_scale = *scale;
    let b_sign = *sign;

    result.digits.clear();

    // handle case (0 - b) = -b
    if a == 0 {
        result.digits.extend_from_slice(&b_digits);
        result.sign = sign.neg();
        result.scale = b_scale;
        return;
    }

    if a.abs() < BIG_DIGIT_RADIX as i64 {
        return sub_small_int_digit_vec_into(a, b, result);
    }

    let mut digit_buff = [0u32; 3];
    let (a_sign, a_digits) = {
        let mut carry = a.abs();
        let mut i = 0;
        while carry != 0 {
            let (hi, lo) = div_rem(carry, BIG_DIGIT_RADIX as i64);
            dbg!(carry, hi, lo);
            digit_buff[i] = lo as BigDigitBase;
            carry = hi;
            i += 1;
        }

        if a >= 0 {
            (Sign::Plus, &digit_buff[..i])
        } else {
            (Sign::Minus, &digit_buff[..i])
        }
    };

    // handle case (a - 0) = a
    if b_sign == Sign::NoSign || b_digits.iter().rev().all(|&d| d == 0) {
        result.digits.extend_from_slice(a_digits);
        result.sign = a_sign;
        result.scale = 0;
        return;
    }

    debug_assert!(a_digits.len() <= 3);
    debug_assert!(a_digits[a_digits.len() - 1] > 0);
    dbg!(&a_digits);
    dbg!(&b_digits);

    if b_scale == 0 {
        if a_sign == b_sign {
            _subtract_aligned_digits(a_digits, b_digits, prec, result);
            result.scale = 0;
            if a_sign == Sign::Minus {
                result.sign = result.sign.neg();
            }
        } else {
            crate::arithmetic::addition::add_digit_vecs_into(a_digits, b_digits, &mut result.digits);
            result.scale = 0;
            result.sign = a_sign;
        }
        return;
    }

    let (count, offset) = div_rem(b_scale, MAX_DIGITS_PER_BIGDIGIT as i64);
    dbg!((count, offset));
    match (count, offset) {
        (-1, 0) => {
            // dbg!(b_scale % (MAX_DIGITS_PER_BIGDIGIT as i64));
            result.digits.push(count as u32);
            result.digits.push(offset as u32);
        }
        _ => unimplemented!(),
    }

    if b_scale < 0 {
        dbg!(b_scale % (MAX_DIGITS_PER_BIGDIGIT as i64));
    }

    // foo bar
    if b_scale > 0 {
        dbg!(a_digits.len());
        match b_scale as usize % MAX_DIGITS_PER_BIGDIGIT {
            0 => {
                let digit_count = std::cmp::max(a_digits.len(), b_digits.len());
                dbg!(digit_count);
            }
            _ => unimplemented!(),
        }
    }

    let ctx = Context {
        precision: prec.get() as u64,
        ..Default::default()
    };
    subtract_into(a_digits, 0, b_digits, b_scale, &ctx, result);

    unimplemented!();
}

#[cfg(test)]
#[allow(overflowing_literals)]
#[allow(unreachable_patterns)]
#[allow(non_snake_case)]
mod test_sub_int_digit_vec_into {
    use super::*;

    const DEFAULT_PREC: std::num::NonZeroU32 = unsafe { std::num::NonZeroU32::new_unchecked(19) };

    #[test]
    fn test_10_3() {
        let input = DigitInfo {
            digits: digit_vec![3],
            scale: 0,
            sign: Sign::Plus,
        };

        let mut output = DigitInfo {
            digits: digit_vec![],
            scale: 0,
            sign: Sign::NoSign,
        };

        sub_int_digit_vec_into(10, &input, DEFAULT_PREC, &mut output);
        assert_eq!(&output.digits, &[7]);
        assert_eq!(output.sign, Sign::Plus);
    }

    #[test]
    fn test_3_10() {
        let input = DigitInfo {
            digits: digit_vec![10],
            scale: 0,
            sign: Sign::Plus,
        };

        let mut output = DigitInfo {
            digits: digit_vec![],
            scale: 0,
            sign: Sign::NoSign,
        };

        sub_int_digit_vec_into(3, &input, DEFAULT_PREC, &mut output);
        assert_eq!(&output.digits, &[7]);
        assert_eq!(output.sign, Sign::Minus);
    }

    #[test]
    fn test_20_3() {
        let input = DigitInfo {
            digits: digit_vec![2],
            scale: 1,
            sign: Sign::Plus,
        };

        let mut output = DigitInfo {
            digits: digit_vec![],
            scale: 0,
            sign: Sign::NoSign,
        };

        sub_int_digit_vec_into(3, &input, DEFAULT_PREC, &mut output);
        assert_eq!(&output.digits, &[17]);
        assert_eq!(output.sign, Sign::Plus);
    }

    #[test]
    fn test_3_20202020202() {
        let input = DigitInfo {
            digits: digit_vec![202020202, 20],
            scale: 0,
            sign: Sign::Plus,
        };

        let mut output = DigitInfo {
            digits: digit_vec![],
            scale: 0,
            sign: Sign::NoSign,
        };

        sub_int_digit_vec_into(3, &input, DEFAULT_PREC, &mut output);
        assert_eq!(&output.digits, &[202020199, 20]);
        assert_eq!(output.sign, Sign::Minus);
    }

    macro_rules! impl_test {
        (- $a:literal $($rest:tt)*) => {
            // impl_test!(ARGS -$a ; NAME ᄆｰ $a; $($rest)*);
            impl_test!(ARGS -$a ; NAME case_neg $a; $($rest)*);
        };
        ($a:literal $($rest:tt)*) => {
            // impl_test!(ARGS $a ; NAME  ᄆ  $a ; $($rest)*);
            impl_test!(ARGS $a ; NAME  case_ $a ; $($rest)*);
        };
        ( ARGS $a:expr; NAME $($name:expr)*; - [$($b:literal),+] $($rest:tt)*) => {
            impl_test!( ARGS $a; $($b),*; NAME $($name)* => ( $($b)* ) (); $($rest)*);
        };
        ( ARGS $a:expr; $($b:literal),+; NAME $($name:expr)* => ($nextb:literal $($forb:literal)*) ($($revb:literal)*); $($rest:tt)*) => {
            impl_test!( ARGS $a; $($b),*; NAME $($name)* => ( $($forb)* ) ( $nextb $($revb)* ); $($rest)*);
        };
        ( ARGS $a:expr; $($b:literal),+; NAME $($name:expr)* => () ( $($revb:literal)* ); $($rest:tt)*) => {
            // impl_test!( ARGS $a; $($b),*; NAME $($name)* ｰ $($revb)* => ; $($rest)*);
            impl_test!( ARGS $a; $($b),*; NAME $($name)* __ $($revb)* => ; $($rest)*);
        };
        ( ARGS $a:expr; $($b:literal),+; NAME $($name:expr)* => ; E - $scale:literal $($rest:tt)*) => {
            impl_test!( ARGS $a; $($b),*; -$scale; NAME $($name)* e_neg $scale; $($rest)*);
        };
        ( ARGS $a:expr; $($b:literal),+; NAME $($name:expr)* => ; E $scale:literal $($rest:tt)*) => {
            impl_test!( ARGS $a; $($b),*; $scale; NAME $($name)* e_ $scale; $($rest)* );
        };
        ( ARGS $a:expr; $($b:literal),+; NAME $($name:expr)* => ; $($rest:tt)*) => {
            impl_test!( ARGS $a; $($b),*; 0; NAME $($name)* ; $($rest)* );
        };
        ( ARGS $a:expr; $($b:literal),+; $scale:literal;  NAME $($name:expr)* ; = - [$($diff:literal),+] $($rest:tt)*) => {
            impl_test!( ARGS $a; $($b),*; $scale; Sign::Minus; $($diff),* ; NAME $($name)*; $($rest)* );
        };
        ( ARGS $a:expr; $($b:literal),+; $scale:literal;  NAME $($name:expr)* ; = [$($diff:literal),+] $($rest:tt)*) => {
            impl_test!( ARGS $a; $($b),*; $scale; Sign::Plus; $($diff),* ; NAME $($name)*; $($rest)* );
        };
        ( ARGS $a:expr; $($b:literal),*; $scale:literal; $sign:expr; $($r:literal),*; NAME $($name:expr)*; E $rscale:literal) => {
            impl_test!( ARGS $a; $($b),*; $scale; $sign; $($r),*; $rscale; NAME $($name)*; );
        };
        ( ARGS $a:expr; $($b:literal),*; $scale:literal; $sign:expr; $($r:literal),*; NAME $($name:expr)*;) => {
            impl_test!( ARGS $a; $($b),*; $scale; $sign; $($r),*; 0; NAME $($name)*; );
        };
        ( ARGS $a:expr; $($b:literal),*; $scale:literal; $sign:expr; $($r:literal),*; NAME $($name:expr)*;) => {
            impl_test!( ARGS $a; $($b),*; $scale; Sign::Plus; $($r),*; 0; NAME $($name)*; );
        };
        ( ARGS $a:expr; $($b:literal),*; $scale:literal; $sign:expr; $($r:literal),*; $rscale:literal; NAME $($name:expr)*;) => {
            paste! {
                #[test]
                fn [< $($name)* >]() {
                    impl_test!(IMPL $a; $($b),*; $scale; $sign; $($r),*; $rscale)
                }
            }
        };
        (IMPL $minuend:expr; $($subtrahend:literal),*; $scale:literal; $sign:expr; $($r:literal),*; $rscale:literal) => {{
            let input = DigitInfo {
                digits: digit_vec![$($subtrahend),*],
                scale: $scale,
                sign: Sign::Plus,
            };

            let mut output = DigitInfo {
                digits: digit_vec![],
                scale: 0,
                sign: Sign::NoSign,
            };

            // assert!(($minuend as i128) <= (i64::MAX as i128));
            assert!(($minuend as i128) < crate::MAX_BIG_DIGIT_BASE_DOUBLE as i128);

            sub_int_digit_vec_into($minuend, &input, DEFAULT_PREC, &mut output);
            dbg!(&output.sign, &output.digits);
            assert_eq!(&output.digits, &[$($r),*]);
            assert_eq!(output.sign, $sign);
            assert_eq!(output.scale, $rscale);
        }};
    }

    impl_test!(123 - [030023874, 47234] = -[30023751, 47234]);
    impl_test!(-123 - [030023874, 47234] = -[30023997, 47234]);

    // impl_test!(-123 - [030023874, 47234] = -[30023997, 47234]);

    // impl_test!(123 - [0] = [123]);

    impl_test!(15 - [7] = [8]);
    impl_test!(7 - [15] = -[8]);
    impl_test!(898497495 - [898497496] = -[1]);
    // impl_test!(942445061 - [942445061] E 1 = -[482005549, 8]);

    impl_test!(1898497000 - [898497496, 1] = -[496]);
    impl_test!(1898497496 - [898497000, 1] = [496]);
    impl_test!(898497000 - [898497000, 1] = -[0, 1]);

    impl_test!(308558008 - [308558009, 1] = -[1, 1]);
    impl_test!(308558008 - [308558007, 1] = -[999999999]);
    impl_test!(-308558008 - [308558009, 1] = -[617116017, 1]);

    impl_test!(1522311586 - [936540162, 644790012, 745991119, 93] = -[414228576, 644790011, 745991119, 93]);

    impl_test!(-13 - [13] = -[26]);

    impl_test!(-958253824 - [958253824] = -[916507648, 1]);

    // impl_test!(11633491985251901031 - [1032340950] = -[219560081, 633491984, 11]);

    impl_test!(132340950 - [132340950] = [0]);

    impl_test!(-38114338160860411 - [35540405] = -[196400816, 38114338]);
    impl_test!(601033208449587446 - [449587446] = [0, 601033208]);

    impl_test!(999999999999999999 - [380292085] = [619707914, 999999999]);
    impl_test!(1000000000444635166 - [973719306] = [470915860, 999999999]);
    impl_test!(1000000003767677855 - [984077921] = [783599934, 000000002, 1]);
    // i64::MAX
    impl_test!(9223372036854775807 - [032340950, 1] = [822434857, 223372035, 9]);
    impl_test!(9223372036854775807 - [933375281] = [921400526, 223372035, 9]);
    impl_test!(
        9223372036854775807 - [945672187, 270605744, 453822838, 776256045, 8260] =
            -[90896380, 47233708, 453822829, 776256045, 8260]
    );
    impl_test!(
        9223372036854775807 - [003594813, 537760215, 712063757, 040691711, 5178] =
            -[148819006, 314388178, 712063748, 40691711, 5178]
    );

    // impl_test!(-16495329599712012293 - [958253824] = -[670266117, 495329600, 16]);
    // impl_test!(16495329599712012293 - [958253824] = -[753758469, 495329598, 16]);
    // impl_test!(9223372036854775808 - [958253824] = -[753758469, 495329598, 16]);

    impl_test!(2147483648 - [944215022, 2] = -[796731374]);
    impl_test!(-2147483648 - [944215022, 2] = -[91698670, 5]);

    // impl_test!(
    //      - [999999999, 1] = -[1, 1]
    // );

    impl_test!(396984238 - [752594762, 901176759, 857429] = -[355610524, 901176759, 857429]);

    impl_test!(770949474 - [239227606, 633] = -[468278132, 632]);

    impl_test!(-845976267 - [624860973] E -6 = -[891860973, 845976] E -6);
    impl_test!(-475148789 - [398317042, 433486196] E -20 = -[398317042, 433486196, 514878900, 47] E -20);

    impl_test!(109530412037944878 - [604710212, 882598735, 7184598] E -9 = [395289788, 155346142, 102345813] E -9);

    // impl_test!(-475148789 - [398317042, 433486196] E -20 = -[398317042, 433486196, 514878900, 47] E -20);
    // #[test]
    // fn test_396984238_857429901176759752594762() {

    //     let input = DigitInfo {
    //         digits: digit_vec![752594762, 901176759, 857429],
    //         scale: 0,
    //         sign: Sign::Plus,
    //     };

    //     let mut output = DigitInfo {
    //         digits: digit_vec![],
    //         scale: 0,
    //         sign: Sign::NoSign,
    //     };

    //     sub_int_digit_vec_into(396984238, &input, &mut output);
    //     assert_eq!(&output.digits, &);
    //     assert_eq!(output.sign, Sign::Minus);
    // }
}

#[inline]
pub(crate) fn sub_digit_info_into(a: &DigitInfo, b: &DigitInfo, result: &mut DigitInfo) {
    let DigitInfo {
        digits: a_digits,
        scale: a_scale,
        sign: a_sign,
    } = a;
    let DigitInfo {
        digits: b_digits,
        scale: b_scale,
        sign: b_sign,
    } = b;

    // if
}

// fn add_digit_vecs(a_digits: &[BigDigitBase], a_scale: i64, b_digits
