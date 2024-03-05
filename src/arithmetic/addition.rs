//! addition routines
//!

use crate::*;


pub(crate) fn add_bigdecimals(
    mut a: BigDecimal,
    mut b: BigDecimal,
) -> BigDecimal {
    if b.is_zero() {
        if a.scale < b.scale {
            a.int_val *= ten_to_the((b.scale - a.scale) as u64);
            a.scale = b.scale;
        }
        return a;
    }

    if a.is_zero() {
        if b.scale < a.scale {
            b.int_val *= ten_to_the((a.scale - b.scale) as u64);
            b.scale = a.scale;
        }
        return b;
    }

    let (a, b) = match a.scale.cmp(&b.scale) {
        Ordering::Equal => (a, b),
        Ordering::Less => (a.take_and_scale(b.scale), b),
        Ordering::Greater => (b.take_and_scale(a.scale), a),
    };

    add_aligned_bigdecimals(a, b)
}

fn add_aligned_bigdecimals(
    mut a: BigDecimal,
    mut b: BigDecimal,
) -> BigDecimal {
    debug_assert_eq!(a.scale, b.scale);
    if a.int_val.bits() >= b.int_val.bits() {
        a.int_val += b.int_val;
        a
    } else {
        b.int_val += a.int_val;
        b
    }
}


pub(crate) fn add_bigdecimal_refs<'a, 'b, Lhs, Rhs>(
    lhs: Lhs,
    rhs: Rhs,
) -> BigDecimal
where
    Rhs: Into<BigDecimalRef<'a>>,
    Lhs: Into<BigDecimalRef<'b>>,
{
    let lhs = lhs.into();
    let rhs = rhs.into();
    if rhs.is_zero() {
        return lhs.to_owned();
    }
    if lhs.is_zero() {
        return rhs.to_owned();
    }
    if lhs.scale >= rhs.scale {
        lhs.to_owned() + rhs
    } else {
        rhs.to_owned() + lhs
    }
}


pub(crate) fn addassign_bigdecimals(
    lhs: &mut BigDecimal,
    rhs: BigDecimal,
) {
    if rhs.is_zero() {
        return;
    }
    if lhs.is_zero() {
        *lhs = rhs;
        return;
    }
    lhs.add_assign(rhs.to_ref());
}


pub(crate) fn addassign_bigdecimal_ref<'a, T: Into<BigDecimalRef<'a>>>(
    lhs: &mut BigDecimal,
    rhs: T,
) {
    // TODO: Replace to_owned() with efficient addition algorithm
    let rhs = rhs.into().to_owned();
    match lhs.scale.cmp(&rhs.scale) {
        Ordering::Less => {
            let scaled = lhs.with_scale(rhs.scale);
            lhs.int_val = scaled.int_val + &rhs.int_val;
            lhs.scale = rhs.scale;
        }
        Ordering::Greater => {
            let scaled = rhs.with_scale(lhs.scale);
            lhs.int_val += scaled.int_val;
        }
        Ordering::Equal => {
            lhs.int_val += &rhs.int_val;
        }
    }
}
