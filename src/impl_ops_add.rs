//! Addition operator trait implementation
//!

use crate::{
    Sign,
    BigDecimal,
    BigDecimalRef,
};

use crate::stdlib::{
    ops::{Add, AddAssign, Neg},
    cmp::Ordering,
};

use num_bigint::{BigInt, BigUint};
use crate::ten_to_the;

impl Add<BigDecimal> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn add(self, rhs: BigDecimal) -> BigDecimal {
        let mut lhs = self;

        match lhs.scale.cmp(&rhs.scale) {
            Ordering::Equal => {
                lhs.int_val += rhs.int_val;
                lhs
            }
            Ordering::Less => lhs.take_and_scale(rhs.scale) + rhs,
            Ordering::Greater => rhs.take_and_scale(lhs.scale) + lhs,
        }
    }
}

impl<'a> Add<&'a BigDecimal> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn add(self, rhs: &'a BigDecimal) -> BigDecimal {
        let mut lhs = self;

        match lhs.scale.cmp(&rhs.scale) {
            Ordering::Equal => {
                lhs.int_val += &rhs.int_val;
                lhs
            }
            Ordering::Less => lhs.take_and_scale(rhs.scale) + rhs,
            Ordering::Greater => rhs.with_scale(lhs.scale) + lhs,
        }
    }
}

impl<'a> Add<BigDecimal> for &'a BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn add(self, rhs: BigDecimal) -> BigDecimal {
        rhs + self
    }
}

impl<'a, 'b> Add<&'b BigDecimal> for &'a BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn add(self, rhs: &BigDecimal) -> BigDecimal {
        let lhs = self;
        match self.scale.cmp(&rhs.scale) {
            Ordering::Less => lhs.with_scale(rhs.scale) + rhs,
            Ordering::Greater => rhs.with_scale(lhs.scale) + lhs,
            Ordering::Equal => BigDecimal::new(lhs.int_val.clone() + &rhs.int_val, lhs.scale),
        }
    }
}

impl Add<BigInt> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn add(self, rhs: BigInt) -> BigDecimal {
        let mut lhs = self;

        match lhs.scale.cmp(&0) {
            Ordering::Equal => {
                lhs.int_val += rhs;
                lhs
            }
            Ordering::Greater => {
                lhs.int_val += rhs * ten_to_the(lhs.scale as u64);
                lhs
            }
            Ordering::Less => lhs.take_and_scale(0) + rhs,
        }
    }
}

impl<'a> Add<&'a BigInt> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn add(self, rhs: &BigInt) -> BigDecimal {
        let mut lhs = self;

        match lhs.scale.cmp(&0) {
            Ordering::Equal => {
                lhs.int_val += rhs;
                lhs
            }
            Ordering::Greater => {
                lhs.int_val += rhs * ten_to_the(lhs.scale as u64);
                lhs
            }
            Ordering::Less => lhs.take_and_scale(0) + rhs,
        }
    }
}

impl<'a> Add<BigInt> for &'a BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn add(self, rhs: BigInt) -> BigDecimal {
        BigDecimal::new(rhs, 0) + self
    }
}

impl<'a, 'b> Add<&'a BigInt> for &'b BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn add(self, rhs: &BigInt) -> BigDecimal {
        self.with_scale(0) + rhs
    }
}

forward_val_assignop!(impl AddAssign for BigDecimal, add_assign);

impl<'a> AddAssign<&'a BigDecimal> for BigDecimal {
    #[inline]
    fn add_assign(&mut self, rhs: &BigDecimal) {
        match self.scale.cmp(&rhs.scale) {
            Ordering::Less => {
                let scaled = self.with_scale(rhs.scale);
                self.int_val = scaled.int_val + &rhs.int_val;
                self.scale = rhs.scale;
            }
            Ordering::Greater => {
                let scaled = rhs.with_scale(self.scale);
                self.int_val += scaled.int_val;
            }
            Ordering::Equal => {
                self.int_val += &rhs.int_val;
            }
        }
    }
}

impl AddAssign<BigInt> for BigDecimal {
    #[inline]
    fn add_assign(&mut self, rhs: BigInt) {
        *self += BigDecimal::new(rhs, 0)
    }
}

impl<'a> AddAssign<&'a BigInt> for BigDecimal {
    #[inline]
    fn add_assign(&mut self, rhs: &BigInt) {
        match self.scale.cmp(&0) {
            Ordering::Equal => self.int_val += rhs,
            Ordering::Greater => self.int_val += rhs * ten_to_the(self.scale as u64),
            Ordering::Less => {
                // *self += BigDecimal::new(rhs, 0)
                self.int_val *= ten_to_the((-self.scale) as u64);
                self.int_val += rhs;
                self.scale = 0;
            }
        }
    }
}


#[cfg(test)]
mod test {
    use super::*;
    use paste::paste;

    macro_rules! impl_case {
        ($name:ident: $a:literal + $b:literal => $c:literal ) => {
            #[test]
            fn $name() {
                let mut a: BigDecimal = $a.parse().unwrap();
                let b: BigDecimal = $b.parse().unwrap();
                let c: BigDecimal = $c.parse().unwrap();

                assert_eq!(a.clone() + b.clone(), c);

                assert_eq!(a.clone() + &b, c);
                assert_eq!(&a + b.clone(), c);
                assert_eq!(&a + &b, c);

                a += b;
                assert_eq!(a, c);
            }
        };
    }

    impl_case!(case_1234en2_1234en3: "12.34" + "1.234" => "13.574");
    impl_case!(case_1234en2_n1234en3: "12.34" + "-1.234" => "11.106");
    impl_case!(case_1234en2_n1234en2: "12.34" + "-12.34" => "0");
    impl_case!(case_1234e6_1234en6: "1234e6" + "1234e-6" => "1234000000.001234");
    impl_case!(case_1234en6_1234e6: "1234e6" + "1234e-6" => "1234000000.001234");
    impl_case!(case_18446744073709551616_1: "18446744073709551616.0" + "1" => "18446744073709551617");
    impl_case!(case_184467440737e3380_1: "184467440737e3380" + "0" => "184467440737e3380");


    #[cfg(property_tests)]
    mod prop {
        use super::*;
        use proptest::*;
        use num_traits::FromPrimitive;

        proptest! {
            #[test]
            fn add_refs_and_owners(f: f32, g: f32) {
                // ignore non-normal numbers
                prop_assume!(f.is_normal());
                prop_assume!(g.is_normal());

                let a = BigDecimal::from_f32(f).unwrap();
                let b = BigDecimal::from_f32(g).unwrap();
                let own_plus_ref = a.clone() + &b;
                let ref_plus_own = &a + b.clone();

                let mut c = a.clone();
                c += &b;

                let mut d = a.clone();
                d += b;

                prop_assert_eq!(&own_plus_ref, &ref_plus_own);
                prop_assert_eq!(&c, &ref_plus_own);
                prop_assert_eq!(&d, &ref_plus_own);
            }

            #[test]
            fn addition_is_communative(f: f32, g: f32) {
                // ignore non-normal numbers
                prop_assume!(f.is_normal());
                prop_assume!(g.is_normal());

                let a = BigDecimal::from_f32(f).unwrap();
                let b = BigDecimal::from_f32(g).unwrap();
                let a_plus_b = &a + &b;
                let b_plus_a = &b + &a;

                prop_assert_eq!(a_plus_b, b_plus_a)
            }

            #[test]
            fn addition_is_associative(f: f32, g: f32, h: f32) {
                // ignore non-normal numbers
                prop_assume!(f.is_normal());
                prop_assume!(g.is_normal());
                prop_assume!(h.is_normal());

                let a = BigDecimal::from_f32(f).unwrap();
                let b = BigDecimal::from_f32(g).unwrap();
                let c = BigDecimal::from_f32(h).unwrap();

                let ab = &a + &b;
                let ab_c = ab + &c;

                let bc = &b + &c;
                let a_bc = a + bc;

                prop_assert_eq!(ab_c, a_bc)
            }
        }
    }
}
