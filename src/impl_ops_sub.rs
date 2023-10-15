//!
//! Multiplication operator trait implementation
//!

use crate::*;


impl Sub<BigDecimal> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn sub(self, rhs: BigDecimal) -> BigDecimal {
        let mut lhs = self;
        let scale = cmp::max(lhs.scale, rhs.scale);

        match lhs.scale.cmp(&rhs.scale) {
            Ordering::Equal => {
                lhs.int_val -= rhs.int_val;
                lhs
            }
            Ordering::Less => lhs.take_and_scale(scale) - rhs,
            Ordering::Greater => lhs - rhs.take_and_scale(scale),
        }
    }
}

impl<'a> Sub<&'a BigDecimal> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn sub(self, rhs: &BigDecimal) -> BigDecimal {
        let mut lhs = self;
        let scale = cmp::max(lhs.scale, rhs.scale);

        match lhs.scale.cmp(&rhs.scale) {
            Ordering::Equal => {
                lhs.int_val -= &rhs.int_val;
                lhs
            }
            Ordering::Less => lhs.take_and_scale(rhs.scale) - rhs,
            Ordering::Greater => lhs - rhs.with_scale(scale),
        }
    }
}

impl<'a> Sub<BigDecimal> for &'a BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn sub(self, rhs: BigDecimal) -> BigDecimal {
        -(rhs - self)
    }
}

impl<'a, 'b> Sub<&'b BigDecimal> for &'a BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn sub(self, rhs: &BigDecimal) -> BigDecimal {
        match self.scale.cmp(&rhs.scale) {
            Ordering::Greater => {
                let rhs = rhs.with_scale(self.scale);
                self - rhs
            }
            Ordering::Less => self.with_scale(rhs.scale) - rhs,
            Ordering::Equal => BigDecimal::new(&self.int_val - &rhs.int_val, self.scale),
        }
    }
}

impl Sub<BigInt> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn sub(self, rhs: BigInt) -> BigDecimal {
        let mut lhs = self;

        match lhs.scale.cmp(&0) {
            Ordering::Equal => {
                lhs.int_val -= rhs;
                lhs
            }
            Ordering::Greater => {
                lhs.int_val -= rhs * ten_to_the(lhs.scale as u64);
                lhs
            }
            Ordering::Less => lhs.take_and_scale(0) - rhs,
        }
    }
}

impl<'a> Sub<&'a BigInt> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn sub(self, rhs: &BigInt) -> BigDecimal {
        let mut lhs = self;

        match lhs.scale.cmp(&0) {
            Ordering::Equal => {
                lhs.int_val -= rhs;
                lhs
            }
            Ordering::Greater => {
                lhs.int_val -= rhs * ten_to_the(lhs.scale as u64);
                lhs
            }
            Ordering::Less => lhs.take_and_scale(0) - rhs,
        }
    }
}

impl<'a> Sub<BigInt> for &'a BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn sub(self, rhs: BigInt) -> BigDecimal {
        BigDecimal::new(rhs, 0) - self
    }
}

impl<'a, 'b> Sub<&'a BigInt> for &'b BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn sub(self, rhs: &BigInt) -> BigDecimal {
        self.with_scale(0) - rhs
    }
}

forward_val_assignop!(impl SubAssign for BigDecimal, sub_assign);

impl<'a> SubAssign<&'a BigDecimal> for BigDecimal {
    #[inline]
    fn sub_assign(&mut self, rhs: &BigDecimal) {
        match self.scale.cmp(&rhs.scale) {
            Ordering::Less => {
                let lhs = self.with_scale(rhs.scale);
                self.int_val = lhs.int_val - &rhs.int_val;
                self.scale = rhs.scale;
            }
            Ordering::Greater => {
                self.int_val -= rhs.with_scale(self.scale).int_val;
            }
            Ordering::Equal => {
                self.int_val = &self.int_val - &rhs.int_val;
            }
        }
    }
}

impl SubAssign<BigInt> for BigDecimal {
    #[inline(always)]
    fn sub_assign(&mut self, rhs: BigInt) {
        *self -= BigDecimal::new(rhs, 0)
    }
}

impl<'a> SubAssign<&'a BigInt> for BigDecimal {
    #[inline(always)]
    fn sub_assign(&mut self, rhs: &BigInt) {
        match self.scale.cmp(&0) {
            Ordering::Equal => SubAssign::sub_assign(&mut self.int_val, rhs),
            Ordering::Greater => SubAssign::sub_assign(&mut self.int_val, rhs * ten_to_the(self.scale as u64)),
            Ordering::Less => {
                self.int_val *= ten_to_the((-self.scale) as u64);
                SubAssign::sub_assign(&mut self.int_val, rhs);
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
        ($name:ident: $a:literal - $b:literal => $c:literal ) => {
            #[test]
            fn $name() {
                let mut a: BigDecimal = $a.parse().unwrap();
                let b: BigDecimal = $b.parse().unwrap();
                let c: BigDecimal = $c.parse().unwrap();

                assert_eq!(a.clone() - b.clone(), c);

                assert_eq!(a.clone() - &b, c);
                assert_eq!(&a - b.clone(), c);
                assert_eq!(&a - &b, c);

                a -= b;
                assert_eq!(a, c);
            }
        };
    }

    impl_case!(case_1234en2_1234en3: "12.34" - "1.234" => "11.106");
    impl_case!(case_1234en2_n1234en3: "12.34" - "-1.234" => "13.574");
    impl_case!(case_1234e6_1234en6: "1234e6" - "1234e-6" => "1233999999.998766");

    #[cfg(property_tests)]
    mod prop {
        use super::*;
        use proptest::*;
        use num_traits::FromPrimitive;

        proptest! {
            #[test]
            fn sub_refs_and_owners(f: f32, g: f32) {
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
            fn subtraction_is_anticommunative(f: f32, g: f32) {
                // ignore non-normal numbers
                prop_assume!(f.is_normal());
                prop_assume!(g.is_normal());

                let a = BigDecimal::from_f32(f).unwrap();
                let b = BigDecimal::from_f32(g).unwrap();
                let a_minus_b = &a - &b;
                let b_minus_a = &b - &a;

                prop_assert_eq!(a_minus_b, -b_minus_a)
            }
        }
    }
}
