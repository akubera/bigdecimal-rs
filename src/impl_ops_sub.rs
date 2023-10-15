//!
//! Multiplication operator trait implementation
//!

use crate::*;


impl Sub<BigDecimal> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn sub(self, rhs: BigDecimal) -> BigDecimal {
        if rhs.is_zero() {
            return self;
        }

        if self.is_zero() {
            return rhs.neg();
        }

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

impl<'a, T: Into<BigDecimalRef<'a>>> Sub<T> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn sub(mut self, rhs: T) -> BigDecimal {
        let rhs = rhs.into();
        if rhs.is_zero() {
            return self
        }

        if self.is_zero() {
            self.int_val = BigInt::from_biguint(rhs.sign.neg(), rhs.digits.clone());
            self.scale = rhs.scale;
            return self
        }

        let mut lhs = self;
        match lhs.scale.cmp(&rhs.scale) {
            Ordering::Equal => {
                lhs.int_val -= BigInt::from_biguint(rhs.sign, rhs.digits.clone());
                lhs
            }
            Ordering::Less => {
                lhs.take_and_scale(rhs.scale) - rhs.to_owned()
            }
            Ordering::Greater => {
                lhs - rhs.to_owned_with_scale(lhs.scale)
            },
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

impl Sub<BigInt> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn sub(self, rhs: BigInt) -> BigDecimal {
        if rhs.is_zero() {
            return self;
        }

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

impl<'a, 'b, T: Into<BigDecimalRef<'b>>> Sub<T> for &'a BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn sub(self, rhs: T) -> BigDecimal {
        let rhs = rhs.into();

        match self.scale.cmp(&rhs.scale) {
            Ordering::Equal => self.clone() - rhs,
            Ordering::Less => self.with_scale(rhs.scale) - rhs,
            Ordering::Greater => self - rhs.to_owned_with_scale(self.scale),
        }
    }
}

forward_val_assignop!(impl SubAssign for BigDecimal, sub_assign);

impl<'rhs, T: Into<BigDecimalRef<'rhs>>> SubAssign<T> for BigDecimal {
    #[inline]
    fn sub_assign(&mut self, rhs: T) {
        let rhs = rhs.into();
        if rhs.is_zero() {
            return;
        }
        if self.is_zero() {
            *self = rhs.neg().to_owned();
            return;
        }

        match self.scale.cmp(&rhs.scale) {
            Ordering::Equal => {
                self.int_val -= rhs.to_owned().int_val;
            }
            Ordering::Less => {
                self.int_val *= ten_to_the((rhs.scale - self.scale) as u64);
                self.int_val -= rhs.to_owned().int_val;
                self.scale = rhs.scale;
            }
            Ordering::Greater => {
                *self -= rhs.to_owned_with_scale(self.scale);
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
    impl_case!(case_85616001e4_0: "85616001e4" - "0" => "85616001e4");
    impl_case!(case_0_520707672en5: "0" - "5207.07672" => "-520707672e-5");

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
