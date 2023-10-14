//! Addition operator trait implementation
//!

use super::*;


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

impl<'a, T: Into<BigDecimalRef<'a>>> Add<T> for BigDecimal {
    type Output = BigDecimal;

    fn add(mut self, rhs: T) -> BigDecimal {
        self.add_assign(rhs);
        self
    }
}

impl Add<BigDecimal> for &'_ BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn add(self, rhs: BigDecimal) -> BigDecimal {
        rhs + self
    }
}

impl<'a> Add<&'a BigDecimal> for &'_ BigDecimal {
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
        self + BigDecimal::from(rhs)
    }
}

impl Add<BigInt> for &'_ BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn add(self, rhs: BigInt) -> BigDecimal {
        self.to_ref() + rhs
    }
}

impl<'a> Add<&'a BigInt> for &'_ BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn add(self, rhs: &BigInt) -> BigDecimal {
        self.to_ref() + rhs
    }
}

impl<'a, T: Into<BigDecimalRef<'a>>> Add<T> for BigDecimalRef<'_> {
    type Output = BigDecimal;
    fn add(self, rhs: T) -> BigDecimal {
        let rhs = rhs.into();
        if self.scale >= rhs.scale {
            self.to_owned() + rhs
        } else {
            rhs.to_owned() + self
        }
    }
}

impl Add<BigInt> for BigDecimalRef<'_> {
    type Output = BigDecimal;

    #[inline]
    fn add(self, rhs: BigInt) -> BigDecimal {
        self + BigDecimal::from(rhs)
    }
}

impl Add<BigDecimal> for BigDecimalRef<'_> {
    type Output = BigDecimal;

    #[inline]
    fn add(self, rhs: BigDecimal) -> BigDecimal {
        rhs + self
    }
}

forward_val_assignop!(impl AddAssign for BigDecimal, add_assign);

impl<'a, N: Into<BigDecimalRef<'a>>> AddAssign<N> for BigDecimal {
    #[inline]
    fn add_assign(&mut self, rhs: N) {
        // TODO: Replace to_owned() with efficient addition algorithm
        let rhs = rhs.into().to_owned();
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
        let sign = rhs.sign();
        let mag = rhs.magnitude();
        let rhs_ref = BigDecimalRef {
            scale: 0,
            sign: sign,
            digits: mag.into(),
        };

        self.add_assign(rhs_ref);
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
