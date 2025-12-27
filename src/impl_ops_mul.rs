//! Multiplication operator trait implementation
//!

use super::*;
use crate::stdlib::mem::swap;


impl Mul<BigDecimal> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn mul(mut self, rhs: BigDecimal) -> BigDecimal {
        if self.is_one_quickcheck() == Some(true) {
            return rhs;
        }
        if rhs.is_one_quickcheck() != Some(true) {
            self.scale += rhs.scale;
            self.int_val *= rhs.int_val;
        }
        self
    }
}

impl Mul<&BigDecimal> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn mul(mut self, rhs: &BigDecimal) -> BigDecimal {
        if self.is_one_quickcheck() == Some(true) {
            self.scale = rhs.scale;
            self.int_val.set_zero();
            self.int_val += &rhs.int_val;
        } else if rhs.is_zero() {
            self.scale = 0;
            self.int_val.set_zero();
        } else if !self.is_zero() && rhs.is_one_quickcheck() != Some(true) {
            self.scale += rhs.scale;
            self.int_val *= &rhs.int_val;
        }
        self
    }
}

impl Mul<BigDecimal> for &BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn mul(self, rhs: BigDecimal) -> BigDecimal {
        rhs * self
    }
}

impl Mul<&BigDecimal> for &BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn mul(self, rhs: &BigDecimal) -> BigDecimal {
        if self.is_one_quickcheck() == Some(true) {
            rhs.normalized()
        } else if rhs.is_one_quickcheck() == Some(true) {
            self.normalized()
        } else {
            let scale = self.scale + rhs.scale;
            BigDecimal::new(&self.int_val * &rhs.int_val, scale)
        }
    }
}

impl Mul<BigInt> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn mul(mut self, rhs: BigInt) -> BigDecimal {
        self.int_val *= rhs;
        self
    }
}

impl Mul<&BigInt> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn mul(mut self, rhs: &BigInt) -> BigDecimal {
        self.int_val *= rhs;
        self
    }
}

impl Mul<BigInt> for &BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn mul(self, mut rhs: BigInt) -> BigDecimal {
        rhs *= &self.int_val;
        BigDecimal::new(rhs, self.scale)
    }
}

impl Mul<&BigInt> for &BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn mul(self, rhs: &BigInt) -> BigDecimal {
        if rhs.is_one() {
            self.normalized()
        } else if self.is_one_quickcheck() == Some(true) {
            BigDecimal::new(rhs.clone(), 0)
        } else {
            let value = &self.int_val * rhs;
            BigDecimal::new(value, self.scale)
        }
    }
}

// swap (lhs * rhs) to (rhs * lhs) for (BigInt * BigDecimal)
forward_communative_binop!(impl Mul<BigDecimal>::mul for BigInt);
forward_communative_binop!(impl Mul<&BigDecimal>::mul for BigInt);
forward_communative_binop!(impl Mul<BigDecimal>::mul for &BigInt);
forward_communative_binop!(impl Mul<&BigDecimal>::mul for &BigInt);


impl Mul<BigUint> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn mul(mut self, rhs: BigUint) -> BigDecimal {
        self *= rhs;
        self
    }
}

impl Mul<&BigUint> for BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn mul(mut self, rhs: &BigUint) -> BigDecimal {
        self *= rhs;
        self
    }
}

impl Mul<BigUint> for &BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn mul(self, rhs: BigUint) -> BigDecimal {
        self * BigInt::from_biguint(Sign::Plus, rhs)
    }
}

impl Mul<&BigUint> for &BigDecimal {
    type Output = BigDecimal;

    #[inline]
    fn mul(self, rhs: &BigUint) -> BigDecimal {
        if rhs.is_one() {
            self.normalized()
        } else if self.is_one_quickcheck() == Some(true) {
            let value = BigInt::from_biguint(Sign::Plus, rhs.clone());
            BigDecimal::new(value, 0)
        } else {
            let biguint = self.int_val.magnitude() * rhs;
            let value = BigInt::from_biguint(self.sign(), biguint);
            BigDecimal::new(value, self.scale)
        }
    }
}

// swap (lhs * rhs) to (rhs * lhs) for (BigUint * BigDecimal)
forward_communative_binop!(impl Mul<BigDecimal>::mul for BigUint);
forward_communative_binop!(impl Mul<&BigDecimal>::mul for BigUint);
forward_communative_binop!(impl Mul<BigDecimal>::mul for &BigUint);
forward_communative_binop!(impl Mul<&BigDecimal>::mul for &BigUint);


impl MulAssign<BigDecimal> for BigDecimal {
    #[inline]
    fn mul_assign(&mut self, rhs: BigDecimal) {
        if self.is_one_quickcheck() == Some(true) {
            self.int_val = rhs.int_val;
            self.scale = rhs.scale;
        } else if rhs.is_one_quickcheck() != Some(true) {
            self.scale += rhs.scale;
            self.int_val *= rhs.int_val;
        }
    }
}

impl MulAssign<&BigDecimal> for BigDecimal {
    #[inline]
    fn mul_assign(&mut self, rhs: &BigDecimal) {
        if rhs.is_one_quickcheck() == Some(true) {
            return;
        }
        self.scale += rhs.scale;
        self.int_val *= &rhs.int_val;
    }
}

impl MulAssign<&BigInt> for BigDecimal {
    #[inline]
    fn mul_assign(&mut self, rhs: &BigInt) {
        if rhs.is_one() {
            return;
        }
        self.int_val *= rhs;
    }
}

impl MulAssign<BigInt> for BigDecimal {
    #[inline]
    fn mul_assign(&mut self, rhs: BigInt) {
        *self *= &rhs
    }
}

impl MulAssign<BigUint> for BigDecimal {
    #[inline]
    fn mul_assign(&mut self, rhs: BigUint) {
        if rhs.is_one() {
            return;
        }
        *self *= BigInt::from_biguint(Sign::Plus, rhs);
        // *self *= &rhs
    }
}

impl MulAssign<&BigUint> for BigDecimal {
    #[inline]
    fn mul_assign(&mut self, rhs: &BigUint) {
        if rhs.is_one() {
            return;
        }
        // No way to multiply bigint and biguint, we have to clone
        *self *= BigInt::from_biguint(Sign::Plus, rhs.clone());
    }
}

#[cfg(test)]
#[allow(non_snake_case)]
mod bigdecimal_tests {
    use super::*;
    use num_traits::{ToPrimitive, FromPrimitive, Signed, Zero, One};
    use num_bigint;
    use paste::paste;

    macro_rules! impl_test {
        ($name:ident; $a:literal * $b:literal => $expected:literal) => {
            #[test]
            fn $name() {
                let mut a: BigDecimal = $a.parse().unwrap();
                let b: BigDecimal = $b.parse().unwrap();
                let expected: BigDecimal = $expected.parse().unwrap();

                let prod = a.clone() * b.clone();
                assert_eq!(prod, expected);
                assert_eq!(prod.scale, expected.scale);

                let prod = a.clone() * &b;
                assert_eq!(prod, expected);
                // assert_eq!(prod.scale, expected.scale);

                let prod = &a * b.clone();
                assert_eq!(prod, expected);
                // assert_eq!(prod.scale, expected.scale);

                let prod = &a * &b;
                assert_eq!(prod, expected);
                assert_eq!(prod.scale, expected.scale);

                a *= b;
                assert_eq!(a, expected);
                assert_eq!(a.scale, expected.scale);
            }
        };
        ($name:ident; $bigt:ty; $a:literal * $b:literal => $expected:literal) => {
            #[test]
            fn $name() {
                let a: BigDecimal = $a.parse().unwrap();
                let b: $bigt = $b.parse().unwrap();
                let c: BigDecimal = $expected.parse().unwrap();

                let prod = a.clone() * b.clone();
                assert_eq!(prod, c);
                assert_eq!(prod.scale, c.scale);

                let prod = b.clone() * a.clone();
                assert_eq!(prod, c);
                assert_eq!(prod.scale, c.scale);

                let prod = a.clone() * &b;
                assert_eq!(prod, c);
                assert_eq!(prod.scale, c.scale);

                let prod = b.clone() * &a;
                assert_eq!(prod, c);
                // assert_eq!(prod.scale, c.scale);

                let prod = &a * b.clone();
                assert_eq!(prod, c);
                assert_eq!(prod.scale, c.scale);

                let prod = &b * a.clone();
                assert_eq!(prod, c);
                // assert_eq!(prod.scale, c.scale);

                let prod = &a * &b;
                assert_eq!(prod, c);
                // assert_eq!(prod.scale, c.scale);

                let prod = &b * &a;
                assert_eq!(prod, c);
                // assert_eq!(prod.scale, c.scale);
            }
        };
    }

    impl_test!(case_2_1; "2" * "1" => "2");
    impl_test!(case_12d34_1d234; "12.34" * "1.234" => "15.22756");
    impl_test!(case_2e1_1; "2e1" * "1" => "2e1");
    impl_test!(case_3_d333333; "3" * ".333333" => "0.999999");
    impl_test!(case_2389472934723_209481029831; "2389472934723" * "209481029831" => "500549251119075878721813");
    impl_test!(case_1ed450_1e500; "1e-450" * "1e500" => "0.1e51");
    impl_test!(case_n995052931ddd_4d523087321; "-995052931372975485719.533153137" * "4.523087321" => "-4500711297616988541501.836966993116075977");
    impl_test!(case_995052931ddd_n4d523087321; "995052931372975485719.533153137" * "-4.523087321" => "-4500711297616988541501.836966993116075977");
    impl_test!(case_n8d37664968_n4d523087321; "-8.37664968" * "-1.9086963714056968482094712882596748" => "15.988480848752691653730876239769592670324064");
    impl_test!(case_n8d37664968_0; "-8.37664968" * "0" => "0.00000000");

    impl_test!(case_8d561_10; BigInt; "8.561" * "10" => "85.610");

    // Test multiplication between big decimal and big integer
    impl_test!(case_10000_638655273892892437; BigInt; "10000" * "638655273892892437" => "6386552738928924370000");
    impl_test!(case_1en10_n9056180052657301; BigInt; "1e-10" * "-9056180052657301" => "-905618.0052657301");
    impl_test!(case_n9en1_n368408638655273892892437473; BigInt; "-9e-1" * "-368408638655273892892437473" => "331567774789746503603193725.7");
    impl_test!(case_n1d175470587012343730098_577575785; BigInt; "-1.175470587012343730098" * "577575785" => "-678923347.038065234601180476930");

    impl_test!(case_1d000000_7848321491728058276; BigInt; "1.000000" * "7848321491728058276" => "7848321491728058276.000000");
    impl_test!(case_16535178640845d04844_1; BigInt; "16535178640845.04844" * "1" => "16535178640845.04844");

    impl_test!(case_1d000000_u7848321491728058276; BigUint; "1.000000" * "7848321491728058276" => "7848321491728058276.000000");
    impl_test!(case_16535178640845d04844_u1; BigUint; "16535178640845.04844" * "1" => "16535178640845.04844");
}
