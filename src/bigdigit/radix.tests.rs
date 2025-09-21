
mod radix_10p19_u64 {
    use super::*;
    use super::RADIX_10p19_u64 as Radix;

    #[test]
    fn split_wide_digit_10e19_0() {
        let (hi, lo) = Radix::split_wide_digit(0);
        assert_eq!(hi, 0);
        assert_eq!(lo, 0);
    }

    #[test]
    fn split_wide_digit_10e19_sqrd() {
        let (hi, lo) = Radix::split_wide_digit(99999999999999999980000000000000000001);
        assert_eq!(hi, 9999999999999999998);
        assert_eq!(lo, 1);
    }

    #[test]
    fn split_wide_digit_5060270152244608514849739578370464703() {
        let (hi, lo) = Radix::split_wide_digit(5060270152244608514849739578370464703);
        assert_eq!(hi, 506027015224460851);
        assert_eq!(lo, 4849739578370464703);
    }

    #[test]
    fn add_with_carry() {
        let mut carry = 20;
        let sum = Radix::add_carry(222292843123382, &mut carry);
        assert_eq!(sum, 222292843123402);
        assert_eq!(carry, 0);
    }

    #[test]
    fn add_with_carry_overflow_18446744073709551600_55() {
        let mut carry = 55;
        let sum = Radix::add_carry(18446744073709551600, &mut carry);
        assert_eq!(sum, 8446744073709551655);
        assert_eq!(carry, 1);
    }

    #[test]
    fn add_with_carry_overflow_2() {
        let result = &mut [0, 1, 2];
        let mut carry = 40;
        Radix::add_carry_into_slice(result, &mut carry);
        assert_eq!(result, &[40, 1, 2]);
        assert_eq!(carry, 0);
    }
}

mod radix_u64 {
    use super::*;
    use super::RADIX_u64 as Radix;

    #[test]
    fn add_with_carry_overflow_1() {
        let mut carry = 55;
        let sum = Radix::add_carry(18446744073709551600, &mut carry);
        assert_eq!(sum, 39);
        assert_eq!(carry, 1);
    }

    #[test]
    fn add_with_carry_overflow_2() {
        let result = &mut 0;
        let mut carry = 40;
        Radix::addassign_carry(result, &mut carry);
        assert_eq!(*result, 40);
        assert_eq!(carry, 0);
    }

    #[test]
    fn add_with_carry_overflow_3() {
        let mut result = 3533561901698977160;
        let mut carry = 17004058994074047095;
        Radix::addassign_carry(&mut result, &mut carry);
        assert_eq!(result, 2090876822063472639);
        assert_eq!(carry, 1);
    }
}
