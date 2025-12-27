use paste::*;

macro_rules! impl_case {
    ($n:literal >> $s:literal => $expected:literal) => {
        paste! {
            #[test]
            fn [< case_ $n _ $s >]() {
                assert_eq!(TEST_FUNC($n, $s), $expected);
            }
        }
    };
    ($n:literal => $expected:literal) => {
        paste! {
            #[test]
            fn [< case_ $n >]() {
                assert_eq!(TEST_FUNC($n), $expected);
            }
        }
    };
}


mod count_digits_u32 {
    use super::*;
    const TEST_FUNC: fn(u32) -> usize = count_digits_u32;

    impl_case!(0 => 1);
    impl_case!(1 => 1);
    impl_case!(10 => 2);
    impl_case!(999999 => 6);
    impl_case!(4294967295 => 10);
}

mod count_digits_u64 {
    use super::*;
    const TEST_FUNC: fn(u64) -> usize = count_digits_u64;

    impl_case!(0 => 1);
    impl_case!(1 => 1);
    impl_case!(10 => 2);
    impl_case!(999999 => 6);
    impl_case!(4294967295 => 10);
    impl_case!(18446744073709551615 => 20);
}

mod count_digits_uint {
    use super::*;

    #[allow(non_snake_case)]
    fn TEST_FUNC(src: &str) -> u64 {
        let n = src.parse().unwrap();
        count_digits_biguint(&n)
    }

    impl_case!("999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999" => 99);
    impl_case!("9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999" => 100);
    impl_case!("10000000000000000000000000000000000000000000000000000000000000000" => 65);
}


mod dec_shift_right_u32 {
    use super::*;
    const TEST_FUNC: fn(u32, usize) -> u32 = dec_shift_right_u32;

    impl_case!(0 >> 0 => 0);

    impl_case!(12345 >> 0 => 12345);
    impl_case!(12345 >> 1 => 1234);
    impl_case!(12345 >> 2 => 123);
    impl_case!(12345 >> 6 => 0);
    impl_case!(12345 >> 7 => 0);

    impl_case!(999999999 >> 1 => 99999999);
    impl_case!(999999999 >> 5 => 9999);
    impl_case!(999999999 >> 7 => 99);
}


mod dec_shift_right_u64 {
    use super::*;
    const TEST_FUNC: fn(u64, usize) -> u64 = dec_shift_right_u64;

    impl_case!(1234567890123 >> 0 => 1234567890123);
    impl_case!(1234567890123 >> 2 => 12345678901);
    impl_case!(1234567890123 >> 6 => 1234567);
    impl_case!(1234567890123 >> 7 => 123456);

    impl_case!(18446744073709551615 >>  1 => 1844674407370955161);
    impl_case!(18446744073709551615 >>  5 => 184467440737095);
    impl_case!(18446744073709551615 >>  6 => 18446744073709);
    impl_case!(18446744073709551615 >>  7 => 1844674407370);
    impl_case!(18446744073709551615 >>  9 => 18446744073);
    impl_case!(18446744073709551615 >> 10 => 1844674407);
    impl_case!(18446744073709551615 >> 19 => 1);
    impl_case!(18446744073709551615 >> 20 => 0);
}


#[cfg(property_tests)]
mod prop {
    use super::*;
    use proptest::*;
    use proptest::num::f64::*;

    proptest! {
        #[test]
        fn check_dec_shift_right_u32(n: u32) {
            let mut x = 1;
            for s in 0..12 {
                let expected = if x > 0 { n / x } else { 0 };
                x = x.checked_mul(10).unwrap_or(0);

                let value = dec_shift_right_u32(n, s);
                prop_assert_eq!(expected, value);
            }
        }
        #[test]
        fn check_dec_shift_right_u64(n: u64) {
            let mut x = 1;
            for s in 0..22 {
                let expected = if x > 0 { n / x } else { 0 };
                x = x.checked_mul(10).unwrap_or(0);

                let value = dec_shift_right_u64(n, s);
                prop_assert_eq!(expected, value);
            }
        }
    }
}
