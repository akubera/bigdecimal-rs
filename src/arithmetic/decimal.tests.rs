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
