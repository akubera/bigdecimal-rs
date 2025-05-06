use paste::paste;

mod test_multiply_quad_spread_into {
    use super::*;

    macro_rules! impl_case {
        ( wrapping: $($toks:tt)* ) => {
            impl_case!(multiply_quad_spread_into_wrapping; $($toks)*);
        };
        (
            $func:ident;
            $s:literal @ $n:literal,
            [ $a:literal, $b:literal, $y:literal, $z:literal] => $expected:expr
        ) => {
            paste!{
                #[test]
                fn [< case_ $n _ $a _ $b _ $y _ $z >]() {
                    let mut result = vec![0; $s];
                    $func(&mut result, $n, $a, $b, $y, $z);
                    let expected = &$expected;
                    assert_eq!(expected, result.as_slice());
                }
            }
        };
        ( $($toks:tt)* ) => {
            impl_case!(multiply_quad_spread_into; $($toks)*);
        };
    }

    impl_case!(
        8 @ 2,
        [2559712337, 684026673, 1163340730, 1823138616]
         => [0u32, 0, 3001179060, 4203670869, 1059648540, 580714756, 0, 0]);

    impl_case!(
        6 @ 1,
        [4294967295, 4294967295, 4294967295, 4294967295]
         => [0u32, 2, 0, 4294967292, 4294967295, 1]);

    impl_case!(
        wrapping: 8 @ 6,
        [2559712337, 684026673, 1163340730, 1823138616]
         => [1059648540u32, 580714756, 0, 0, 0, 0, 3001179060, 4203670869]);
}
