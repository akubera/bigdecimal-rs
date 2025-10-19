use bigdigit::radix::RADIX_10p9_u32;
use bigdigit::radix::RADIX_10p19_u64;


#[test]
fn split_987654321_low_3() {
    let (hi, lo) = BigDigitSplitter::<RADIX_10p9_u32>::mask_low(3).split(987654321);
    assert_eq!(hi, 987654000);
    assert_eq!(lo, 000000321)
}

#[test]
fn split_987654321_high_3() {
    let (hi, lo) = BigDigitSplitter::<RADIX_10p9_u32>::mask_high(3).split(987654321);
    assert_eq!(hi, 987000000);
    assert_eq!(lo, 000654321)
}

#[test]
fn split_and_shift_987654321_high_3() {
    let (hi, lo) = BigDigitSplitter::<RADIX_10p9_u32>::mask_high(3).split_and_shift(987654321);
    assert_eq!(hi, 000000987);
    assert_eq!(lo, 654321000)
}

#[test]
fn split_and_shift_987654321_low_3() {
    let (hi, lo) = BigDigitSplitter::<RADIX_10p9_u32>::mask_low(3).split_and_shift(987654321);
    assert_eq!(hi, 000987654);
    assert_eq!(lo, 321000000)
}

mod from_lengths_and_scales {
    use super::*;
    use paste::*;

    macro_rules! impl_test {
        (($x:literal, -$y:literal) += $($t:tt)*) => {
            paste! { impl_test!([< case_ $x _n$y >]; ($x, -$y); $($t)*); }
        };
        (($x:literal, $y:literal) += $($t:tt)*) => {
            paste! { impl_test!([< case_ $x _$y >]; ($x, $y); $($t)*); }
        };
        ($name:ident; ($x:literal, $y:literal); ($a:literal, -$b:literal) => $e:expr ) => {
            paste! { impl_test!([< $name _ $a _n $b >]; ($x, $y); ($a, -$b); $e); }
        };
        ($name:ident; ($x:literal, $y:literal); ($a:literal, $b:literal) => $e:expr ) => {
            paste! { impl_test!([< $name _ $a _ $b >]; ($x, $y); ($a, $b); $e); }
        };
        ($name:ident; ($x:literal, $y:literal); ($a:literal, $b:literal); $expected:expr) => {
            #[test]
            fn $name() {
                use self::AddAssignSliceAlignment::*;

                let alignment = AddAssignSliceAlignment::from_lengths_and_scales(
                    WithScale { value: $x, scale: $y },
                    WithScale { value: $a, scale: $b },
                );
                assert_eq!(alignment, $expected);
            }
        };
    }

    // ll.llllllll
    //  r.rrrrrrr
    impl_test!((10, 8) += (8, 7) => RightOverlap { count: 1 });

    // lllllll.
    //  rrrrr0.
    impl_test!((7, 0) += (5, -1) => RightOverlap { count: 1 });

    //     lll.
    //  rrrrrr.rrr
    impl_test!((3, 0) += (9, 3) => LeftOverlap { count: 3 });

    // lll.l
    //    .000000rrr
    impl_test!((4, 1) += (3, 9) => LeftDisjoint { count: 8 });

    //    0.00000llll
    // rrrr.rr
    impl_test!((4, 9) += (6, 2) => RightDisjoint{ count: 7 });
}

mod from_lengths_and_icount {
    use super::*;
    use paste::*;

    macro_rules! impl_test {
        (($x:literal, -$y:literal) += $($t:tt)*) => {
            paste! {
                impl_test!([< case_ $x _n$y >]; ($x, -$y); $($t)*);
            }
        };
        (($x:literal, $y:literal) += $($t:tt)*) => {
            paste! {
                impl_test!([< case_ $x _$y >]; ($x, $y); $($t)*);
            }
        };
        ($name:ident; ($x:literal, $y:literal); ($a:literal, -$b:literal) => $e:expr ) => {
            paste! {
                impl_test!([< $name _ $a _n $b >]; ($x, $y); ($a, -$b); $e);
            }
        };
        ($name:ident; ($x:literal, $y:literal); ($a:literal, $b:literal) => $e:expr ) => {
            paste! {
                impl_test!([< $name _ $a _ $b >]; ($x, $y); ($a, $b); $e);
            }
        };
        ($name:ident; ($x:literal, $y:literal); ($a:literal, $b:literal); $expected:expr) => {
            #[test]
            fn $name() {
                use self::AddAssignSliceAlignment::*;

                let alignment = AddAssignSliceAlignment::from_lengths_and_icount(
                    WithIntCount { value: $x, count: $y },
                    WithIntCount { value: $a, count: $b },
                );
                assert_eq!(alignment, $expected);
            }
        };
    }

    // ll.llllllll
    //  r.rrrrrrr
    impl_test!((10, 2) += (8, 1) => RightOverlap { count: 1 });

    // ll.lllllll
    //   .rrrrrrr
    impl_test!((9, 2) += (7, 0) => RightOverlap { count: 0 });

    //    ll.ll
    // rrrrr.rr
    impl_test!((4, 2) += (7, 5) => RightOverlap { count: 0 });

    // lllll000.
    //         .00rrrrrrr
    impl_test!((5, 8) += (7, -2) => LeftDisjoint { count: 12 });

    // l0.
    //   .0rrrrrrr
    impl_test!((1, 2) += (7, -1) => LeftDisjoint { count: 9 });

    // ll.lllllllll
    //   .0rrrrrrr
    impl_test!((11, 2) += (7, -1) => RightOverlap { count: 1 });

    // ll.llllllll
    //   .0rrrrrrr
    impl_test!((10, 2) += (7, -1) => RightOverlap { count: 0 });

    // ll.lllllll
    //   .0rrrrrrr
    impl_test!((9, 2) += (7, -1) => LeftOverlap { count: 1 });

    // ll.ll
    //   .0rrrrrrr
    impl_test!((4, 2) += (7, -1) => LeftOverlap { count: 6 });

    // ll.l
    //   .0rrrrrrr
    impl_test!((3, 2) += (7, -1) => LeftDisjoint { count: 7 });

    // ll.
    //   .0rrrrrrr
    impl_test!((2, 2) += (7, -1) => LeftDisjoint { count: 8 });

    // rrrrr000.
    //         .00lllllll
    impl_test!((7, -2) += (5, 8) => RightDisjoint { count: 12 });

    // lllll.ll
    //     r.rrrr
    impl_test!((7, 5) += (5, 1) => LeftOverlap { count: 2 });

    // lllll.l
    //     r.rrrr
    impl_test!((6, 5) += (5, 1) => LeftOverlap { count: 3 });

    // lllll.
    //     r.rrrr
    impl_test!((5, 5) += (5, 1) => LeftOverlap { count: 4 });

    // llll0.
    //     r.rrrr
    impl_test!((4, 5) += (5, 1) => LeftDisjoint { count: 5 });

    //       l.llll
    // rrr0000.
    impl_test!((5, 1) += (3, 7) => RightDisjoint { count: 8 });
}
