

macro_rules! make_test {
    (start=$low_pos:literal, round=$rounding_pos:literal, insig=$insig:literal : insignificant) => {
        make_test!(NAME case_ at_ $low_pos _round_ $rounding_pos _insig_ $insig; $low_pos; $rounding_pos; $insig; insignificant);
    };
    (NAME $($name:expr)* ; $low_pos:literal; $rounding_pos:literal; $insig:literal; insignificant ) => {
        paste! {
            #[test]
            fn [< $($name)* >]() {
                use super::BigDigitLoc::*;
                let digits = case_input!();
                let high_pos = $low_pos + digits.count_digits() - 1;
                let (
                    mut digit_iter,
                    range,
                    ignored,
                ) = align_with(&digits, $low_pos, high_pos, $rounding_pos, $insig);

                assert_eq!(digits.as_slice(), ignored);
                assert_eq!(digit_iter.next(), None);
                assert!(range.is_none());
            }
        }
    };

    (start=$low_pos:literal, round=$rounding_pos:literal, insig=$insig:literal : ($($digits:literal)+) $low_range:expr) => {
        make_test!(NAME case_ at_ $low_pos _round_ $rounding_pos _insig_ $insig; $low_pos; $rounding_pos; $insig; $($digits)*; $low_range; 0);
    };
    (start=$low_pos:literal, round=$rounding_pos:literal, insig=$insig:literal : ($($digits:literal)+) $low_range:expr; ignored=$ignored:literal) => {
        make_test!(NAME case_ at_ $low_pos _round_ $rounding_pos _insig_ $insig; $low_pos; $rounding_pos; $insig; $($digits)*; $low_range; $ignored);
    };
    (NAME $($name:expr)* ; $low_pos:literal; $rounding_pos:literal; $insig:literal; $($expected_digits:literal)+; $low_range:expr; $ignored_digit_count:literal) => {
        paste! {
            #[test]
            fn [< $($name)* >]() {
                use super::BigDigitLoc::*;
                let input = case_input!();
                let high_pos = $low_pos + input.count_digits() - 1;
                let (
                    digit_iter,
                    range,
                    ignored,
                ) = align_with(&input, $low_pos, high_pos, $rounding_pos, $insig);

                let expected_ignored_digits = &input[..$ignored_digit_count];
                assert_eq!(ignored, expected_ignored_digits);

                let expected_digits = bigdigitvec_from_be_digits![$($expected_digits)*];
                let digits: Vec<BigDigit> = digit_iter.collect();
                dbg!(&digits);
                assert_eq!(digits.as_slice(), expected_digits.as_slice());

                let low_range = $low_range;
                dbg!(low_range);
                let high_range = match low_range {
                    Significant(n) => Significant(n + digits.len()),
                    Insignificant(n) if n.get() > digits.len() => BigDigitLoc::insig(n.get() - digits.len()),
                    Insignificant(n) => BigDigitLoc::sig(digits.len() - n.get()),
                };
                dbg!(high_range);

                let range = range.unwrap();
                assert_eq!(range.low, low_range);
                assert_eq!(range.high, high_range);
            }
        }
    };


    (start=$low_pos:literal, round=$rounding_pos:literal : ($($digits:literal)*) $high_range:expr; $low_range:expr) => {
        make_test!(NAME case_ at_ $low_pos _round_ $rounding_pos ; $low_pos; $rounding_pos; $low_range; $high_range; 0; 0; [$($digits)*]);
    };
    (start=$low_pos:literal, round=$rounding_pos:literal, insig=$insig:literal : ($($digits:literal)*) $high_range:expr; $low_range:expr; $ignored:literal) => {
        make_test!(NAME case_ at_ $low_pos _round_ $rounding_pos _insig_ $insig; $low_pos; $rounding_pos; $low_range; $high_range; $ignored; $insig; [$($digits)*]);
    };
    (start=$low_pos:literal, round=$rounding_pos:literal : ($($digits:literal)*) $high_range:expr; $low_range:expr; $ignored:literal) => {
        make_test!(NAME case_ at_ $low_pos _round_ $rounding_pos ; $low_pos; $rounding_pos; $low_range; $high_range; $ignored; 0; [$($digits)*]);
    };
    (start=$low_pos:literal, round=$rounding_pos:literal, insig=$insig:literal : ($($digits:literal)*) $low_range:expr) => {
        make_test!(NAME case_ at_ $low_pos _round_ $rounding_pos _insig_ $insig; $low_pos; $rounding_pos; $low_range; 0; $insig; [$($digits)*]);
    };
    (NAME $($name:expr)* ; $low_pos:literal; $rounding_pos:literal; $low_range:expr; $ignored:literal; $insig:literal; [$($expect_digits:literal)+]) => {
        paste! {
            #[test]
            fn [< $($name)* >]() {
                use super::BigDigitLoc::*;

                let digits = case_input!();
                let high_pos = digits.count_digits() + $low_pos - 1;
                // dbg!(digits);
                // dbg!(high_pos);

                let expected_values = bigdigitvec_from_be_digits![$($expect_digits)*];
                let expected_low_range = $low_range;

                let expected_high_range = match expected_low_range {
                    Significant(n) => {
                        dbg!(1 + n + expected_values.len());
                        Significant(1 + n + expected_values.len())
                    }
                    Insignificant(n) if n.get() <= expected_values.len() => {
                        dbg!(1 + n.get() + expected_values.len());
                        Significant(expected_values.len() - n.get())
                    }
                    Insignificant(n) => {
                        Insignificant(std::num::NonZeroUsize::new(n.get() - expected_values.len()).unwrap())
                    }
                };

                let (
                    digit_iter,
                    range,
                    ignored,
                ) = new_align_with(&digits, $low_pos, high_pos, $rounding_pos, $insig);

                let values: Vec<BigDigit> = digit_iter.collect();
                match range {
                    Some(range) => {
                        dbg!(range.low, expected_low_range);
                        dbg!(range.high, expected_high_range);
                        dbg!(ignored);

                        assert_eq!(range.low, expected_low_range);
                        assert_eq!(range.high, expected_high_range);
                    }
                    None => {
                        assert_eq!(values.len(), 0);
                    }
                }
            }
        }
    };
    (NAME $($name:expr)* ; $low_pos:literal; $rounding_pos:literal; $low_range:expr; $high_range:expr; $ignored:literal; $insig:literal; [$($exdigits:literal)*]) => {
        paste! {
            #[test]
            fn [< $($name)* >]() {
                let digits = case_input!();
                let high_pos = digits.count_digits() + $low_pos - 1;
                let (
                    digit_iter,
                    range,
                    ignored,
                ) = align_with(&digits, $low_pos, high_pos, $rounding_pos, $insig);

                let range = range.unwrap();
                let values: Vec<BigDigit> = digit_iter.collect();
                let expected_values = bigdigitvec_from_be_digits![$($exdigits)*];
                assert_eq!(values.as_slice(), expected_values.as_slice());
                assert_eq!(range.low, $low_range);
                assert_eq!(range.high, $high_range);
                assert_eq!(ignored.len(), $ignored);
            }
        }
    };
}


mod case_974397965206906100072489 {
    use super::*;

    macro_rules! case_input {
        () => { bigdigitvec_from_be_digits![974397 965206906 100072489] };
    }

    // 974397 965206906 100072489
    // ^23  ^18       ^9        ^0
    make_test!(start=0, round=0 : (974397 965206906 100072489) BigDigitLoc::sig(3); BigDigitLoc::sig(0));

    // 974397965206906000000
    // ^23  ^18       ^9        ^0
    make_test!(start=0, round=9 : (974397 965206906 100072489) BigDigitLoc::sig(2); BigDigitLoc::insig(1));

    make_test!(start=0, round=9, insig=0 : (974397 965206906 100072489) BigDigitLoc::insig(1));
    make_test!(start=0, round=9, insig=1 : (974397 965206906 100072489) BigDigitLoc::insig(1));
    make_test!(start=0, round=9, insig=3 : (974397 965206906 100072489) BigDigitLoc::insig(1));
    make_test!(start=0, round=9, insig=8 : (974397 965206906 100072489) BigDigitLoc::insig(1));
    make_test!(start=0, round=9, insig=9 : (974397 965206906) BigDigitLoc::sig(0); ignored=1);

    // 97439 796520690 610007248 900000000
    // ^23   ^18     ~ ^9        ^0
    make_test!(start=0, round=10, insig=7 : (97439 796520690 610007248 900000000) BigDigitLoc::insig(2); ignored=0);
    make_test!(start=0, round=10, insig=8 : (97439 796520690 610007248 900000000) BigDigitLoc::insig(2); ignored=0);
    make_test!(start=0, round=10, insig=9 : (97439 796520690 600000000) BigDigitLoc::insig(1); ignored=1);
    make_test!(start=1, round=11, insig=10 : (97439 796520690 600000000) BigDigitLoc::insig(1); ignored=1);
    make_test!(start=9, round=19, insig=18 : (97439 796520690 600000000) BigDigitLoc::insig(1); ignored=1);
    make_test!(start=10, round=20, insig=19 : (97439 796520690 600000000) BigDigitLoc::insig(1); ignored=1);
    make_test!(start=80, round=90, insig=89 : (97439 796520690 600000000) BigDigitLoc::insig(1); ignored=1);

    make_test!(start=0, round=11, insig=9 : (9743 979652069 060000000) BigDigitLoc::insig(1); ignored=1);
    make_test!(start=0, round=13, insig=9 : (97 439796520 690600000) BigDigitLoc::insig(1); ignored=1);
    make_test!(start=0, round=14, insig=9 : (9 743979652 069060000) BigDigitLoc::insig(1); ignored=1);
    make_test!(start=0, round=15, insig=9 : (974397965 206906000) BigDigitLoc::insig(1); ignored=1);
    make_test!(start=0, round=17, insig=9 : (9743979 652069060) BigDigitLoc::insig(1); ignored=1);
    make_test!(start=0, round=18, insig=9 : (974397 965206906) BigDigitLoc::insig(1); ignored=1);

    make_test!(start=0, round=19, insig=9 : (97439 796520690 600000000) BigDigitLoc::insig(2); ignored=1);
    make_test!(start=0, round=20, insig=9 : (9743 979652069 060000000) BigDigitLoc::insig(2); ignored=1);
    make_test!(start=0, round=23, insig=9 : (9 743979652 069060000) BigDigitLoc::insig(2); ignored=1);
    make_test!(start=0, round=24, insig=9 : (974397965 206906000) BigDigitLoc::insig(2); ignored=1);
    make_test!(start=0, round=25, insig=9 : (97439796 520690600) BigDigitLoc::insig(2); ignored=1);
    make_test!(start=0, round=26, insig=9 : (9743979 652069060) BigDigitLoc::insig(2); ignored=1);
    make_test!(start=0, round=27, insig=9 : (974397 965206906) BigDigitLoc::insig(2); ignored=1);

    make_test!(start=0, round=28, insig=9 : (97439 796520690 600000000) BigDigitLoc::insig(3); ignored=1);
    make_test!(start=0, round=29, insig=9 : (9743 979652069 060000000) BigDigitLoc::insig(3); ignored=1);
    make_test!(start=0, round=30, insig=9 : (974 397965206 906000000) BigDigitLoc::insig(3); ignored=1);
    make_test!(start=0, round=36, insig=9 : (974397 965206906) BigDigitLoc::insig(3); ignored=1);

    make_test!(start=0, round=37, insig=9 : (97439 796520690 600000000) BigDigitLoc::insig(4); ignored=1);
    make_test!(start=0, round=46, insig=9 : (97439 796520690 600000000) BigDigitLoc::insig(5); ignored=1);

    //   [97439][796520690][600000000] {ignored: 100072489}
    //    ^23    ^18     ~  ^9
    make_test!(start=0, round=10, insig=10 : (97439 796520690 600000000) BigDigitLoc::insig(1); ignored=1);
    make_test!(start=0, round=11, insig=10 : (9743 979652069 060000000) BigDigitLoc::insig(1); ignored=1);
    make_test!(start=0, round=12, insig=10 : (974 397965206 906000000) BigDigitLoc::insig(1); ignored=1);
    make_test!(start=0, round=14, insig=10 : (9 743979652 069060000) BigDigitLoc::insig(1); ignored=1);
    make_test!(start=0, round=15, insig=10 : (974397965 206906000) BigDigitLoc::insig(1); ignored=1);
    make_test!(start=0, round=18, insig=10 : (974397 965206906) BigDigitLoc::insig(1); ignored=1);
    make_test!(start=0, round=19, insig=10 : (97439 796520690 600000000) BigDigitLoc::insig(2); ignored=1);
    make_test!(start=0, round=28, insig=10 : (97439 796520690 600000000) BigDigitLoc::insig(3); ignored=1);

    make_test!(start=0, round=30, insig=22 : (974 397000000) BigDigitLoc::insig(2); ignored=2);

    //   xxxx9 74397zzzz
    //       ^23
    make_test!(start=0, round=23, insig=23 : (9 743970000) BigDigitLoc::insig(1); ignored=2);
    make_test!(start=1, round=24, insig=24 : (9 743970000) BigDigitLoc::insig(1); ignored=2);
    make_test!(start=2, round=25, insig=25 : (9 743970000) BigDigitLoc::insig(1); ignored=2);

    //   xxxxx 974397zzz
    //       ~ ^23
    make_test!(start=0, round=24, insig=23 : (974397000) BigDigitLoc::insig(1); ignored=2);
    make_test!(start=0, round=25, insig=23 : (97439700) BigDigitLoc::insig(1); ignored=2);

    make_test!(start=0, round=26, insig=23 : (9743970) BigDigitLoc::insig(1); ignored=2);
    make_test!(start=0, round=27, insig=23 : (974397) BigDigitLoc::insig(1); ignored=2);
    make_test!(start=0, round=28, insig=23 : (97439 700000000) BigDigitLoc::insig(2); ignored=2);
    make_test!(start=0, round=29, insig=23 : (9743 970000000) BigDigitLoc::insig(2); ignored=2);
    make_test!(start=0, round=30, insig=23 : (974 397000000) BigDigitLoc::insig(2); ignored=2);
    make_test!(start=0, round=32, insig=23 : (9 743970000) BigDigitLoc::insig(2); ignored=2);
    make_test!(start=0, round=33, insig=23 : (974397000) BigDigitLoc::insig(2); ignored=2);
    make_test!(start=0, round=36, insig=23 : (974397) BigDigitLoc::insig(2); ignored=2);
    make_test!(start=0, round=37, insig=23 : (97439 700000000) BigDigitLoc::insig(3); ignored=2);
    make_test!(start=0, round=45, insig=23 : (974397) BigDigitLoc::insig(3); ignored=2);
    make_test!(start=0, round=51, insig=23 : (974397000) BigDigitLoc::insig(4); ignored=2);

    make_test!(start=0, round=24, insig=24 : insignificant);
    make_test!(start=0, round=25, insig=24 : insignificant);
    make_test!(start=0, round=25, insig=25 : insignificant);

    make_test!(start=0, round=30, insig=24 : insignificant);
    make_test!(start=0, round=30, insig=30 : insignificant);
    make_test!(start=0, round=32, insig=32 : insignificant);

    make_test!(start=0, round=12, insig=0 : (974 397965206 906100072 489000000) BigDigitLoc::insig(2));
    make_test!(start=0, round=12, insig=8 : (974 397965206 906100072 489000000) BigDigitLoc::insig(2));
    make_test!(start=0, round=12, insig=9 : (974 397965206 906000000) BigDigitLoc::insig(1); ignored=1);

    make_test!(start=24, round=25, insig=25 : (97439 796520690 610007248 900000000) BigDigitLoc::insig(1); ignored=0);
    make_test!(start=25, round=25, insig=25 : (974397 965206906 100072489) BigDigitLoc::sig(0); ignored=0);

    make_test!(start=9, round=10, insig=10 : (97439 796520690 610007248 900000000) BigDigitLoc::insig(1));
    make_test!(start=10, round=10, insig=10 : (974397 965206906 100072489) BigDigitLoc::sig(0));
    make_test!(start=11, round=10, insig=10 : (9743979 652069061 000724890) BigDigitLoc::sig(0));
    make_test!(start=13, round=10, insig=10 : (974397965 206906100 072489000) BigDigitLoc::sig(0));
    make_test!(start=14, round=10, insig=10 : (9 743979652 069061000 724890000) BigDigitLoc::sig(0));
    make_test!(start=15, round=10, insig=10 : (97 439796520 690610007 248900000) BigDigitLoc::sig(0));
    make_test!(start=16, round=10, insig=10 : (974 397965206 906100072 489000000) BigDigitLoc::sig(0));
    make_test!(start=17, round=10, insig=10 : (9743 979652069 061000724 890000000) BigDigitLoc::sig(0));
    make_test!(start=18, round=10, insig=10 : (97439 796520690 610007248 900000000) BigDigitLoc::sig(0));
    make_test!(start=19, round=10, insig=10 : (974397 965206906 100072489) BigDigitLoc::sig(1));
    make_test!(start=20, round=10, insig=10 : (9743979 652069061 000724890) BigDigitLoc::sig(1));
    make_test!(start=23, round=10, insig=10 : (9 743979652 069061000 724890000) BigDigitLoc::sig(1));
    make_test!(start=24, round=10, insig=10 : (97 439796520 690610007 248900000) BigDigitLoc::sig(1));
}
