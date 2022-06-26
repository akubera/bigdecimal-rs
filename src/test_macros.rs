// file to be included in tests modules

macro_rules! apply {
    ($func:ident, $a:literal, [ $($b:literal),* ]) => {{
        let a = BigDigit::from_literal_integer($a);
        let b = [ $( BigDigit::from_literal_integer($b) ),* ];
        $func(&a, &b)
    }};
    ($func:ident, [ $($a:literal),* ], [ $($b:literal),* ]) => {{
        let a = [ $( BigDigit::from_literal_integer($a) ),* ];
        let b = [ $( BigDigit::from_literal_integer($b) ),* ];
        $func(&a, &b)
    }};
}

macro_rules! assert_bigdecvec_eq {
    ( $v:ident, [ $($digits:literal),* ] ) => {
        let expected = [ $( BigDigit::from_literal_integer($digits) ),* ];
        assert_eq!($v.as_ref(), &expected);
    };
}

macro_rules! call_func {
    ( $func:ident, [ $($a:literal),* ] [ $($b:literal),* ] [ $($c:literal),* ]) => {{
        use crate::bigdigit::BigDigitBase;
        let a = [ $( BigDigit::from_literal_integer($a) ),* ];
        let b = [ $( BigDigit::from_literal_integer($b) ),* ];
        let expected = [ $( BigDigit::from_literal_integer($c) ),* ];

        $func(a.as_ref(), b.as_ref(), expected.as_ref());
    }}
}


/// Implement test with different inputs depending on bigdigit radix
///
macro_rules! impl_test_for_radix {
    ( $($rad:pat => [$($a:literal),*] [$($b:literal),*] == [$($c:literal),*]),* $(,)* ) => {{
        let do_test = impl_test!();
        match crate::bigdigit::BIG_DIGIT_RADIX {
            $(
                $rad => { call_func!(do_test, [$($a),*] [$($b),*] [$($c),*]) },
            )*
        };
    }};
    ( _ => $all:block, $($rad:pat => [$($a:literal),*] [$($b:literal),*] == [$($c:literal),*]),* $(,)*) => {{
        let do_test = impl_test!();
        match crate::bigdigit::BIG_DIGIT_RADIX {
            $(
                $rad => { call_func!(do_test, [$($a),*] [$($b),*] [$($c),*]) },
            )*
            _ => $all,
        };
    }};
}
