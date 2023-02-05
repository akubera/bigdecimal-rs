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
    }};
    ( $func:ident, [ $($a:literal),* ]/$a_scale:literal [ $($b:literal),* ]/$b_scale:literal [ $($c:literal),* ]) => {{
        use crate::bigdigit::BigDigitBase;
        let a = [ $( BigDigit::from_literal_integer($a) ),* ];
        let b = [ $( BigDigit::from_literal_integer($b) ),* ];
        let expected = [ $( BigDigit::from_literal_integer($c) ),* ];

        $func(a.as_ref(), $a_scale, b.as_ref(), $b_scale, expected.as_ref());
    }};
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


/// Reverse order of interior literal digits
///
/// Used for converting easy-to-ready big-endian numbers with correctly-ordered
/// little-endian numbers.
///
macro_rules! reverse_digits {
    (; $($nr:literal)+) => {
        $($nr),*
    };
    ($($n:literal)+) => {
        reverse_digits!($($n)* ;)
    };
    ($($n:literal),+) => {
        reverse_digits!($($n)* ;)
    };
    ($n0:literal $($n:literal)* ; $($nr:literal)*) => {
        reverse_digits!($($n)* ; $n0 $($nr)*)
    };
}


/// Standard construction of a DigitInfo
///
/// Allows sign, digits, and exponent set in a natural notation.
///
macro_rules! digit_info {
    (0 E 0) => {
        digit_info!(; 0 ; E 0 sign=NoSign)
    };
    (- $($n:literal)+ E $scale:literal) => {
        digit_info!($($n)* ; ; E $scale sign=Minus)
    };
    ($($n:literal)+ E $scale:literal) => {
        digit_info!($($n)* ; ; E $scale sign=Plus)
    };
    ( $n0:literal $($n:literal)* ; $($nr:literal)* ; E $scale:literal sign=$sign:ident) => {
        digit_info!($($n)* ; $n0 $($nr)* ; E $scale sign=$sign)
    };
    (; $($n:literal)+ ; E $scale:literal sign=$sign:ident) => {
        DigitInfo {
            digits: BigDigitVec::from_literal_slice(
                &[$($n),*]
            ),
            scale: $scale,
            // precision: std::num::NonZeroI64::new($prec).unwrap(),
            sign: num_bigint::Sign::$sign,
        }
    };
    (- $($n:literal)+ E $scale:literal precision=$prec:literal) => {
        DigitInfo {
            digits: BigDigitVec::from_literal_slice(&[reverse_digits!($($n)*)]),
            scale: $scale,
            // precision: std::num::NonZeroI64::new($prec).unwrap(),
            sign: num_bigint::Sign::Minus,
        }
    };
    ([$($n:literal),+] scale=$scale:literal precision=$prec:literal) => {
        DigitInfo {
            digits: BigDigitVec::from_literal_slice(&[$($n),*]),
            scale: $scale,
            // precision: std::num::NonZeroI64::new($prec).unwrap(),
            sign: num_bigint::Sign::Plus,
        }
    };
    (-[$($n:literal),+] scale=$scale:literal precision=$prec:literal) => {
        DigitInfo {
            digits: BigDigitVec::from_literal_slice(&[$($n),*]),
            scale: $scale,
            // precision: std::num::NonZeroI64::new($prec).unwrap(),
            sign: num_bigint::Sign::Minus,
        }
    }
}


/// Make BigDigitVec from digits in big-endian order
macro_rules! bigdigitvec_from_be_digits {
    () => {
        bigdigit_vec![]
    };
    ($n0:literal $($n:literal)*) => {
        bigdigitvec_from_be_digits!($($n)* ; $n0)
    };
    ($n0:literal $($n:literal)* ; $($nr:literal)*) => {
        bigdigitvec_from_be_digits!($($n)* ; $n0 $($nr)*)
    };
    ( ; $($nr:literal)+) => {
        BigDigitVec::from_literal_slice(&[$($nr),*])
    }
}
