// \file src/macros.rs
//! macros for
/*
macro_rules! forward_val_val_binop {
    (impl $imp:ident for $res:ty, $method:ident) => {
        impl $imp<$res> for $res {
            type Output = $res;

            #[inline]
            fn $method(self, other: $res) -> $res {
                // forward to val-ref
                $imp::$method(self, &other)
            }
        }
    };
}

*/
macro_rules! forward_ref_val_binop {
    (impl $imp:ident for $res:ty, $method:ident) => {
        impl<'a> $imp<$res> for &'a $res {
            type Output = $res;

            #[inline]
            fn $method(self, other: $res) -> $res {
                // forward to ref-ref
                $imp::$method(self, &other)
            }
        }
    };
}

macro_rules! forward_communative_binop {
    (impl $trait:ident<$t1:ty>::$method:ident for $t2:ty) => {
        forward_communative_binop!(
            impl $trait<$t1>::$method for $t2; Output=BigDecimal
        );
    };
    (impl $trait:ident<$t1:ty>::$method:ident for $t2:ty; Output=$output:ty) => {
        impl $trait<$t1> for $t2 {
            type Output = $output;

            #[inline]
            fn $method(self, rhs: $t1) -> Self::Output {
                // swap operands
                $trait::$method(rhs, self)
            }
        }
    };
}

/*
macro_rules! forward_val_ref_binop {
    (impl $imp:ident for $res:ty, $method:ident) => {
        impl<'a> $imp<&'a $res> for $res {
            type Output = $res;

            #[inline]
            fn $method(self, other: &$res) -> $res {
                // forward to ref-ref
                $imp::$method(&self, other)
            }
        }
    };
}

// Forward everything to ref-ref, when reusing storage is not helpful
macro_rules! forward_all_binop_to_ref_ref {
    (impl $imp:ident for $res:ty, $method:ident) => {
        forward_val_val_binop!(impl $imp for $res, $method);
        forward_val_ref_binop!(impl $imp for $res, $method);
        forward_ref_val_binop!(impl $imp for $res, $method);
    };
}
*/
