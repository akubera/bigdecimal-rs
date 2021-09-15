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

macro_rules! forward_val_assignop {
    (impl $imp:ident for $res:ty, $method:ident) => {
        impl $imp<$res> for $res {
            #[inline]
            fn $method(&mut self, other: $res) {
                // forward to mutref-ref
                $imp::$method(self, &other)
            }
        }
    };
}

macro_rules! impl_div_for_uint_primitive {
    // (impl $imp:ident for $res:ty, $method:ident) => {
    ($res:ty) => {
        impl<'a> Div<$res> for &'a BigDecimal {
            type Output = BigDecimal;

            #[inline]
            fn div(self, den: $res) -> Self::Output {
                if den == 1 {
                    self.clone()
                } else if den == 2 {
                    self.half()
                } else {
                    self / BigDecimal::from(den)
                }
            }
        }

        impl<'a> Div<&'a BigDecimal> for $res {
            type Output = BigDecimal;

            #[inline(always)]
            fn div(self, den: &'a BigDecimal) -> Self::Output {
                BigDecimal::from(self) / den
            }
        }

        impl Div<BigDecimal> for $res {
            type Output = BigDecimal;

            #[inline(always)]
            fn div(self, den: BigDecimal) -> Self::Output {
                BigDecimal::from(self) / den
            }
        }
    };
}

macro_rules! impl_div_for_int_primitive {
    // (impl $imp:ident for $res:ty, $method:ident) => {
    ($res:ty) => {
        impl<'a> Div<$res> for BigDecimal {
            type Output = BigDecimal;

            #[inline(always)]
            fn div(self, den: $res) -> Self::Output {
                if den < 0 {
                    -Div::div(self, -den)
                } else if den == 1 {
                    self
                } else if den == 2 {
                    self.half()
                } else {
                    self / BigDecimal::from(den)
                }
            }
        }

        impl<'a> Div<$res> for &'a BigDecimal {
            type Output = BigDecimal;

            #[inline(always)]
            fn div(self, den: $res) -> Self::Output {
                if den < 0 {
                    -Div::div(self, -den)
                } else if den == 1 {
                    self.clone()
                } else if den == 2 {
                    self.half()
                } else {
                    self / BigDecimal::from(den)
                }
            }
        }

        impl<'a> Div<&'a BigDecimal> for $res {
            type Output = BigDecimal;

            #[inline(always)]
            fn div(self, den: &'a BigDecimal) -> Self::Output {
                match (self < 0, den.is_negative()) {
                    (true, true) => -self / -den,
                    (true, false) => (-self / den).neg(),
                    (false, true) => (-self / den.abs()),
                    (false, false) => BigDecimal::from(self) / den,
                }
            }
        }

        impl Div<BigDecimal> for $res {
            type Output = BigDecimal;

            #[inline(always)]
            fn div(self, den: BigDecimal) -> Self::Output {
                match (self < 0, den.is_negative()) {
                    (true, true) => -self / -den,
                    (true, false) => (-self / den).neg(),
                    (false, true) => (-self / den.abs()),
                    (false, false) => BigDecimal::from(self) / den,
                }
            }
        }
    };
}

macro_rules! impl_div_for_float_primitive {
    // (impl $imp:ident for $res:ty, $method:ident) => {
    ($res:ty) => {
        impl<'a> Div<$res> for &'a BigDecimal {
            type Output = BigDecimal;

            #[inline]
            #[allow(clippy::float_cmp)]
            fn div(self, den: $res) -> Self::Output {
                if den.is_nan() {
                    BigDecimal::zero()
                } else if den == 1.0 {
                    self.clone()
                } else if den == 0.5 {
                    self.double()
                } else if den == 2.0 {
                    self.half()
                } else if den == -1.0 {
                    -self
                } else if den < 0.0 && self.is_positive() {
                    -(self / -den)
                } else {
                    // Unwrap is safe, because `is_nan` checked above
                    self / BigDecimal::try_from(den).unwrap()
                }
            }
        }

        impl<'a> Div<&'a BigDecimal> for $res {
            type Output = BigDecimal;
            #[inline(always)]
            fn div(self, den: &'a BigDecimal) -> Self::Output {
                if self.is_nan() {
                    BigDecimal::zero()
                } else {
                    BigDecimal::try_from(self).unwrap() / den
                }
            }
        }

        impl Div<BigDecimal> for $res {
            type Output = BigDecimal;
            #[inline(always)]
            fn div(self, den: BigDecimal) -> Self::Output {
                if self.is_nan() {
                    BigDecimal::zero()
                } else {
                    BigDecimal::try_from(self).unwrap() / den
                }
            }
        }
    };
}

macro_rules! forward_primitive_types {
    (floats => $macro_name:ident) => {
        $macro_name!(f32);
        $macro_name!(f64);
    };
    (ints => $macro_name:ident) => {
        $macro_name!(i8);
        $macro_name!(i16);
        $macro_name!(i32);
        $macro_name!(i64);
    };
    (uints => $macro_name:ident) => {
        $macro_name!(u8);
        $macro_name!(u16);
        $macro_name!(u32);
        $macro_name!(u64);
    };
}

macro_rules! impl_div_for_primitives {
    () => {
        forward_primitive_types!(floats => impl_div_for_float_primitive);
        forward_primitive_types!(ints => impl_div_for_int_primitive);
        forward_primitive_types!(uints => impl_div_for_uint_primitive);
    };
}

macro_rules! do_mul_and_add_into {
    ( $value:expr, $factor:expr, $dest:ident, $limit:expr; $t1:ty, $t2:ty) => {{
        use num_integer::div_rem;

        let factors = $factor;
        $dest.resize(factors.len(), 0);

        let mut carry = 0;
        for (&factor, out) in factors.iter().zip($dest.iter_mut()) {
            let tmp = ($value as $t2 * factor as $t2) + carry + *out as $t2;
            let (high, low) = div_rem(tmp, $limit);
            *out = low as $t1;
            carry = high;
        }

        while carry != 0 {
            $dest.push((carry % $limit) as $t1);
            carry /= $limit;
        }
    }};
}

#[macro_export]
macro_rules! change_base {
//   ( $base_vec:expr => $dest:ident; ($in_base:ident $in_type:ty) => ($out_base:ident $out_type:ty; $other_out_type:ty)) => {{
//   ($base_vec:ident)

  ( $base_vec:expr => $dest:ident; ($in_base:ident $in_type:ty) => ($out_base:ident $out_type:ty; $other_out_type:ty)) => {{
    let mut dec_digits = Vec::with_capacity($dest.capacity());
    dec_digits.push(1);
    $dest.push(0);

    for value in $base_vec {
      if *value != 0 {
        do_mul_and_add_into!(*value, &dec_digits, $dest, $out_base; $other_out_type, $in_type)
      }
      change_base!( SHIFT-BASIS dec_digits ($in_base $in_type) ($out_base $out_type));
    }

  }};

  ( SHIFT-BASIS $base_vec:ident ($in_base:ident $in_type:ty) ($out_base:ident $out_type:ty) ) => {{
    let mut carry = 0;
    for digit in $base_vec.iter_mut() {
      let tmp = *digit as $in_type * $in_base as $in_type + carry;
      carry = tmp / $out_base;
      *digit = (tmp % $out_base) as $out_type;
    }

    while carry != 0 {
      $base_vec.push((carry % $out_base) as $out_type);
      carry /= $out_base;
    }
  }};

  ( DEC $dec_var:ident => ($dest:ident $out_base:literal) ) => {{
    let mut dec_digits = Vec::<BigDigitBaseDouble>::with_capacity($dest.capacity());
    dec_digits.push(1);
    $dest.push(0);

    for value in $dec_var.data.iter().map(|bd| bd.0) {
      if value != 0 {
        do_mul_and_add_into!(value, &dec_digits, $dest, $out_base; BigDigitBaseDouble, BigDigitBaseDouble);
      }
      // change_base!( SHIFT-BASIS dec_digits ( BigDigitBaseDouble) ($out_base $out_type));

      let mut carry = 0;
      for digit in dec_digits.iter_mut() {
        let tmp = *digit as BigDigitBaseDouble * BIG_DIGIT_RADIX + carry;
        carry = tmp / $out_base;
        *digit = tmp % $out_base;
      }

      while carry != 0 {
        dec_digits.push(carry % $out_base);
        carry /= $out_base;
      }
    }
  }}
}
