//! Add a scale to any type
//!
//! To scale means decorate the number with an i64 which implies
//! multiplying by 10^-scale.
//!

use crate::*;

/// pair i64 'scale' with some other value
#[derive(Clone, Copy, Default)]
pub(crate) struct WithScale<T> {
    pub value: T,
    pub scale: i64,
}

impl<T> WithScale<T>  {
    /// Return new WithScale object with borrowed value and copied scale
    pub fn as_ref(&self) -> WithScale<&T> {
        let &WithScale { ref value, scale } = self;
        WithScale { value, scale }
    }
}

macro_rules! impl_is_zero_for {
    ($t:ty) => {
        impl WithScale<$t> {
            pub fn is_zero(&self) -> bool {
                self.value.is_zero()
            }
        }
    }
}

impl_is_zero_for!(&BigUint);

impl<T: fmt::Debug> fmt::Debug for WithScale<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(scale={} {:?})", self.scale, self.value)
    }
}

impl<T> From<(T, i64)> for WithScale<T> {
    fn from(pair: (T, i64)) -> Self {
        Self { value: pair.0, scale: pair.1 }
    }
}

impl<'a> From<WithScale<&'a BigInt>> for BigDecimalRef<'a> {
    fn from(obj: WithScale<&'a BigInt>) -> Self {
        Self {
            scale: obj.scale,
            sign: obj.value.sign(),
            digits: obj.value.magnitude(),
        }
    }
}

impl<'a> From<WithScale<&'a BigUint>> for BigDecimalRef<'a> {
    fn from(obj: WithScale<&'a BigUint>) -> Self {
        Self {
            scale: obj.scale,
            sign: Sign::Plus,
            digits: obj.value,
        }
    }
}

impl From<WithScale<BigUint>> for BigDecimal {
    fn from(obj: WithScale<BigUint>) -> Self {
        let WithScale { value, scale } = obj;
        Self {
            scale: scale,
            int_val: value.into(),
        }
    }
}

impl<'a, T> From<&'a WithScale<T>> for WithScale<&'a T> {
    fn from(obj: &'a WithScale<T>) -> Self {
        let &WithScale { ref value, scale } = obj;
        Self { scale, value }
    }
}

macro_rules! impl_addassign_for {
    ($t:ty) => {
        impl WithScale<$t> {
            pub fn addassign_scaled_biguint<'a, Rhs>(&mut self, rhs: Rhs)
                where Rhs: Into<WithScale<&'a BigUint>>
            {
                use crate::arithmetic::addition::addassign_scaled_biguint;
                addassign_scaled_biguint(self, rhs.into());
            }
        }
    }
}

impl_addassign_for!(BigUint);
