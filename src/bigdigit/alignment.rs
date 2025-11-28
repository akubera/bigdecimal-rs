//! Splitting and shifting bigdigits for alignment
//!
#![allow(dead_code)]

use crate::*;
use super::radix::RadixPowerOfTen;
use super::endian::LittleEndian;
use crate::arithmetic::diff_usize;

type BigDigitVec<R> = super::digitvec::DigitVec<R, LittleEndian>;

/// The cases resulting from applying (lhs += rhs * offset)
///
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum AddAssignSliceAlignment {
    ///  [rrrrrrrr]     |   [rrr]    |  [rrrrrrr]
    ///      [lllllll]  | [lllllll]  |    [lllll]
    RightOverlap {
        count: usize,
    },
    ///  [rrrrr]
    ///              [lllllll]
    ///       ^count        ^0
    RightDisjoint {
        count: usize,
    },
    /// Left starts with the more significant digits
    ///      [rrrrrrr]  | [rrrrrrr]
    ///  [llllllll]     |   [lll]
    LeftOverlap {
        count: usize,
    },
    /// Disjoint, left more significant
    ///              [rrrrrrr]
    ///  [lllll]
    ///       ^count        ^0
    LeftDisjoint {
        count: usize,
    },
}

impl AddAssignSliceAlignment {
    /// Determine relative alignment of digit-arrays of given length
    /// and scale (exponent of the least significant digit)
    pub fn from_lengths_and_scales(lhs: WithScale<usize>, rhs: WithScale<usize>) -> Self {
        use cmp::Ordering::*;

        match diff_usize(rhs.scale, lhs.scale) {
            (Equal, _) => {
                Self::RightOverlap {
                    count: 0,
                }
            }
            (Less, count) => {
                if count < lhs.value {
                    Self::RightOverlap {
                        count,
                    }
                } else {
                    Self::RightDisjoint {
                        count,
                    }
                }
            }
            (Greater, count) => {
                if count < rhs.value {
                    Self::LeftOverlap {
                        count,
                    }
                } else {
                    Self::LeftDisjoint {
                        count,
                    }
                }
            }
        }
    }

    /// Determine relative alignment of digit-arrays of given length
    /// and number of integer bigdigits
    pub fn from_lengths_and_icount(lhs: WithIntCount<usize>, rhs: WithIntCount<usize>) -> Self {
        // position of least-significant digits
        Self::from_lengths_and_scales(
            WithScale {
                scale: lhs.value as i64 - lhs.count as i64,
                value: lhs.value,
            },
            WithScale {
                scale: rhs.value as i64 - rhs.count as i64,
                value: rhs.value,
            },
        )
    }
}

#[derive(Copy, Clone, Debug)]
pub(crate) struct BigDigitSplitterIter<R, I>
where
    R: RadixPowerOfTen,
    I: Iterator<Item = R::Base>,
{
    shift: ShiftState<R>,
    digits: I,
}

impl<R, I> BigDigitSplitterIter<R, I>
where
    R: RadixPowerOfTen,
    I: Iterator<Item = R::Base>,
{
    /// Wrap iterator with on shifting
    pub fn new(iter: I) -> Self {
        Self::from_shifter_and_iter(ShiftState::Zero, iter)
    }

    /// Wrap iterator, shifting by shift-state
    pub fn from_shifter_and_iter(shifter: ShiftState<R>, iter: I) -> Self {
        Self {
            shift: shifter,
            digits: iter,
        }
    }

    /// Return the internal 'mask' value
    pub fn mask(&self) -> R::Base {
        match self.shift {
            ShiftState::Zero => Zero::zero(),
            ShiftState::Shifted {
                mask:
                    BigDigitSplitter {
                        mask,
                        ..
                    },
                ..
            } => mask,
        }
    }

    /// Returns the value of the 'shift' with one subtracted
    ///
    /// Useful for adding nines to first result of `from_slice_starting_bottom`
    ///
    pub fn shift_minus_one(&self) -> R::Base {
        match self {
            BigDigitSplitterIter {
                shift: ShiftState::Zero,
                ..
            } => R::max(),
            BigDigitSplitterIter {
                shift:
                    ShiftState::Shifted {
                        mask,
                        ..
                    },
                ..
            } => mask.shift - One::one(),
        }
    }

    /// Copy all remaining digits into destination vector
    pub fn extend_vector(self, dest: &mut BigDigitVec<R>) {
        if let Self {
            shift: ShiftState::Zero,
            digits,
            ..
        } = self
        {
            dest.digits.extend(digits);
        } else {
            dest.digits.extend(self);
        }
    }

    /// Copy all remaining digits into destination vector, adding carry
    ///
    /// Note: carry is not zeroed after being pushed into the vector
    ///
    pub(crate) fn extend_vector_adding_carry(
        mut self,
        mut carry: R::Base,
        dest: &mut BigDigitVec<R>,
    ) {
        while !carry.is_zero() {
            if let Some(mut next_digit) = self.next() {
                R::addassign_carry(&mut next_digit, &mut carry);
                dest.push_significant_digit(next_digit);
            } else {
                dest.push_significant_digit(carry);
                return;
            }
        }
        self.extend_vector(dest)
    }

    /// Extend vector with digits in self, adding carry and subtracting borrow
    pub(crate) fn extend_vector_with_carry_borrow(
        mut self,
        carry: &mut R::Base,
        borrow: &mut R::Base,
        dest: &mut BigDigitVec<R>,
    ) {
        use num_traits::WrappingSub;

        if borrow.is_zero() && carry.is_zero() {
            return self.extend_vector(dest);
        }

        // the two cancel
        if carry == borrow {
            *borrow = Zero::zero();
            *carry = Zero::zero();
            return self.extend_vector(dest);
        }

        match self.next() {
            Some(digit) => {
                let d = R::sub_with_carry_borrow(digit, R::Base::zero(), carry, borrow);
                dest.push_significant_digit(d);
                // TODO: is there a cost to recursion?
                self.extend_vector_with_carry_borrow(borrow, carry, dest);
            }
            None if carry == borrow => {}
            None if carry > borrow => {
                dest.push_significant_digit(carry.wrapping_sub(borrow));
                *carry = Zero::zero();
                *borrow = Zero::zero();
            }
            None => {
                unreachable!("borrow underflow");
            }
        }
    }

    /// skip n digits
    pub fn advance_by_n(&mut self, n: usize) {
        // naive loop implementation
        for _ in 0..n {
            if self.next().is_none() {
                break;
            }
        }
    }

    /// called when there's further digits to iterate
    fn on_next_digit(&mut self, digit: R::Base) -> R::Base {
        if let ShiftState::Shifted {
            ref mut prev,
            ref mask,
        } = self.shift
        {
            let (hi, mut lo) = mask.split_and_shift(digit);
            lo += *prev;
            *prev = hi;
            lo
        } else {
            digit
        }
    }

    /// called when internal iterator is exhausted, returning final
    /// shifted digits
    fn on_last_digit(&mut self) -> Option<R::Base> {
        match self.shift {
            ShiftState::Shifted {
                ref mut prev,
                ..
            } if !prev.is_zero() => {
                let result = *prev;
                *prev = Zero::zero();
                Some(result)
            }
            _ => None,
        }
    }
}

impl<R, I> Iterator for BigDigitSplitterIter<R, I>
where
    R: RadixPowerOfTen,
    I: Iterator<Item = R::Base>,
{
    type Item = R::Base;

    fn next(&mut self) -> Option<Self::Item> {
        self.digits
            .next()
            .map(|digit| self.on_next_digit(digit))
            .or_else(|| self.on_last_digit())
    }
}

type CopiedDigitSlice<'a, R> =
    stdlib::iter::Copied<stdlib::slice::Iter<'a, <R as super::radix::RadixType>::Base>>;
pub(crate) type BigDigitSliceSplitterIter<'a, R> = BigDigitSplitterIter<R, CopiedDigitSlice<'a, R>>;

impl<'a, R: RadixPowerOfTen> BigDigitSliceSplitterIter<'a, R> {
    /// Return the complimentary size to 'n'
    fn comp_n(n: usize) -> usize {
        debug_assert!(n < R::DIGITS);
        if n == 0 {
            0
        } else {
            R::DIGITS - n
        }
    }

    /// Build without shifting digits
    pub fn from_slice(slice: &'a [R::Base]) -> Self {
        Self {
            shift: ShiftState::Zero,
            digits: slice.iter().copied(),
        }
    }

    /// Stream will behave as if adding n zeros to beginning of digits
    ///
    /// ```ignore
    /// [987654321, ...] : n=3 => [654321000, xxxxxx987, ...]
    /// ```
    ///
    pub(crate) fn from_slice_shifting_left(slice: &'a [R::Base], n: usize) -> Self {
        Self::from_slice_starting_bottom(slice, Self::comp_n(n))
    }

    /// Stream will behave as if removing first n-digits from the slice
    ///
    /// ```ignore
    /// [987654321, ...] : n=3 => [xxx987654, ...]
    /// ```
    ///
    /// This is the second digit of `from_slice_starting_bottom`
    ///
    pub(crate) fn from_slice_shifting_right(slice: &'a [R::Base], n: usize) -> Self {
        Self::from_slice_starting_top(slice, Self::comp_n(n))
    }

    /// First digit will be the bottom n digits shifted to top
    ///
    /// ```ignore
    /// [987654321, ...] : n=3 => [321000000, xxx987654, ...]
    /// ```
    ///
    pub(crate) fn from_slice_starting_bottom(slice: &'a [R::Base], n: usize) -> Self {
        Self::from_shifter_and_iter(ShiftState::starting_with_bottom(n), slice.iter().copied())
    }

    /// First digit will be the highest n-digits shifted to bottom
    ///
    /// ```ignore
    /// [987654321, ...] : n=3 => [xxxxxx987, ...]
    /// ```
    ///
    /// This is the second digit of `from_slice_shifting_left`
    /// The bottom digits will be lost.
    ///
    pub(crate) fn from_slice_starting_top(slice: &'a [R::Base], n: usize) -> Self {
        let mut digits = slice.iter().copied();
        let shifter = ShiftState::starting_with_top(n, &mut digits);
        Self::from_shifter_and_iter(shifter, digits)
    }

    /// True if iterator has no more values
    pub fn is_exhausted(&self) -> bool {
        match self.shift {
            ShiftState::Zero => self.digits.len() == 0,
            _ => self.peek_next().is_none(),
        }
    }

    /// Return the next bigdigit (if available) without advancing the internal value
    pub fn peek_next(&self) -> Option<R::Base> {
        self.clone().next()
    }
}

/// Wrap shift-and-mask type with special-case for zero shift
///
#[derive(Copy, Clone, Debug)]
pub(crate) enum ShiftState<R: RadixPowerOfTen> {
    Zero,
    Shifted {
        mask: BigDigitSplitter<R>,
        prev: R::Base,
    },
}

impl<R: RadixPowerOfTen> ShiftState<R> {
    /// Start with the lower n digits of the first bigdigit, shifted up
    ///
    /// ```ignore
    /// Self::starting_with_top([987654321, ...], 3) => [32100000, xxx987654, ...]
    /// ```
    /// 987654321, 3 =>
    ///
    fn starting_with_bottom(n: usize) -> Self {
        if n == 0 {
            Self::Zero
        } else {
            Self::Shifted {
                mask: BigDigitSplitter::mask_low(n as u8),
                prev: R::Base::zero(),
            }
        }
    }

    /// Start with high n digits of the first bigdigit
    ///
    /// ```ignore
    /// Self::starting_with_top([987654321, ...], 3) => [xxxxxx987, ...]
    /// ```
    ///
    fn starting_with_top<I: Iterator<Item = R::Base>>(n: usize, digits: &mut I) -> Self {
        if n == 0 {
            Self::Zero
        } else {
            let mask = BigDigitSplitter::mask_high(n);
            let first_digit = digits.next().map(|d| d / mask.mask).unwrap_or(Zero::zero());
            Self::Shifted {
                mask: mask,
                prev: first_digit,
            }
        }
    }
}

/// Splits a bigdigit into pieces, used when aligning
#[derive(Copy, Clone, Debug)]
pub(crate) struct BigDigitSplitter<R: RadixPowerOfTen> {
    /// dividend to split a bigdigit into high and low digits
    mask: R::Base,
    /// multiplication shifts high bigdigit to correct place after split
    shift: R::Base,
}

impl<R: RadixPowerOfTen> BigDigitSplitter<R> {
    /// Build such that (X % mask) 'keeps' n digits of X
    pub fn mask_low(n: u8) -> Self {
        use crate::arithmetic::ten_to_the_t;

        debug_assert!((n as usize) < R::DIGITS);
        let mask = ten_to_the_t(n);
        let shift = ten_to_the_t(R::DIGITS as u8 - n);
        Self {
            shift,
            mask,
        }
    }

    /// Build such that (X / mask) 'keeps' n digits of X
    pub fn mask_high(n: usize) -> Self {
        Self::mask_low((R::DIGITS - n) as u8)
    }

    /// Split bigdigit into high and low digits
    ///
    /// BigDigitSplitter::mask_high(3).split(987654321) => (987000000, 000654321)
    /// BigDigitSplitter::mask_low(3).split(987654321)  => (987654000, 000000321)
    ///
    pub fn split(&self, n: R::Base) -> (R::Base, R::Base) {
        let lo = n % self.mask;
        (n - lo, lo)
    }

    /// Split and shift such that the n "high" bits are on low
    /// side of digit and low bits are at the high end
    ///
    /// BigDigitSplitter::mask_high(3).split_and_shift(987654321) => (000000987, 654321000)
    /// BigDigitSplitter::mask_low(3).split_and_shift(987654321)  => (000987654, 321000000)
    ///
    pub fn split_and_shift(&self, n: R::Base) -> (R::Base, R::Base) {
        let (hi, lo) = self.div_rem(n);
        (hi, lo * self.shift)
    }

    pub fn div_rem(&self, n: R::Base) -> (R::Base, R::Base) {
        n.div_rem(&self.mask)
    }

    pub fn div(&self, n: R::Base) -> R::Base {
        n / self.mask
    }
}

/// Wrap a container of bigidigts with a count of how
/// many are integer
///
/// i.e. The digits are aligned with zero
///
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct WithIntCount<T> {
    /// number of big-digits in value to treat as integer
    count: i32,
    /// Slice of bigdigits
    value: T,
}

#[cfg(test)]
#[allow(clippy::zero_prefixed_literal)]
mod test {
    use super::*;

    include!("alignment.tests.rs");
}
