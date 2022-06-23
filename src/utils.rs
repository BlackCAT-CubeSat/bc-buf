//! 

use super::CBuf;

pub(crate) trait IndexMath: Copy {
    fn add_index<const SIZE: usize>(self, increment: usize) -> Self;

    fn sub_index<const SIZE: usize>(self, decrement: usize) -> Self;

    #[inline]
    fn next_index<const SIZE: usize>(self) -> Self {
        self.add_index::<SIZE>(1)
    }

    #[inline]
    fn incr_index<const SIZE: usize>(&mut self) {
        *self = self.next_index::<SIZE>();
    }

    fn in_range<const SIZE: usize>(self, base: Self, len: usize) -> bool;
}

impl IndexMath for usize {
    #[inline]
    fn add_index<const SIZE: usize>(self, increment: usize) -> usize {
        if !CBuf::<(), SIZE>::IS_POWER_OF_TWO { return 0; }

        let (naive_sum, wrapped) = self.overflowing_add(increment);

        if !wrapped {
            naive_sum
        } else if naive_sum <= (usize::MAX - SIZE) {
            naive_sum.wrapping_add(SIZE)
        } else {
            naive_sum.wrapping_add(SIZE.wrapping_mul(2))
        }
    }

    #[inline]
    fn sub_index<const SIZE: usize>(self, decrement: usize) -> usize {
        if !CBuf::<(), SIZE>::IS_POWER_OF_TWO { return 0; }

        if self >= SIZE {
            let (mut difference, wrapped) = self.overflowing_sub(decrement);
            if wrapped { difference = difference.wrapping_sub(SIZE); }
            if difference < SIZE { difference = difference.wrapping_sub(SIZE); }
            difference
        } else {
            self.saturating_sub(decrement)
        }
    }

    #[inline]
    fn in_range<const SIZE: usize>(self, base: Self, len: Self) -> bool {
        let end_idx = base.add_index::<SIZE>(len);

        if end_idx > base {
            (base <= self) && (self < end_idx)
        } else {
            (base <= self) || ((SIZE <= self) && (self < end_idx))
        }
    }
}

