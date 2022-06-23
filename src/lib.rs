#![no_std]

use core::sync::atomic::{fence, AtomicUsize, Ordering::SeqCst};
use core::ptr::{read_volatile, write_volatile};

#[repr(C)]
pub struct CBuf<T, const SIZE: usize> where T: Sized+Copy+'static {
    buf: [T; SIZE],
    next: AtomicUsize,
}

/// Calculates floor(log_2(`n`)).
const fn log2(n: usize) -> u32 {
    if n == 0 { panic!("tried to take log2 of 0"); }

    let (mut n, mut lg) = (n, 0);
    while n > 1 {
        n >>= 1;
        lg += 1;
    }

    lg
}

impl<T, const SIZE: usize> CBuf<T, SIZE> where T: Sized+Copy+'static {
    /// If `SIZE` is a power of two, as it should be, this is just `true`;
    /// otherwise, this generates a compile-time panic.
    const IS_POWER_OF_TWO: bool = if SIZE.is_power_of_two() { true }
    else { panic!("SIZE param of some CBuf is *not* a power of two") };

    const IDX_MASK: usize = if Self::IS_POWER_OF_TWO { SIZE - 1 } else { 0 };
    const EXP: u32 = log2(SIZE);
}

pub struct CBufWriter<'a, T, const SIZE: usize> where T: Sized+Copy+'static {
    cbuf: &'a mut CBuf<T, SIZE>,
    next: usize,
}

pub struct CBufReader<'a, T, const SIZE: usize> where T: Sized+Copy+'static {
    cbuf: &'a CBuf<T, SIZE>,
    next: usize,
}

trait IndexMath: Copy {
    fn add_index<const SIZE: usize>(self, increment: Self) -> Self;

    fn next_index<const SIZE: usize>(self) -> Self;

    #[inline]
    fn incr_index<const SIZE: usize>(&mut self) {
        *self = self.next_index::<SIZE>();
    }

    fn as_index_parts<const SIZE: usize>(self) -> (Self, Self);

    fn in_range<const SIZE: usize>(self, base: Self, len: Self) -> bool;
}

impl IndexMath for usize {
    #[inline]
    fn add_index<const SIZE: usize>(self, increment: usize) -> usize {
        if !CBuf::<(), SIZE>::IS_POWER_OF_TWO { return 0; }

        let (naive_sum, wrapped) = self.overflowing_add(increment);

        // not quite right in the case where (self, increment) == (usize::MAX, usize::MAX).
        if !wrapped { naive_sum } else { naive_sum.wrapping_add(SIZE) }
    }

    #[inline]
    fn next_index<const SIZE: usize>(self) -> usize { self.add_index::<SIZE>(1) }

    #[inline]
    fn as_index_parts<const SIZE: usize>(self) -> (usize, usize) {
        (self >> CBuf::<(), SIZE>::EXP, self & CBuf::<(), SIZE>::IDX_MASK)
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

impl<'a, T, const SIZE: usize> CBufWriter<'a, T, SIZE> where T: Sized+Copy+'static {
    pub unsafe fn from_ptr_init(cbuf: *mut CBuf<T, SIZE>) -> Option<Self> {
        if !CBuf::<T, SIZE>::IS_POWER_OF_TWO { return None; }
        let cbuf: &'a mut CBuf<T, SIZE> = cbuf.as_mut()?;

        cbuf.next.store(0, SeqCst);

        Some(CBufWriter { cbuf: cbuf, next: 0 })
    }

    pub fn add_item(&mut self, item: T) {
        #[allow(non_snake_case)]
        let IDX_MASK = CBuf::<T, SIZE>::IDX_MASK;

        let cbuf = &mut self.cbuf;

        fence(SeqCst);
        unsafe { write_volatile(&mut cbuf.buf[self.next & IDX_MASK], item) };
        fence(SeqCst);
        self.next.incr_index::<SIZE>();
        cbuf.next.store(self.next, SeqCst);
    }
}

pub enum ReadResult<T> {
    /// Normal case; fetched next item.
    Success(T),
    /// Fetched an item, but we missed some number.
    Skipped(T),
    /// No new items are available.
    None,
    /// After trying a number of times, not able to read.
    SpinFail,
}

impl<'a, T, const SIZE: usize> CBufReader<'a, T, SIZE> where T: Sized+Copy+'static {
    pub unsafe fn from_ptr(cbuf: *const CBuf<T, SIZE>) -> Option<Self> {
        if !CBuf::<T, SIZE>::IS_POWER_OF_TWO { return None; }
        let cbuf: &'a CBuf<T, SIZE> = cbuf.as_ref()?;

        Some(CBufReader { cbuf: cbuf, next: cbuf.next.load(SeqCst) })
    }

    const NUM_READ_TRIES: u32 = 16;

    pub fn fetch_next_item(&mut self, fast_forward: bool) -> ReadResult<T> {
        use ReadResult as RR;

        #[allow(non_snake_case)]
        let IDX_MASK = CBuf::<T, SIZE>::IDX_MASK;

        let cbuf = self.cbuf;
        let mut missed = false;

        for _ in 0..Self::NUM_READ_TRIES {
            let next_0 = cbuf.next.load(SeqCst);
            fence(SeqCst);
            let item = unsafe { read_volatile(&cbuf.buf[self.next & IDX_MASK]) };
            fence(SeqCst);
            let next_1 = cbuf.next.load(SeqCst);

            if next_1 == 0 { return RR::None; }

            if next_0.in_range::<SIZE>(self.next, SIZE) && next_1.in_range::<SIZE>(self.next, SIZE) {
                self.next.incr_index::<SIZE>();
                return if !missed { RR::Success(item) } else { RR::Skipped(item) };
            }

            // we need to play catch-up

            // the following isn't quite right in cases where next_1 < SIZE.
            //self.next = if fast_forward { next_1.wrapping_sub(1) } else { next_1.wrapping_sub(SIZE) };
            missed = true;
        }

        RR::SpinFail
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}
