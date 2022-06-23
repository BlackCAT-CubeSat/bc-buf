#![no_std]

use core::sync::atomic::{fence, AtomicUsize, Ordering::SeqCst};
use core::ptr::{read_volatile, write_volatile};

/// A convenience trait for possible items
/// read from and written to a circular buffer.
pub trait CBufItem: Sized + Copy + Send + 'static {}

/// Blanket implementation for all eligible types.
impl<T> CBufItem for T where T: Sized + Copy + Send + 'static {}

#[repr(C)]
pub struct CBuf<T: CBufItem, const SIZE: usize> {
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

/// Dummy trait used to satiate the Rust compiler
/// in certain uses of a lifetime inside the concrete type
/// used as an `impl Trait` return type.
///
/// Idea taken straight from [a comment in rust-users].
///
/// [a comment in rust-users]: https://users.rust-lang.org/t/lifetimes-in-smol-executor/59157/8?u=yandros
pub trait Captures<'_a> {}
impl<T: ?Sized> Captures<'_> for T {}

impl<T: CBufItem, const SIZE: usize> CBuf<T, SIZE> {
    /// If `SIZE` is a power of two, as it should be, this is just `true`;
    /// otherwise, this generates a compile-time panic.
    const IS_POWER_OF_TWO: bool = if SIZE.is_power_of_two() { true }
    else { panic!("SIZE param of some CBuf is *not* a power of two") };

    const IDX_MASK: usize = if Self::IS_POWER_OF_TWO { SIZE - 1 } else { 0 };
    const EXP: u32 = log2(SIZE);

    #[inline]
    pub fn new(filler_item: T) -> Self {
        let initial_next: usize = if Self::IS_POWER_OF_TWO { 0 } else { 0 };

        CBuf {
            buf: [filler_item; SIZE],
            next: AtomicUsize::new(initial_next),
        }
    }

    #[inline]
    pub unsafe fn initialize(p: *mut Self, filler_item: T) {
        use core::ptr::addr_of_mut;

        if p.is_null() || !Self::IS_POWER_OF_TWO { return; }

        for i in 0..SIZE {
            write_volatile(addr_of_mut!((*p).buf[i]), filler_item);
        }
        write_volatile(addr_of_mut!((*p).next), AtomicUsize::new(0));
        fence(SeqCst);
    }
}

impl<T: CBufItem + Default, const SIZE: usize> CBuf<T, SIZE> {
    #[inline]
    pub fn new_with_default() -> Self {
        Self::new(T::default())
    }

    #[inline]
    pub unsafe fn initialize_with_default(p: *mut Self) {
        Self::initialize(p, T::default());
    }
}

pub struct CBufWriter<'a, T: CBufItem, const SIZE: usize> {
    cbuf: &'a mut CBuf<T, SIZE>,
    next: usize,
}

pub struct CBufReader<'a, T: CBufItem, const SIZE: usize> {
    cbuf: &'a CBuf<T, SIZE>,
    next: usize,
}

trait IndexMath: Copy {
    fn add_index<const SIZE: usize>(self, increment: Self) -> Self;

    fn sub_index<const SIZE: usize>(self, decrement: Self) -> Self;

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

impl<'a, T: CBufItem, const SIZE: usize> CBufWriter<'a, T, SIZE> {
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
        let next_next = self.next.next_index::<SIZE>();

        fence(SeqCst);
        unsafe { write_volatile(&mut cbuf.buf[self.next & IDX_MASK], item) };
        fence(SeqCst);
        cbuf.next.store(next_next, SeqCst);

        self.next = next_next;
    }

    pub fn current_items<'b>(&'b mut self) -> impl Iterator<Item = T> + 'b + Captures<'a> where 'a: 'b {
        CBufWriterIterator {
            idx: self.next.saturating_sub(SIZE),
            writer: self,
        }
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

impl<'a, T: CBufItem, const SIZE: usize> CBufReader<'a, T, SIZE> {
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
            if (self.next == next_0) && (self.next == next_1) { return RR::None; }

            if next_0.in_range::<SIZE>(self.next, SIZE) && next_1.in_range::<SIZE>(self.next, SIZE) {
                self.next.incr_index::<SIZE>();
                return if !missed { RR::Success(item) } else { RR::Skipped(item) };
            }

            // we've gotten too far behind, and we've gotten wrapped by the writer,
            // or else the circular buffer's been re-initialized;
            // in either case, we need to play catch-up
            let offset = if fast_forward { 1 } else { SIZE };
            self.next = self.next.sub_index::<SIZE>(offset);
            missed = true;
        }

        RR::SpinFail
    }

    pub fn available_items<'b>(&'b mut self, fast_forward: bool) -> impl Iterator<Item = ReadResult<T>> + 'b + Captures<'a> where 'a: 'b {
        CBufReaderIterator {
            reader: self,
            fast_forward,
            is_done: false,
        }
    }
}

struct CBufWriterIterator<'a, 'b, T: CBufItem, const SIZE: usize> where 'a: 'b {
    writer: &'b mut CBufWriter<'a, T, SIZE>,
    idx: usize,
}

impl<'a, 'b, T: CBufItem, const SIZE: usize> Iterator for CBufWriterIterator<'a, 'b, T, SIZE> where 'a: 'b {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx == self.writer.next { return None; }

        let old_idx = self.idx;
        self.idx = old_idx.wrapping_add(1);
        Some(self.writer.cbuf.buf[old_idx & CBuf::<T, SIZE>::IDX_MASK])
    }
}

struct CBufReaderIterator<'a, 'b, T: CBufItem, const SIZE: usize> where 'a: 'b {
    reader: &'b mut CBufReader<'a, T, SIZE>,
    fast_forward: bool,
    is_done: bool,
}

impl<'a, 'b, T: CBufItem, const SIZE: usize> Iterator for CBufReaderIterator<'a, 'b, T, SIZE> where 'a: 'b {
    type Item = ReadResult<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.is_done { return None; }

        match self.reader.fetch_next_item(self.fast_forward) {
            ReadResult::None => { self.is_done = true; None }
            i => Some(i)
        }
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
