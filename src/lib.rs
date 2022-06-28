//! Nonblocking single-writer, multiple-reader circular buffers
//! for sharing data across threads and processes
//! (with possible misses by readers).

#![no_std]

pub(crate) mod utils;
pub(crate) mod iter;

use core::sync::atomic::{fence, AtomicUsize, Ordering::SeqCst};
use core::ptr::{read_volatile, write_volatile};
use crate::utils::IndexMath;

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

impl<T: CBufItem, const SIZE: usize> CBuf<T, SIZE> {
    /// If `SIZE` is a power of two, as it should be, this is just `true`;
    /// otherwise, this generates a compile-time panic.
    const IS_POWER_OF_TWO: bool = if SIZE.is_power_of_two() { true }
    else { panic!("SIZE param of some CBuf is *not* a power of two") };

    const IDX_MASK: usize = if Self::IS_POWER_OF_TWO { SIZE - 1 } else { 0 };

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

    #[inline]
    pub fn as_writer<'a>(&'a mut self) -> CBufWriter<'a, T, SIZE> {
        CBufWriter {
            next: self.next.load(SeqCst),
            cbuf: self,
        }
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

impl<'a, T: CBufItem, const SIZE: usize> CBufWriter<'a, T, SIZE> {
    pub unsafe fn from_ptr_init(cbuf: *mut CBuf<T, SIZE>) -> Option<Self> {
        if !CBuf::<T, SIZE>::IS_POWER_OF_TWO { return None; }
        let cbuf: &'a mut CBuf<T, SIZE> = cbuf.as_mut()?;

        cbuf.next.store(0, SeqCst);

        Some(CBufWriter { cbuf: cbuf, next: 0 })
    }

    pub fn add_item(&mut self, item: T) {
        use core::ptr::addr_of_mut;

        #[allow(non_snake_case)]
        let IDX_MASK = CBuf::<T, SIZE>::IDX_MASK;

        let cbuf = &mut self.cbuf;
        let next_next = self.next.next_index::<SIZE>();

        fence(SeqCst);
        unsafe { write_volatile(addr_of_mut!(cbuf.buf[self.next & IDX_MASK]), item) };
        fence(SeqCst);
        cbuf.next.store(next_next, SeqCst);

        self.next = next_next;
    }

    pub fn current_items<'b>(&'b mut self) -> impl Iterator<Item = T> + 'b + Captures<'a> where 'a: 'b {
        iter::CBufWriterIterator {
            idx: self.next.saturating_sub(SIZE),
            writer: self,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
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
        use core::ptr::addr_of;

        use ReadResult as RR;

        #[allow(non_snake_case)]
        let IDX_MASK = CBuf::<T, SIZE>::IDX_MASK;

        let cbuf = self.cbuf;
        let mut missed = false;

        for _ in 0..Self::NUM_READ_TRIES {
            let next_0 = cbuf.next.load(SeqCst);
            fence(SeqCst);
            let item = unsafe { read_volatile(addr_of!(cbuf.buf[self.next & IDX_MASK])) };
            fence(SeqCst);
            let next_1 = cbuf.next.load(SeqCst);

            if next_1 == 0 { return RR::None; }
            if (self.next == next_0) && (self.next == next_1) { return RR::None; }

            let ok_next_01_base = self.next.next_index::<SIZE>();
            if next_0.in_range::<SIZE>(ok_next_01_base, SIZE) && next_1.in_range::<SIZE>(ok_next_01_base, SIZE) {
                self.next.incr_index::<SIZE>();
                return if !missed { RR::Success(item) } else { RR::Skipped(item) };
            }

            // we've gotten too far behind, and we've gotten wrapped by the writer,
            // or else the circular buffer's been re-initialized;
            // in either case, we need to play catch-up
            let offset = if fast_forward { 1 } else { SIZE };
            self.next = next_1.sub_index::<SIZE>(offset);
            missed = true;
        }

        RR::SpinFail
    }

    pub fn available_items<'b>(&'b mut self, fast_forward: bool) -> impl Iterator<Item = ReadResult<T>> + 'b + Captures<'a> where 'a: 'b {
        iter::CBufReaderIterator {
            reader: self,
            fast_forward,
            is_done: false,
        }
    }
}

/// Dummy trait used to satiate the Rust compiler
/// in certain uses of lifetimes inside the concrete type
/// behind a function/method's `impl Trait` return type.
///
/// Idea taken straight from [a comment in rust-users].
///
/// [a comment in rust-users]: https://users.rust-lang.org/t/lifetimes-in-smol-executor/59157/8?u=yandros
pub trait Captures<'_a> {}
impl<T: ?Sized> Captures<'_> for T {}

#[cfg(test)]
mod tests {
    use super::*;
    use core::sync::atomic::AtomicUsize;
    use core::sync::atomic::Ordering::SeqCst;

    #[test]
    fn can_construct_cbuf() {
        let a: CBuf<u32, 256> = CBuf::new(42);

        assert_eq!(a.next.load(SeqCst), 0usize);
        assert_eq!(a.buf.len(), 256);
        assert!(a.buf.iter().all(|x| *x == 42u32));

        let _b: CBuf<(u64, i32), 64> = CBuf::new((5u64, -3));

        let _c: CBuf<(), 16> = CBuf::new(());

        let _d: CBuf<(), 4096> = CBuf::new_with_default();

        let e: CBuf<isize, 128> = CBuf::new_with_default();

        assert_eq!(e.next.load(SeqCst), 0usize);
        assert_eq!(e.buf.len(), 128);
        assert!(e.buf.iter().all(|x| *x == <isize as Default>::default()));
    }

    #[test]
    fn can_initialize_cbuf() {
        use core::mem::MaybeUninit;

        let mut un_cb: MaybeUninit<CBuf<u16, 128>> = MaybeUninit::uninit();
        let cb = unsafe {
            CBuf::initialize(un_cb.as_mut_ptr(), 1729);
            un_cb.assume_init()
        };

        assert_eq!(cb.next.load(SeqCst), 0usize);
        assert!(cb.buf.iter().all(|x| *x == 1729));
    }

    #[test]
    fn add_an_item() {
        fn run_cbuf_add_item(
            initial_buffer: [i16; 4], initial_next: usize,
            item: i16,
            final_buffer: [i16; 4], final_next: usize
        ) {
            let mut buf: CBuf<i16, 4> = CBuf { buf: initial_buffer, next: AtomicUsize::new(initial_next) };
            let mut writer = buf.as_writer();

            writer.add_item(item);
            assert_eq!(buf.buf, final_buffer);
            assert_eq!(buf.next.load(SeqCst), final_next);
        }

        run_cbuf_add_item(
            [-1, -2, -3, -4], 0,
            99,
            [99, -2, -3, -4], 1
        );

        run_cbuf_add_item(
            [99, -2, -3, -4], 1,
            101,
            [99, 101, -3, -4], 2
        );

        run_cbuf_add_item(
            [-1, -2, -3, -4], 3,
            99,
            [-1, -2, -3, 99], 4
        );

        run_cbuf_add_item(
            [-1, -2, -3, 99], 4,
            101,
            [101, -2, -3, 99], 5
        );

        run_cbuf_add_item(
            [-1, -2, -3, -4], 0x12,
            99,
            [-1, -2, 99, -4], 0x13
        );

        run_cbuf_add_item(
            [-1, -2, 99, -4], 0x13,
            101,
            [-1, -2, 99, 101], 0x14
        );

        run_cbuf_add_item(
            [-1, -2, 99, 101], 0x14,
            202,
            [202, -2, 99, 101], 0x15
        );

        run_cbuf_add_item(
            [-1, -2, -3, -4], usize::MAX - 1,
            99,
            [-1, -2, 99, -4], usize::MAX
        );

        run_cbuf_add_item(
            [-1, -2, 99, -4], usize::MAX,
            101,
            [-1, -2, 99, 101], 4
        );
    }

    #[test]
    fn write_then_read() {
        use super::ReadResult as RR;

        let mut cbuf: CBuf<u32, 16> = CBuf::new_with_default();
        let cbuf_ptr: *mut CBuf<u32, 16> = &mut cbuf;

        let mut writer = unsafe { CBufWriter::from_ptr_init(cbuf_ptr) }.unwrap();
        let mut reader1 = unsafe { CBufReader::from_ptr(cbuf_ptr) }.unwrap();

        assert_eq!(reader1.fetch_next_item(false), RR::None);

        writer.add_item(42);
        assert_eq!(reader1.fetch_next_item(false), RR::Success(42));

        let mut reader2 = unsafe { CBufReader::from_ptr(cbuf_ptr) }.unwrap();
        assert_eq!(reader2.fetch_next_item(false), RR::None);

        writer.add_item(43);
        assert_eq!(reader1.fetch_next_item(false), RR::Success(43));

        writer.add_item(44);
        assert_eq!(reader1.fetch_next_item(false), RR::Success(44));
        assert_eq!(reader1.fetch_next_item(false), RR::None);
        assert_eq!(reader2.fetch_next_item(false), RR::Success(43));
        assert_eq!(reader2.fetch_next_item(false), RR::Success(44));
        assert_eq!(reader2.fetch_next_item(false), RR::None);

        for _ in 0..3 {
            writer.add_item(99);
            assert_eq!(reader1.fetch_next_item(false), RR::Success(99));
        }

        for i in 100..116 {
            writer.add_item(i);
            assert_eq!(reader1.fetch_next_item(false), RR::Success(i));
        }

        assert_eq!(reader2.fetch_next_item(false), RR::Skipped(100));
        for i in 101..116 {
            assert_eq!(reader2.fetch_next_item(false), RR::Success(i));
        }

        for i in 200..216 {
            writer.add_item(i);
        }
        for i in 200..216 {
            assert_eq!(reader1.fetch_next_item(false), RR::Success(i));
        }

        writer.add_item(300);
        assert_eq!(reader2.fetch_next_item(true), RR::Skipped(300));

        core::mem::drop(cbuf);
    }
}
