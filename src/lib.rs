// Copyright (c) 2022 The Pennsylvania State University and the project contributors.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Nonblocking single-writer, multiple-reader,
//! zero-or-one-allocation circular buffers
//! for sharing data across threads and processes
//! (with possible misses by readers).

#![no_std]

#[cfg(test)]
extern crate std;

pub(crate) mod iter;
pub(crate) mod utils;

pub use crate::utils::CBufIndex;
use crate::utils::{AtomicIndex, Sequencer};

use core::ptr::{read_volatile, write_volatile};
use core::sync::atomic::{fence, AtomicUsize, Ordering::SeqCst};

/// A convenience trait for possible items
/// read from and written to a circular buffer.
pub trait CBufItem: Sized + Copy + Send + 'static {}

/// Blanket implementation for all eligible types.
impl<T> CBufItem for T where T: Sized + Copy + Send + 'static {}

#[repr(C)]
pub struct CBuf<T: CBufItem, const SIZE: usize> {
    buf:  [T; SIZE],
    next: AtomicIndex<SIZE>,
}

pub struct CBufReader<'a, T: CBufItem, const SIZE: usize> {
    buf:        *const T,
    next_ref:   &'a AtomicIndex<SIZE>,
    next_local: CBufIndex<SIZE>,
}

pub struct CBufWriter<'a, T: CBufItem, const SIZE: usize> {
    buf:        *mut T,
    next_ref:   &'a AtomicIndex<SIZE>,
    next_local: CBufIndex<SIZE>,
}

impl<T: CBufItem, const SIZE: usize> CBuf<T, SIZE> {
    /// If `SIZE` is a power of two that's greater than 1 and less than
    /// 2<sup>[`usize::BITS`]`-1`</sup>, as it should be, this is just `true`;
    /// otherwise, this generates a compile-time panic.
    const IS_SIZE_OK: bool = if SIZE.is_power_of_two() && SIZE > 1 {
        true
    } else {
        panic!("SIZE param of some CBuf is *not* an allowed value")
    };

    const IDX_MASK: usize = if Self::IS_SIZE_OK { SIZE - 1 } else { 0 };

    #[inline]
    pub const fn new(filler_item: T) -> Self {
        let initial_next: usize = if Self::IS_SIZE_OK { 0 } else { 1 };

        CBuf {
            buf:  [filler_item; SIZE],
            next: AtomicIndex::new(initial_next),
        }
    }

    #[inline]
    pub unsafe fn initialize(p: *mut Self, filler_item: T) {
        use core::ptr::addr_of_mut;

        if p.is_null() || !Self::IS_SIZE_OK {
            return;
        }

        for i in 0..SIZE {
            write_volatile(addr_of_mut!((*p).buf[i]), filler_item);
        }
        write_volatile(addr_of_mut!((*p).next), AtomicIndex::new(0));
        fence(SeqCst);
    }

    #[inline]
    pub fn as_writer<'a>(&'a mut self) -> CBufWriter<'a, T, SIZE> {
        CBufWriter {
            buf:        self.buf.as_mut_ptr(),
            next_ref:   &self.next,
            next_local: self.next.load(SeqCst),
        }
    }

    #[inline]
    pub const fn as_ptrs(&self) -> (*const T, *const AtomicUsize) {
        (self.buf.as_ptr(), &self.next.n)
    }

    #[inline]
    pub fn as_mut_ptrs(&mut self) -> (*mut T, *const AtomicUsize) {
        (self.buf.as_mut_ptr(), &self.next.n)
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

unsafe impl<'a, T: CBufItem, const SIZE: usize> Send for CBufWriter<'a, T, SIZE> {}

impl<'a, T: CBufItem, const SIZE: usize> CBufWriter<'a, T, SIZE> {
    const IS_SIZE_OK: bool = CBuf::<T, SIZE>::IS_SIZE_OK;
    const IDX_MASK: usize = CBuf::<T, SIZE>::IDX_MASK;

    #[inline]
    pub unsafe fn new_from_ptr(buf: *mut T, next_idx: *const AtomicUsize) -> Option<Self> {
        if !Self::IS_SIZE_OK || buf.is_null() || next_idx.is_null()
        /*|| !buf.is_aligned() || !next_idx.is_aligned()*/
        {
            return None;
        }

        let next_ref: &AtomicIndex<SIZE> = &*(next_idx as *const AtomicIndex<SIZE>);
        Some(Self {
            buf,
            next_ref,
            next_local: next_ref.load(SeqCst),
        })
    }

    #[inline(always)]
    pub fn add_item(&mut self, item: T) {
        self.add_item_seq(item, &());
    }

    #[inline]
    pub(crate) fn add_item_seq<S: Sequencer<WriteProtocolStep>>(&mut self, item: T, seq: &S) {
        macro_rules! wrap_atomic {
            ($label:ident, $($x:tt)*) => {
                seq.wait_for_go_ahead();
                { $($x)* }
                seq.send_result(WriteProtocolStep::$label);
            };
        }

        let next_next = self.next_local + 1;

        wrap_atomic! { PreWrite, }
        wrap_atomic! { BufferWrite,
            fence(SeqCst);
            unsafe { write_volatile(self.buf.add(self.next_local.as_usize() & Self::IDX_MASK), item) };
            fence(SeqCst);
        }
        wrap_atomic! { IndexPostUpdate, self.next_ref.store(next_next, SeqCst); }

        self.next_local = next_next;
    }

    #[inline]
    pub fn current_items_iter<'b>(&'b mut self) -> impl Iterator<Item = T> + 'b + Captures<'a>
    where
        'a: 'b,
    {
        iter::WriterIterator {
            writer_next: self.next_local,
            buf:         unsafe { &*(self.buf as *const [T; SIZE]) },
            idx:         self.next_local - (SIZE - 1),
            _writer:     self,
        }
    }
}

unsafe impl<'a, T: CBufItem, const SIZE: usize> Send for CBufReader<'a, T, SIZE> {}

impl<'a, T: CBufItem, const SIZE: usize> CBufReader<'a, T, SIZE> {
    const IS_SIZE_OK: bool = CBuf::<T, SIZE>::IS_SIZE_OK;
    const IDX_MASK: usize = CBuf::<T, SIZE>::IDX_MASK;

    const NUM_READ_TRIES: u32 = 16;

    #[inline]
    pub unsafe fn new_from_ptr(buf: *const T, next_idx: *const AtomicUsize) -> Option<Self> {
        if !Self::IS_SIZE_OK || buf.is_null() || next_idx.is_null()
        /*|| !buf.is_aligned() || !next_idx.is_aligned()*/
        {
            return None;
        }

        let next_ref: &AtomicIndex<SIZE> = &*(next_idx as *const AtomicIndex<SIZE>);
        Some(Self {
            buf,
            next_ref,
            next_local: next_ref.load(SeqCst),
        })
    }

    #[inline(always)]
    pub fn fetch_next_item(&mut self, fast_forward: bool) -> ReadResult<T> {
        self.fetch_next_item_seq(fast_forward, &())
    }

    #[inline]
    pub(crate) fn fetch_next_item_seq<S>(&mut self, fast_forward: bool, seq: &S) -> ReadResult<T>
    where
        S: Sequencer<FetchCheckpoint<ReadResult<T>>>,
    {
        use ReadResult as RR;

        macro_rules! wrap_atomic {
            ($label:ident, $($x:tt)*) => {
                {
                    seq.wait_for_go_ahead();
                    let x = { $($x)* };
                    seq.send_result(FetchCheckpoint::Step(ReadProtocolStep::$label));
                    x
                }
            };
        }
        macro_rules! send_and_return {
            ($result:expr) => {
                seq.wait_for_go_ahead();
                let x = $result;
                seq.send_result(FetchCheckpoint::ReturnVal(x));
                return x;
            };
        }

        let mut skipped = false;

        for _ in 0..Self::NUM_READ_TRIES {
            let next_0 = wrap_atomic! { IndexCheckPre, self.next_ref.load(SeqCst) };
            let item = wrap_atomic! { BufferRead,
                fence(SeqCst);
                let item = unsafe { read_volatile(self.buf.add(self.next_local.as_usize() & Self::IDX_MASK)) };
                fence(SeqCst);
                item
            };
            let next_1 = wrap_atomic! { IndexCheckPost, self.next_ref.load(SeqCst) };
            #[cfg(test)]
            std::eprintln!(
                "next: 0x{:02x}    0: 0x{:02x}    1: 0x{:02x}",
                self.next_local.as_usize(),
                next_0.as_usize(),
                next_1.as_usize()
            );

            let next_next = self.next_local + 1;

            if next_1 == CBufIndex::ZERO {
                send_and_return!(RR::None);
            }
            if (self.next_local == next_0) && (self.next_local == next_1) {
                send_and_return!(RR::None);
            }

            if next_0.is_in_range(next_next, SIZE - 1) && next_1.is_in_range(next_next, SIZE - 1) {
                self.next_local = next_next;
                send_and_return!(if !skipped { RR::Success(item) } else { RR::Skipped(item) });
            }

            if !(next_1.is_in_range(next_next, SIZE - 1)) {
                // we've gotten too far behind, and we've gotten wrapped by the writer,
                // or else the circular buffer's been re-initialized;
                // in either case, we need to play catch-up
                let offset = if fast_forward { 1 } else { SIZE - 1 };
                self.next_local = next_1 - offset;
                skipped = true;
            }

            if next_0 != next_1 {
                // writer is active, let's give a hint to cool this thread's jets:
                core::hint::spin_loop();
            }
        }

        send_and_return!(RR::SpinFail);
    }

    pub fn available_items_iter<'b>(
        &'b mut self,
        fast_forward: bool,
    ) -> impl Iterator<Item = ReadResult<T>> + 'b + Captures<'a>
    where
        'a: 'b,
    {
        iter::ReaderIterator {
            reader: self,
            fast_forward,
            is_done: false,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum WriteProtocolStep {
    PreWrite,
    BufferWrite,
    IndexPostUpdate,
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

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ReadProtocolStep {
    IndexCheckPre,
    BufferRead,
    IndexCheckPost,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum FetchCheckpoint<T> {
    Step(ReadProtocolStep),
    ReturnVal(T),
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
mod tests;
