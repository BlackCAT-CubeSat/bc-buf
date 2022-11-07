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

use crate::utils::{AtomicIndex, BufIndex, Sequencer};
use core::ptr::{read_volatile, write_volatile};
use core::sync::atomic::{fence, Ordering::SeqCst};

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
    pub fn new(filler_item: T) -> Self {
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
    next: BufIndex<SIZE>,
}

pub struct CBufReader<'a, T: CBufItem, const SIZE: usize> {
    cbuf: &'a CBuf<T, SIZE>,
    next: BufIndex<SIZE>,
}

impl<'a, T: CBufItem, const SIZE: usize> CBufWriter<'a, T, SIZE> {
    const IS_SIZE_OK: bool = CBuf::<T, SIZE>::IS_SIZE_OK;
    const IDX_MASK: usize = CBuf::<T, SIZE>::IDX_MASK;

    pub unsafe fn from_ptr_init(cbuf: *mut CBuf<T, SIZE>) -> Option<Self> {
        if !Self::IS_SIZE_OK {
            return None;
        }
        let cbuf: &'a mut CBuf<T, SIZE> = cbuf.as_mut()?;

        cbuf.next.store(BufIndex::ZERO, SeqCst);

        Some(CBufWriter {
            cbuf: cbuf,
            next: BufIndex::ZERO,
        })
    }

    #[inline(always)]
    pub fn add_item(&mut self, item: T) {
        self.add_item_seq(item, &());
    }

    #[inline]
    pub(crate) fn add_item_seq<S: Sequencer<WriteProtocolStep>>(&mut self, item: T, seq: &S) {
        use core::ptr::addr_of_mut;

        macro_rules! wrap_atomic {
            ($label:ident, $($x:tt)*) => {
                seq.wait_for_go_ahead();
                { $($x)* }
                seq.send_result(WriteProtocolStep::$label);
            };
        }

        let next_next = self.next + 1;

        wrap_atomic! { PreWrite, }
        wrap_atomic! { BufferWrite,
            fence(SeqCst);
            unsafe { write_volatile(addr_of_mut!(self.cbuf.buf[self.next.as_usize() & Self::IDX_MASK]), item) };
            fence(SeqCst);
        }
        wrap_atomic! { IndexPostUpdate, self.cbuf.next.store(next_next, SeqCst); }

        self.next = next_next;
    }

    pub fn current_items<'b>(&'b mut self) -> impl Iterator<Item = T> + 'b + Captures<'a>
    where
        'a: 'b,
    {
        iter::CBufWriterIterator {
            idx:    self.next - (SIZE - 1),
            writer: self,
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

impl<'a, T: CBufItem, const SIZE: usize> CBufReader<'a, T, SIZE> {
    const IS_SIZE_OK: bool = CBuf::<T, SIZE>::IS_SIZE_OK;
    const IDX_MASK: usize = CBuf::<T, SIZE>::IDX_MASK;

    pub unsafe fn from_ptr(cbuf: *const CBuf<T, SIZE>) -> Option<Self> {
        if !Self::IS_SIZE_OK {
            return None;
        }
        let cbuf: &'a CBuf<T, SIZE> = cbuf.as_ref()?;

        Some(CBufReader {
            cbuf: cbuf,
            next: cbuf.next.load(SeqCst),
        })
    }

    const NUM_READ_TRIES: u32 = 16;

    #[inline]
    pub fn fetch_next_item(&mut self, fast_forward: bool) -> ReadResult<T> {
        self.fetch_next_item_seq(fast_forward, &())
    }

    #[inline]
    pub(crate) fn fetch_next_item_seq<S>(&mut self, fast_forward: bool, seq: &S) -> ReadResult<T>
    where
        S: Sequencer<FetchCheckpoint<ReadResult<T>>>,
    {
        use core::ptr::addr_of;

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

        let cbuf = self.cbuf;
        let mut skipped = false;

        for _ in 0..Self::NUM_READ_TRIES {
            let next_0 = wrap_atomic! { IndexCheckPre, cbuf.next.load(SeqCst) };
            let item = wrap_atomic! { BufferRead,
                fence(SeqCst);
                let item = unsafe { read_volatile(addr_of!(cbuf.buf[self.next.as_usize() & Self::IDX_MASK])) };
                fence(SeqCst);
                item
            };
            let next_1 = wrap_atomic! { IndexCheckPost, cbuf.next.load(SeqCst) };
            #[cfg(test)]
            std::eprintln!(
                "next: 0x{:02x}    0: 0x{:02x}    1: 0x{:02x}",
                self.next.as_usize(),
                next_0.as_usize(),
                next_1.as_usize()
            );

            let next_next = self.next + 1;

            if next_1 == BufIndex::ZERO {
                send_and_return!(RR::None);
            }
            if (self.next == next_0) && (self.next == next_1) {
                send_and_return!(RR::None);
            }

            if next_0.is_in_range(next_next, SIZE - 1) && next_1.is_in_range(next_next, SIZE - 1) {
                self.next = next_next;
                send_and_return!(if !skipped { RR::Success(item) } else { RR::Skipped(item) });
            }

            if !(next_1.is_in_range(next_next, SIZE - 1)) {
                // we've gotten too far behind, and we've gotten wrapped by the writer,
                // or else the circular buffer's been re-initialized;
                // in either case, we need to play catch-up
                let offset = if fast_forward { 1 } else { SIZE - 1 };
                self.next = next_1 - offset;
                skipped = true;
            }

            if next_0 != next_1 {
                // writer is active, let's give a hint to cool this thread's jets:
                core::hint::spin_loop();
            }
        }

        send_and_return!(RR::SpinFail);
    }

    pub fn available_items<'b>(
        &'b mut self,
        fast_forward: bool,
    ) -> impl Iterator<Item = ReadResult<T>> + 'b + Captures<'a>
    where
        'a: 'b,
    {
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
mod tests;
