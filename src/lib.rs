// Copyright (c) 2022 The Pennsylvania State University and the project contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Nonblocking single-writer, multiple-reader circular buffers
//! for sharing data across threads and processes
//! (with possible misses by readers).

#![no_std]

#[cfg(test)]
extern crate std;

pub(crate) mod utils;
pub(crate) mod iter;

use core::sync::atomic::{fence, Ordering::SeqCst};
use core::ptr::{read_volatile, write_volatile};
use crate::utils::{BufIndex, Sequencer, AtomicIndex};

/// A convenience trait for possible items
/// read from and written to a circular buffer.
pub trait CBufItem: Sized + Copy + Send + 'static {}

/// Blanket implementation for all eligible types.
impl<T> CBufItem for T where T: Sized + Copy + Send + 'static {}

#[repr(C)]
pub struct CBuf<T: CBufItem, const SIZE: usize> {
    buf: [T; SIZE],
    next: AtomicIndex<SIZE>,
}

impl<T: CBufItem, const SIZE: usize> CBuf<T, SIZE> {
    /// If `SIZE` is a power of two that's greater than 1 and less than
    /// 2<sup>[`usize::BITS`]`-1`</sup>, as it should be, this is just `true`;
    /// otherwise, this generates a compile-time panic.
    const IS_SIZE_OK: bool = if SIZE.is_power_of_two() && SIZE < (usize::MAX >> 1) && SIZE > 1 { true }
    else { panic!("SIZE param of some CBuf is *not* an allowed value") };

    const IDX_MASK: usize = if Self::IS_SIZE_OK { SIZE - 1 } else { 0 };

    #[inline]
    pub fn new(filler_item: T) -> Self {
        let initial_next: usize = if Self::IS_SIZE_OK { 0 } else { 1 };

        CBuf {
            buf: [filler_item; SIZE],
            next: AtomicIndex::new(initial_next),
        }
    }

    #[inline]
    pub unsafe fn initialize(p: *mut Self, filler_item: T) {
        use core::ptr::addr_of_mut;

        if p.is_null() || !Self::IS_SIZE_OK { return; }

        for i in 0..SIZE {
            write_volatile(addr_of_mut!((*p).buf[i]), filler_item);
        }
        write_volatile(addr_of_mut!((*p).next), AtomicIndex::new(0));
        fence(SeqCst);
    }

    #[inline]
    pub fn as_writer<'a>(&'a mut self) -> CBufWriter<'a, T, SIZE> {
        CBufWriter {
            next: self.next.load(SeqCst).0,
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
        if !Self::IS_SIZE_OK { return None; }
        let cbuf: &'a mut CBuf<T, SIZE> = cbuf.as_mut()?;

        cbuf.next.store(BufIndex::ZERO, false, SeqCst);

        Some(CBufWriter { cbuf: cbuf, next: BufIndex::ZERO })
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

        wrap_atomic! { IndexPreUpdate, self.cbuf.next.store(self.next, true, SeqCst); }
        wrap_atomic! { BufferWrite,
            fence(SeqCst);
            unsafe { write_volatile(addr_of_mut!(self.cbuf.buf[self.next.as_usize() & Self::IDX_MASK]), item) };
            fence(SeqCst);
        }
        wrap_atomic! { IndexPostUpdate, self.cbuf.next.store(next_next, false, SeqCst); }

        self.next = next_next;
    }

    pub fn current_items<'b>(&'b mut self) -> impl Iterator<Item = T> + 'b + Captures<'a> where 'a: 'b {
        iter::CBufWriterIterator {
            idx: self.next.as_usize().saturating_sub(SIZE),
            writer: self,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum WriteProtocolStep {
    IndexPreUpdate,
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
        if !Self::IS_SIZE_OK { return None; }
        let cbuf: &'a CBuf<T, SIZE> = cbuf.as_ref()?;

        Some(CBufReader { cbuf: cbuf, next: cbuf.next.load(SeqCst).0 })
    }

    const NUM_READ_TRIES: u32 = 16;

    #[inline]
    pub fn fetch_next_item(&mut self, fast_forward: bool) -> ReadResult<T> {
        self.fetch_next_item_seq(fast_forward, &())
    }

    #[inline]
    pub(crate) fn fetch_next_item_seq<S>(&mut self, fast_forward: bool, seq: &S) -> ReadResult<T>
    where S: Sequencer<FetchCheckpoint<ReadResult<T>>> {
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
                let x = $result;
                seq.send_result(FetchCheckpoint::ReturnVal(x));
                return x;
            };
        }

        let cbuf = self.cbuf;
        let mut skipped = false;

        for _ in 0..Self::NUM_READ_TRIES {
            let (next_0, is_writing_0) = wrap_atomic! { IndexCheckPre, cbuf.next.load(SeqCst) };
            let item = wrap_atomic! { BufferRead,
                fence(SeqCst);
                let item = unsafe { read_volatile(addr_of!(cbuf.buf[self.next.as_usize() & Self::IDX_MASK])) };
                fence(SeqCst);
                item
            };
            let (next_1, is_writing_1) = wrap_atomic! { IndexCheckPost, cbuf.next.load(SeqCst) };

            if next_1 == BufIndex::ZERO { send_and_return!(RR::None); }
            if (self.next == next_0) && (self.next == next_1) { send_and_return!(RR::None); }

            let next_next = self.next + 1;
            let (idx_n, idx_0, idx_1) = (
                self.next.as_usize() & Self::IDX_MASK,
                next_0.as_usize() & Self::IDX_MASK,
                next_1.as_usize() & Self::IDX_MASK
            );

            if next_0.is_in_range(next_next, SIZE) && next_1.is_in_range(next_next, SIZE)
                && !(idx_0 == idx_n && is_writing_0) && !(idx_1 == idx_n && is_writing_1) {
                self.next = next_next;
                send_and_return!(if !skipped { RR::Success(item) } else { RR::Skipped(item) });
            }

            if !(next_1.is_in_range(next_next, SIZE)) {
                // we've gotten too far behind, and we've gotten wrapped by the writer,
                // or else the circular buffer's been re-initialized;
                // in either case, we need to play catch-up
                let offset = if fast_forward { 1 } else { SIZE };
                self.next = next_1 - offset;
                skipped = true;
            }

            if is_writing_0 || is_writing_1 || (next_0 != next_1) {
                // writer is active, let's give a hint to cool this thread's jets:
                core::hint::spin_loop();
            }
        }

        send_and_return!(RR::SpinFail);
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
    use super::ReadResult as RR;
    use core::mem::drop;
    use core::sync::atomic::Ordering::SeqCst;
    use std::thread::{spawn, JoinHandle};
    use std::sync::mpsc;
    use crate::utils::TestSequencer;
    use std::vec::Vec;

    #[test]
    fn can_construct_cbuf() {
        let a: CBuf<u32, 256> = CBuf::new(42);

        assert_eq!(a.next.load(SeqCst).0.as_usize(), 0usize);
        assert_eq!(a.buf.len(), 256);
        assert!(a.buf.iter().all(|x| *x == 42u32));

        let _b: CBuf<(u64, i32), 64> = CBuf::new((5u64, -3));

        let _c: CBuf<(), 16> = CBuf::new(());

        let _d: CBuf<(), 4096> = CBuf::new_with_default();

        let e: CBuf<isize, 128> = CBuf::new_with_default();

        assert_eq!(e.next.load(SeqCst).0.as_usize(), 0usize);
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

        assert_eq!(cb.next.load(SeqCst).0.as_usize(), 0usize);
        assert!(cb.buf.iter().all(|x| *x == 1729));
    }

    #[test]
    fn add_an_item() {
        fn run_cbuf_add_item(
            initial_buffer: [i16; 4], initial_next: usize,
            item: i16,
            final_buffer: [i16; 4], final_next: usize
        ) {
            let mut buf: CBuf<i16, 4> = CBuf { buf: initial_buffer, next: AtomicIndex::new(initial_next) };
            let mut writer = buf.as_writer();

            writer.add_item(item);
            assert_eq!(buf.buf, final_buffer);
            assert_eq!(buf.next.load(SeqCst).0.as_usize(), final_next & !(1usize << (usize::BITS - 1)));
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

        drop(cbuf);
    }

    macro_rules! assert_let {
        ($value:expr, $p:pat) => {
            let val = $value;
            match val {
                $p => (),
                _ => panic!(r"assertion failed: `left matches right`
  left: `{:?}`
 right: `{}`",
                    val, stringify!($p)
                )
            };
        };
    }

    macro_rules! step_writer {
        ($chan_pair:expr) => {
            let (ref goahead, ref result) = &$chan_pair;
            let _ = goahead.send(());
            assert_let!(result.recv(), Ok(_));
        };
    }

    macro_rules! step_reader {
        ($chan_pair:expr) => {
            let (ref goahead, ref result) = &$chan_pair;
            let _ = goahead.send(());
            assert_let!(result.recv(), Ok(FetchCheckpoint::Step(_)));
        };
    }

    macro_rules! expect_reader_ret {
        ($chan_pair:expr, $return_val:expr) => {
            let (_, ref result) = &$chan_pair;
            assert_eq!(result.recv(), Ok(FetchCheckpoint::ReturnVal($return_val)));
        };
    }

    #[test]
    fn very_simple_multithreaded() {
        let mut cbuf: CBuf<(u8, u16), 4> = CBuf::new((0, 0));
        let cbuf_ptr: *mut CBuf<(u8, u16), 4> = &mut cbuf;

        let mut writer = unsafe { CBufWriter::from_ptr_init(cbuf_ptr) }.unwrap();
        let mut reader = unsafe { CBufReader::from_ptr(cbuf_ptr) }.unwrap();

        let (ts_wr, chans_wr) = TestSequencer::new();
        let (ts_rd, chans_rd) = TestSequencer::new();

        let jh_wr = spawn(move || {
            writer.add_item_seq((1, 1), &ts_wr);
        });

        let jh_rd = spawn(move || {
            let _ = reader.fetch_next_item_seq(false, &ts_rd);
            let _ = reader.fetch_next_item_seq(false, &ts_rd);
        });

        for _ in 0..3 { step_reader!(chans_rd); }
        expect_reader_ret!(chans_rd, RR::None);

        for _ in 0..3 { step_writer!(chans_wr); }
        for _ in 0..3 { step_reader!(chans_rd); }
        expect_reader_ret!(chans_rd, RR::Success((1, 1)));

        for jh in [jh_wr, jh_rd] {
            let _ = jh.join();
        }

        drop(cbuf);
    }

    #[test]
    fn simple_interleaved_read_and_write() {
        let mut cbuf: CBuf<i16, 4> = CBuf::new(0);
        let cbuf_ptr: *mut CBuf<i16, 4> = &mut cbuf;

        let mut writer = unsafe { CBufWriter::from_ptr_init(cbuf_ptr) }.unwrap();
        let mut reader = unsafe { CBufReader::from_ptr(cbuf_ptr) }.unwrap();

        cbuf.buf = [-1, -2, -3, -4];
        cbuf.next.store(BufIndex::new(0x16), false, SeqCst);
        writer.next = BufIndex::new(0x16);
        reader.next = BufIndex::new(0x12);

        let (ts_wr, chans_wr) = TestSequencer::new();
        let (ts_rd, chans_rd) = TestSequencer::new();

        let jh_wr = spawn(move || {
            writer.add_item_seq(42, &ts_wr);
            writer.add_item_seq(43, &ts_wr);
            writer.add_item_seq(44, &ts_wr);
            writer.add_item_seq(45, &ts_wr);
        });
        let jh_rd = spawn(move || {
            let _ = reader.fetch_next_item_seq(false, &ts_rd);
            let _ = reader.fetch_next_item_seq(true, &ts_rd);
            let _ = reader.fetch_next_item_seq(false, &ts_rd);
        });

        step_reader!(chans_rd);
        for _ in 0..3 { step_writer!(chans_wr); }
        step_reader!(chans_rd);
        step_reader!(chans_rd);
        for _ in 0..3 { step_reader!(chans_rd); }
        expect_reader_ret!(chans_rd, RR::Skipped(-4));

        step_reader!(chans_rd);
        for _ in 0..(2*3) { step_writer!(chans_wr); }
        step_reader!(chans_rd);
        step_reader!(chans_rd);
        for _ in 0..3 { step_reader!(chans_rd); }
        expect_reader_ret!(chans_rd, RR::Skipped(44));

        step_reader!(chans_rd);
        for _ in 0..3 { step_writer!(chans_wr); }
        for _ in 0..2 { step_reader!(chans_rd); }
        for _ in 0..3 { step_reader!(chans_rd); }
        expect_reader_ret!(chans_rd, RR::Success(45));

        for jh in [jh_wr, jh_rd] {
            let _ = jh.join();
        }

        drop(cbuf);
    }

    #[test]
    fn get_to_spinfail() {
        #[allow(non_snake_case)]
        let NUM_READ_TRIES = CBufReader::<(), 4096>::NUM_READ_TRIES;

        let mut cbuf: CBuf<(), 4096> = CBuf::new_with_default();
        let cbuf_ptr: *mut CBuf<(), 4096> = &mut cbuf;

        let mut writer = unsafe { CBufWriter::from_ptr_init(cbuf_ptr) }.unwrap();
        let mut reader = unsafe { CBufReader::from_ptr(cbuf_ptr) }.unwrap();

        cbuf.next.store(BufIndex::new(0x2005), false, SeqCst);
        writer.next = BufIndex::new(0x2005);
        reader.next = BufIndex::new(0x1005);

        let (ts_wr, chans_wr) = TestSequencer::new();
        let (ts_rd, chans_rd) = TestSequencer::new();

        let join_handles = [
            spawn(move || {
                for _ in 0..NUM_READ_TRIES {
                    writer.add_item_seq((), &ts_wr);
                }
            }),
            spawn(move || {
                reader.fetch_next_item_seq(false, &ts_rd);
            })
        ];

        for _ in 0..NUM_READ_TRIES {
            step_reader!(chans_rd);

            for _ in 0..3 { step_writer!(chans_wr); }

            step_reader!(chans_rd);
            step_reader!(chans_rd);
        }
        expect_reader_ret!(chans_rd, RR::SpinFail);

        for jh in join_handles {
            let _ = jh.join();
        }

        drop(cbuf);
    }

    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    enum TraceStep<T> {
        Reader(FetchCheckpoint<ReadResult<T>>),
        Writer(WriteProtocolStep),
    }

    fn iterate_over_event_sequences<GEN, RD, WR, T, const SIZE: usize, A>(
        generator: &GEN,
        read_thread_generator: &RD,
        initial_read_next: usize,
        write_thread_generator: &WR,
        action: &mut A
    )
    where T: CBufItem,
    GEN: Fn() -> CBuf<T, SIZE>,
    RD: Fn(CBufReader<'static, T, SIZE>, TestSequencer<FetchCheckpoint<ReadResult<T>>>) -> JoinHandle<()>,
    WR: Fn(CBufWriter<'static, T, SIZE>, TestSequencer<WriteProtocolStep>) -> JoinHandle<()>,
    A: FnMut(&[TraceStep<T>]) {
        use std::boxed::Box;

        #[derive(Debug, PartialEq, Eq, Clone, Copy)]
        enum EventStep {
            Reader,
            Writer,
        }

        type ChannelPair<X> = (mpsc::Sender<()>, mpsc::Receiver<X>);

        struct RunningState<U, const SZ: usize> where U: CBufItem {
            cbuf: Box<CBuf<U, SZ>>,
            trace: Vec<TraceStep<U>>,
            chans_wr: ChannelPair<WriteProtocolStep>,
            chans_rd: ChannelPair<FetchCheckpoint<ReadResult<U>>>,
            jhandles: [JoinHandle<()>; 2],
        }

        // impl Fn(&[EventStep]) -> RunningState<T, SIZE>
        let mut replay_event_chain = |chain: &[EventStep]| {
            use EventStep as ES;
            use TraceStep as TS;

            //std::eprintln!("replaying {:?}", chain);

            let mut cbuf = Box::new(generator());
            let cbuf_ptr: *mut CBuf<T, SIZE> = cbuf.as_mut();
            let mut trace: Vec<TraceStep<T>> = Vec::with_capacity(chain.len());

            let buf_writer = CBufWriter {
                next: cbuf.next.load(SeqCst).0,
                cbuf: unsafe { &mut *cbuf_ptr },
            };
            let mut buf_reader = unsafe { CBufReader::from_ptr(cbuf_ptr) }.unwrap();
            buf_reader.next = BufIndex::new(initial_read_next);

            let (ts_wr, chans_wr) = TestSequencer::new();
            let (ts_rd, chans_rd) = TestSequencer::new();

            let jhandles = [
                write_thread_generator(buf_writer, ts_wr),
                read_thread_generator(buf_reader, ts_rd),
            ];

            for step in chain {
                match step {
                    ES::Reader => {
                        let (goahead, result) = &chans_rd;
                        let _ = goahead.send(());
                        match result.recv() {
                            Ok(r) => { trace.push(TS::Reader(r)); }
                            Err(e) => { panic!("Unexpected error `{:?}` during replay of event chain {:?}", e, chain); }
                        }
                    }
                    ES::Writer => {
                        let (goahead, result) = &chans_wr;
                        let _ = goahead.send(());
                        match result.recv() {
                            Ok(r) => { trace.push(TS::Writer(r)); }
                            Err(e) => { panic!("Unexpected error `{:?}` during replay of event chain {:?}", e, chain); }
                        }
                    }
                }
            }

            RunningState { cbuf, trace, chans_wr, chans_rd, jhandles }
        };

        let root_state = replay_event_chain(&[]);

        let mut recurse_over_event_chains = |
            event_steps: Vec<EventStep>,
            currently_running_state: RunningState<T, SIZE>
        | {
            // Helper function used to allow the logic of the closure to be recursive.
            // Technique due to <https://stackoverflow.com/a/72862424>.
            fn helper<REC, A, T, const SIZE: usize>(
                event_steps: Vec<EventStep>,
                currently_running_state: RunningState<T, SIZE>,
                replay_event_chain: &mut REC,
                action: &mut A
            ) where
            T: CBufItem,
            REC: FnMut(&[EventStep]) -> RunningState<T, SIZE>,
            A: FnMut(&[TraceStep<T>]) {
                use EventStep as ES;
                use TraceStep as TS;

                //std::eprintln!("recursing on {:?}", &event_steps[..]);

                // Try another writer step.
                let mut wr_events = event_steps.clone();
                let mut wr_trace = currently_running_state.trace.clone();

                let (goahead, result) = &currently_running_state.chans_wr;
                let _ = goahead.send(());
                match result.recv() {
                    Err(_) => {
                        // The writer thread has finished; run the reader to completion.
                        let (goahead, result) = &currently_running_state.chans_rd;
                        while let Ok(val) = { let _ = goahead.send(()); result.recv() } {
                            wr_trace.push(TS::Reader(val));
                        }
                        for jh in currently_running_state.jhandles {
                            let _ = jh.join();
                        }
                        drop(currently_running_state.cbuf);
                        //std::eprintln!("applying action on trace {:?}", &wr_events[..]);
                        action(&wr_trace);

                        // "Try another reader step" below would just
                        // repeat this sequence of events, so there's
                        // no need to run it.
                        return;
                    }
                    Ok(val) => {
                        wr_trace.push(TS::Writer(val));
                        wr_events.push(ES::Writer);
                        helper(wr_events, RunningState { trace: wr_trace, ..currently_running_state }, replay_event_chain, action);
                    }
                }

                // Try another reader step.
                // We consumed the passed-in threads in "try another writer step",
                // so we need to recreate them first.
                let mut reader_state = replay_event_chain(&event_steps);
                let mut reader_events = event_steps.clone();

                let (goahead, result) = &reader_state.chans_rd;
                let _ = goahead.send(());
                match result.recv() {
                    Err(_) => {
                        // The reader thread has finished. Wind up execution.
                        let (goahead, result) = &reader_state.chans_wr;
                        while let Ok(_) = { let _ = goahead.send(()); result.recv() } {}
                        for jh in reader_state.jhandles {
                            let _ = jh.join();
                        }
                        drop(reader_state.cbuf);

                        // If the situation was symmetrical between reader and writer,
                        // we'd now call action()... but we've already done that with
                        // this particular sequence of events in the recursion in
                        // "try another writer step" above, so we'd just be repeating
                        // that sequence.
                        return;
                    }
                    Ok(val) => {
                        reader_state.trace.push(TS::Reader(val));
                        reader_events.push(ES::Reader);
                        helper(reader_events, reader_state, replay_event_chain, action);
                    }
                }
            }
            helper(event_steps, currently_running_state, &mut replay_event_chain, action);
        };

        recurse_over_event_chains(Vec::new(), root_state);
    }

    // named after the unary iota function in APL
    const fn iota<const SIZE: usize>() -> [u32; SIZE] {
        let mut x = [0u32; SIZE];
        let mut i = 0;
        while i < SIZE {
            x[i] = i as u32;
            i += 1;
        }
        x
    }

    #[test]
    fn mini_model_example() {
        let mut i = 0usize;
        iterate_over_event_sequences(
            &|| {
                CBuf {
                    buf: iota::<16>(),
                    next: AtomicIndex::new(0x14),
                }
            },
            &|mut reader, sequencer| {
                spawn(move || {
                    let _ = reader.fetch_next_item_seq(false, &sequencer);
                })
            },
            0x13,
            &|mut writer, sequencer| {
                spawn(move || {
                    writer.add_item_seq(42, &sequencer);
                })
            },
            &mut |trace| {
                std::eprintln!("{}: {:?}", i, trace);
                i += 1;
                assert!(trace.len() > 0);
            }
        );
        //panic!("panicking just so we can see the list of all traces");
    }

    /// A test case with one write and one read where neither should interfere with each other.
    #[test]
    fn mini_model_no_interference_1w1r() {
        use TraceStep as TS;
        use FetchCheckpoint as FC;

        iterate_over_event_sequences(
            &|| {
                CBuf {
                    buf: iota::<16>(),
                    next: AtomicIndex::new(0x14),
                }
            },
            &|mut reader, sequencer| {
                spawn(move || {
                    let _ = reader.fetch_next_item_seq(false, &sequencer);
                })
            },
            0x11,
            &|mut writer, sequencer| {
                spawn(move || {
                    writer.add_item_seq(42, &sequencer);
                })
            },
            &mut |trace| {
                std::eprintln!("testing {:?}", trace);

                assert!(trace.len() > 0);

                assert_eq!(
                    trace.iter().filter(|ref t| matches!(t, TS::Reader(FC::ReturnVal(_)))).count(),
                    1
                );

                for t in trace {
                    if let TS::Reader(FC::ReturnVal(val)) = *t {
                        assert_eq!(val, ReadResult::Success(1));
                    }
                }
            }
        );
    }

    trait SliceExt {
        type Item;

        fn prev_with<F: Fn(&Self::Item) -> bool>(&self, index: usize, predicate: F) -> Option<Self::Item>;
        fn next_with<F: Fn(&Self::Item) -> bool>(&self, index: usize, predicate: F) -> Option<Self::Item>;
    }

    impl<T: Clone> SliceExt for [T] {
        type Item = T;

        fn prev_with<F: Fn(&Self::Item) -> bool>(&self, index: usize, predicate: F) -> Option<Self::Item> {
            let mut i = index;
            while i > 0 {
                i -= 1;
                if predicate(&self[i]) {
                    return Some(self[i].clone());
                }
            }
            None
        }

        fn next_with<F: Fn(&Self::Item) -> bool>(&self, index: usize, predicate: F) -> Option<Self::Item> {
            for i in &self[(index+1)..] {
                if predicate(i) {
                    return Some(i.clone());
                }
            }
            None
        }
    }

    macro_rules! prev_with_pat {
        ($array:expr, $index:expr, $pattern:pat) => {
            $array.prev_with($index, |ref item| matches!(item, $pattern))
        }
    }

    macro_rules! next_with_pat {
        ($array:expr, $index:expr, $pattern:pat) => {
            $array.next_with($index, |ref item| matches!(item, $pattern))
        }
    }

    /// A test case with one write and one read where interference is possible in some cases.
    #[test]
    fn mini_model_interference_1w1r() {
        use TraceStep as TS;
        use FetchCheckpoint as FC;
        use ReadProtocolStep as RPS;
        use WriteProtocolStep as WPS;

        iterate_over_event_sequences(
            &|| {
                CBuf {
                    buf: iota::<16>(),
                    next: AtomicIndex::new(0x24),
                }
            },
            &|mut reader, sequencer| {
                spawn(move || {
                    let _ = reader.fetch_next_item_seq(false, &sequencer);
                })
            },
            0x14,
            &|mut writer, sequencer| {
                spawn(move || {
                    writer.add_item_seq(42, &sequencer);
                })
            },
            &mut |trace| {
                std::eprintln!("testing {:?}", trace);

                // something should have happened
                assert!(trace.len() > 0);

                // there should be one return from fetch_next_item_seq() :)
                assert_eq!(
                    trace.iter().filter(|t| matches!(t, TS::Reader(FC::ReturnVal(_)))).count(),
                    1
                );

                // return value should be one of Success(4), Skipped(5), and SpinFail
                let return_value = match prev_with_pat!(trace, trace.len(), TS::Reader(FC::ReturnVal(_))) {
                    Some(TS::Reader(FC::ReturnVal(rval))) => rval,
                    _ => unreachable!(),
                };
                assert_let!(return_value, RR::Success(4) | RR::Skipped(5) | RR::SpinFail);

                for (i, t) in trace.iter().enumerate() {
                    // if we read from the buffer entry in a temporal interval
                    // containing a write to that entry, make sure we read again afterward
                    // (or call it quits with a return of SpinFail).
                    if *t == TS::Reader(FC::Step(RPS::BufferRead)) {
                        match prev_with_pat!(trace, i, TS::Writer(_)) {
                            Some(TS::Writer(step)) if step != WPS::IndexPostUpdate => {
                                assert!(next_with_pat!(trace, i, TS::Reader(FC::Step(RPS::BufferRead)) | TS::Reader(FC::ReturnVal(RR::SpinFail))).is_some());
                            }
                            _ => (),
                        }
                    }

                    // the last buffer read should occur either before the write sequence starts
                    // or after the write sequence ends (or we return SpinFail).
                    if *t == TS::Reader(FC::Step(RPS::BufferRead)) && next_with_pat!(trace, i, TS::Reader(FC::Step(RPS::BufferRead))).is_none() {
                        let prev_write_step = prev_with_pat!(trace, i, TS::Writer(_));
                        let next_write_step = next_with_pat!(trace, i, TS::Writer(_));

                        assert!((prev_write_step == Some(TS::Writer(WPS::IndexPostUpdate)) && next_write_step == None)
                             || (prev_write_step == None && next_write_step == Some(TS::Writer(WPS::IndexPreUpdate)))
                             || return_value == RR::SpinFail,
                            "last read should be entirely before or entirely after write sequence");
                    }

                    // if the last read sequence occurs entirely before the write sequence,
                    // we should return Success(4)
                    if *t == TS::Reader(FC::Step(RPS::IndexCheckPost)) && next_with_pat!(trace, i, TS::Reader(FC::Step(RPS::IndexCheckPost))).is_none() {
                        if prev_with_pat!(trace, i, TS::Writer(_)).is_none() {
                            assert_eq!(return_value, RR::Success(4));
                        }
                    }

                    // if the last read sequence occurs entirely after the write sequence,
                    // we should return Skipped(5) or, if *right* after the write sequence,
                    // possibly SpinFail
                    if *t == TS::Reader(FC::Step(RPS::IndexCheckPre)) && next_with_pat!(trace, i, TS::Reader(FC::Step(RPS::IndexCheckPre))).is_none() {
                        if next_with_pat!(trace, i, TS::Writer(_)).is_none() {
                            if i >= 1 && matches!(trace[i-1], TS::Writer(_)) {
                                assert_let!(return_value, RR::Skipped(5) | RR::SpinFail);
                            } else {
                                assert_eq!(return_value, RR::Skipped(5));
                            }
                        }
                    }
                }
            }
        );
    }
}
