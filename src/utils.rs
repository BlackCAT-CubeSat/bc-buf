// Copyright (c) 2022 The Pennsylvania State University and the project contributors.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! 

use super::CBuf;

use core::ops::{Add, Sub, AddAssign, SubAssign};
use core::sync::atomic::{AtomicUsize, Ordering};

#[cfg(test)]
use std::sync::mpsc;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct BufIndex<const SIZE: usize> {
    idx: usize
}

impl<const SIZE: usize> BufIndex<SIZE> {
    const IS_SIZE_OK: bool = CBuf::<(), SIZE>::IS_SIZE_OK;

    #[inline]
    pub const fn new(raw_val: usize) -> Self {
        if !Self::IS_SIZE_OK { return Self { idx: 0 }; }

        Self { idx: raw_val }
    }

    pub const ZERO: Self = Self::new(0);

    #[inline]
    pub const fn as_usize(self) -> usize {
        self.idx
    }
}

impl<const SIZE: usize> Default for BufIndex<SIZE> {
    #[inline]
    fn default() -> Self {
        Self::new(0)
    }
}

impl<const SIZE: usize> Add<usize> for BufIndex<SIZE> {
    type Output = Self;

    #[inline]
    fn add(self, increment: usize) -> Self {
        if !Self::IS_SIZE_OK { return Self { idx: 0 }; }

        let (naive_sum, wrapped) = self.idx.overflowing_add(increment);

        let final_sum = if !wrapped {
            naive_sum
        } else if naive_sum <= (usize::MAX - SIZE) {
            naive_sum.wrapping_add(SIZE)
        } else {
            naive_sum.wrapping_add(SIZE.wrapping_mul(2))
        };
        Self { idx: final_sum }
    }
}

impl<const SIZE: usize> AddAssign<usize> for BufIndex<SIZE> {
    #[inline]
    fn add_assign(&mut self, increment: usize) {
        *self = *self + increment;
    }
}

impl<const SIZE: usize> Sub<usize> for BufIndex<SIZE> {
    type Output = Self;

    #[inline]
    fn sub(self, decrement: usize) -> Self {
        if !Self::IS_SIZE_OK { return Self { idx: 0 }; }

        let result = if self.idx >= SIZE {
            let (mut difference, wrapped) = self.idx.overflowing_sub(decrement);
            if wrapped { difference = difference.wrapping_sub(SIZE); }
            if difference < SIZE { difference = difference.wrapping_sub(SIZE); }
            difference
        } else {
            self.idx.saturating_sub(decrement)
        };
        Self { idx: result }
    }
}

impl<const SIZE: usize> SubAssign<usize> for BufIndex<SIZE> {
    #[inline]
    fn sub_assign(&mut self, decrement: usize) {
        *self = *self - decrement;
    }
}

impl<const SIZE: usize> BufIndex<SIZE> {
    const LOOP_LENGTH: usize = usize::MAX - SIZE + 1;

    #[inline]
    pub fn is_in_range(self, base: Self, len: usize) -> bool {
        if !Self::IS_SIZE_OK { return false; }

        let (idx, base_) = (self.idx, base.idx);

        if base_ < SIZE {
            let (end_idx, overflow) = base_.overflowing_add(len);
            (base_ <= idx) && (overflow || (idx < end_idx))
        } else if len >= Self::LOOP_LENGTH {
            SIZE <= idx
        } else {
            let end = (base + len).idx;

            if end >= base_ {
                (base_ <= idx) && (idx < end)
            } else {
                (base_ <= idx) || ((SIZE <= idx) && (idx < end))
            }
        }
    }
}

#[repr(transparent)]
pub(crate) struct AtomicIndex<const SIZE: usize> {
    n: AtomicUsize
}

impl <const SIZE: usize> AtomicIndex<SIZE> {
    #[inline]
    pub(crate) const fn new(n: usize) -> Self {
        Self { n: AtomicUsize::new(n) }
    }

    #[inline]
    pub(crate) fn load(&self, order: Ordering) -> BufIndex<SIZE> {
        BufIndex { idx: self.n.load(order) }
    }

    #[inline]
    pub(crate) fn store(&self, idx: BufIndex<SIZE>, order: Ordering) {
        self.n.store(idx.idx, order);
    }
}

/// Used in multithreaded tests for reproducible sequencing of events
/// and reporting of results.
pub(crate) trait Sequencer<T: Send> {
    fn wait_for_go_ahead(&self);

    fn send_result(&self, result: T);
}

/// A null implementation for use everywhere except tests.
impl<T: Send> Sequencer<T> for () {
    #[inline(always)]
    fn wait_for_go_ahead(&self) {}

    #[inline(always)]
    fn send_result(&self, _result: T) {}
}

#[cfg(test)]
pub(crate) struct TestSequencer<T: Send> {
    rcv_chan: mpsc::Receiver<()>,
    send_chan: mpsc::Sender<T>,
}

#[cfg(test)]
impl<T: Send> TestSequencer<T> {
    pub(crate) fn new() -> (Self, (mpsc::Sender<()>, mpsc::Receiver<T>)) {
        let (snd0, rcv0) = mpsc::channel::<()>();
        let (snd1, rcv1) = mpsc::channel::<T>();

        (
            TestSequencer { rcv_chan: rcv0, send_chan: snd1 },
            (snd0, rcv1),
        )
    }
}

#[cfg(test)]
impl<T: Send> Sequencer<T> for TestSequencer<T> {
    #[inline]
    fn wait_for_go_ahead(&self) {
        let _ = self.rcv_chan.recv();
    }

    #[inline]
    fn send_result(&self, result: T) {
        let _ = self.send_chan.send(result);
    }
}

#[cfg(test)]
mod index_tests {
    use super::BufIndex;

    const M: usize = usize::MAX;


    macro_rules! test_case {
        (@ 16, $a:expr, $op:literal, $b:expr, $result:expr) => {
            concat!("(<16>(", stringify!($a), ") ", $op, " (", stringify!($b), ") == ", stringify!($result), ")")
        };
        (+, $a:expr, $b:expr, $result:expr) => {
            assert_eq!(BufIndex::<16>::new($a) + ($b as usize), BufIndex::<16>::new($result),
                test_case!(@ 16, $a, "+", $b, $result));
        };
        (-, $a:expr, $b:expr, $result:expr) => {
            assert_eq!(BufIndex::<16>::new($a) - ($b as usize), BufIndex::<16>::new($result),
                test_case!(@ 16, $a, "-", $b, $result));
        };
    }

    #[test]
    fn add_index_from_runup_no_wrap() {
        test_case!(+,  0,  0,  0);
        test_case!(+,  5,  9, 14);
        test_case!(+, 12,  7, 19);
        test_case!(+,  7, 12, 19);
        test_case!(+,  0, 16, 16);

        test_case!(+, 0, M-2, M-2);
        test_case!(+, 0, M-1, M-1);
        test_case!(+, 0,   M,   M);

        test_case!(+, 5, M-6, M-1);
        test_case!(+, 5, M-5,   M);

        test_case!(+, 10, M-11, M-1);
        test_case!(+, 10, M-10,   M);
    }

    #[test]
    fn add_index_from_runup_wrap() {
        test_case!(+, 1, M, 0x10);

        test_case!(+, 10, M-9, 0x10);
        test_case!(+, 10, M-8, 0x11);
        test_case!(+, 10, M-2, 0x17);
        test_case!(+, 10,   M, 0x19);

        test_case!(+, 15, M-14, 0x10);
        test_case!(+, 15,    M, 0x1E);
    }

    #[test]
    fn add_index_from_loop_no_wrap() {
        test_case!(+, 16,    0,   16);
        test_case!(+, 16,    4,   20);
        test_case!(+, 16, M-33, M-17);
        test_case!(+, 16, M-32, M-16);
        test_case!(+, 16, M-30, M-14);
        test_case!(+, 16, M-17,  M-1);
        test_case!(+, 16, M-16,    M);

        test_case!(+, 18,    0,  18);
        test_case!(+, 18,    8,  26);
        test_case!(+, 18, M-20, M-2);
        test_case!(+, 18, M-18,   M);

        test_case!(+, M-10,  0, M-10);
        test_case!(+, M-10,  7,  M-3);
        test_case!(+, M-10, 10,    M);

        test_case!(+, M-1, 0, M-1);
        test_case!(+, M-1, 1,   M);

        test_case!(+, M, 0, M);
    }

    #[test]
    fn add_index_from_loop_one_wrap() {
        test_case!(+, 16, M-15, 0x10);
        test_case!(+, 16, M-12, 0x13);
        test_case!(+, 16,  M-2, 0x1D);
        test_case!(+, 16,    M, 0x1F);

        test_case!(+, 20, M-19, 0x10);
        test_case!(+, 20, M-18, 0x11);
        test_case!(+, 20,    M, 0x23);

        test_case!(+, M-2,    3, 0x10);
        test_case!(+, M-2,    4, 0x11);
        test_case!(+, M-2,   16, 0x1D);
        test_case!(+, M-2, M-15,  M-2);
        test_case!(+, M-2, M-14,  M-1);
        test_case!(+, M-2, M-13,    M);

        test_case!(+, M,    1, 0x10);
        test_case!(+, M,   11, 0x1A);
        test_case!(+, M,   32, 0x2F);
        test_case!(+, M, M-17,  M-2);
        test_case!(+, M, M-15,    M);
    }

    #[test]
    fn add_index_from_loop_two_wraps() {
        test_case!(+, M-14, M, 0x10);

        test_case!(+, M-12, M-2, 0x10);
        test_case!(+, M-12, M-1, 0x11);
        test_case!(+, M-12,   M, 0x12);

        test_case!(+, M-5, M-9, 0x10);
        test_case!(+, M-5, M-6, 0x13);
        test_case!(+, M-5,   M, 0x19);

        test_case!(+, M, M-14, 0x10);
        test_case!(+, M, M-13, 0x11);
        test_case!(+, M,  M-2, 0x1C);
        test_case!(+, M,    M, 0x1E);
    }

    #[test]
    fn sub_index_from_runup_no_sat() {
        test_case!(-, 0, 0, 0);

        test_case!(-, 1, 0, 1);
        test_case!(-, 1, 1, 0);

        test_case!(-, 5, 0, 5);
        test_case!(-, 5, 1, 4);
        test_case!(-, 5, 4, 1);
        test_case!(-, 5, 5, 0);

        test_case!(-, 15,  0, 15);
        test_case!(-, 15,  4, 11);
        test_case!(-, 15, 13,  2);
        test_case!(-, 15, 15,  0);
    }

    #[test]
    fn sub_index_from_runup_sat() {
        test_case!(-, 0,   1, 0);
        test_case!(-, 0,   4, 0);
        test_case!(-, 0,  15, 0);
        test_case!(-, 0,  16, 0);
        test_case!(-, 0,  17, 0);
        test_case!(-, 0, M-4, 0);
        test_case!(-, 0, M-1, 0);
        test_case!(-, 0,   M, 0);

        test_case!(-, 1,   2, 0);
        test_case!(-, 1,   5, 0);
        test_case!(-, 1,  15, 0);
        test_case!(-, 1,  16, 0);
        test_case!(-, 1,  17, 0);
        test_case!(-, 1, M-4, 0);
        test_case!(-, 1,   M, 0);

        test_case!(-, 5,  6, 0);
        test_case!(-, 5, 10, 0);
        test_case!(-, 5, 11, 0);
        test_case!(-, 5, 32, 0);
        test_case!(-, 5,  M, 0);

        test_case!(-, 15,  16, 0);
        test_case!(-, 15,  17, 0);
        test_case!(-, 15,  32, 0);
        test_case!(-, 15, 100, 0);
        test_case!(-, 15, M-5, 0);
        test_case!(-, 15,   M, 0);
    }

    #[test]
    fn sub_index_from_loop_no_wrap() {
        test_case!(-, 16, 0, 16);

        test_case!(-, 17, 0, 17);
        test_case!(-, 17, 1, 16);

        test_case!(-, 32,  0, 32);
        test_case!(-, 32,  1, 31);
        test_case!(-, 32, 15, 17);
        test_case!(-, 32, 16, 16);

        test_case!(-, M-16,    0, M-16);
        test_case!(-, M-16,    1, M-17);
        test_case!(-, M-16,   16, M-32);
        test_case!(-, M-16,   17, M-33);
        test_case!(-, M-16, M-34,   18);
        test_case!(-, M-16, M-32,   16);

        test_case!(-, M,    0,    M);
        test_case!(-, M,    1,  M-1);
        test_case!(-, M,   14, M-14);
        test_case!(-, M,   15, M-15);
        test_case!(-, M,   16, M-16);
        test_case!(-, M, M-32,   32);
        test_case!(-, M, M-31,   31);
        test_case!(-, M, M-20,   20);
        test_case!(-, M, M-18,   18);
        test_case!(-, M, M-16,   16);
    }

    #[test]
    fn sub_index_from_loop_one_wrap() {
        test_case!(-, 16,    1,    M);
        test_case!(-, 16,    2,  M-1);
        test_case!(-, 16,   15, M-14);
        test_case!(-, 16,   16, M-15);
        test_case!(-, 16,   17, M-16);
        test_case!(-, 16, M-31,   32);
        test_case!(-, 16, M-16,   17);
        test_case!(-, 16, M-15,   16);

        test_case!(-, 17,    2,    M);
        test_case!(-, 17,    3,  M-1);
        test_case!(-, 17,   16, M-14);
        test_case!(-, 17,   17, M-15);
        test_case!(-, 17,   18, M-16);
        test_case!(-, 17, M-30,   32);
        test_case!(-, 17, M-29,   31);
        test_case!(-, 17, M-15,   17);
        test_case!(-, 17, M-14,   16);

        test_case!(-, 31, M-16, 32);
        test_case!(-, 31, M-15, 31);
        test_case!(-, 31,    M, 16);

        test_case!(-, 32,   17,   M);
        test_case!(-, 32,   19, M-2);
        test_case!(-, 32, M-16,  33);
        test_case!(-, 32, M-15,  32);
        test_case!(-, 32,    M,  17);

        test_case!(-, M-16, M-31,    M);
        test_case!(-, M-16, M-30,  M-1);
        test_case!(-, M-16, M-17, M-14);
        test_case!(-, M-16, M-16, M-15);

        test_case!(-, M, M-15,    M);
        test_case!(-, M, M-14,  M-1);
        test_case!(-, M,  M-1, M-14);
        test_case!(-, M,    M, M-15);
    }

    #[test]
    fn sub_index_from_loop_two_wraps() {
        test_case!(-, 16, M-14,    M);
        test_case!(-, 16, M-13,  M-1);
        test_case!(-, 16,  M-1, M-13);
        test_case!(-, 16,    M, M-14);

        test_case!(-, 17, M-13,    M);
        test_case!(-, 17, M-12,  M-1);
        test_case!(-, 17,  M-1, M-12);
        test_case!(-, 17,    M, M-13);

        test_case!(-, 29, M-1,   M);
        test_case!(-, 29,   M, M-1);

        test_case!(-, 30, M, M);
    }

    const fn trim_top_bit(x: usize) -> usize {
        x & !(1 << (usize::BITS - 1))
    }

    macro_rules! in_range_tableau {
        (@ @ $a:expr, $b:expr, $c:expr, $result:expr) => {
            concat!("<16>((", stringify!($a), ").in_range(", stringify!($b), ", ", stringify!($c), ") == ", stringify!($result), ")")
        };
        (@ 0 $a:expr , $b:expr, $c:expr, T) => {
            assert!(BufIndex::<16>::new($a).is_in_range(BufIndex::new($b), $c) == true,
                in_range_tableau!(@ @ $a, $b, $c, true));
        };
        (@ 0 $a:expr , $b:expr, $c:expr, F) => {
            assert!(BufIndex::<16>::new($a).is_in_range(BufIndex::new($b), $c) == false,
                in_range_tableau!(@ @ $a, $b, $c, true));
        };
        (@ 1 $a:expr ; ( $( ($b:expr, $c:expr) ),* ) ; ( $( $d:ident ),* )) => {
            $( in_range_tableau!(@ 0 $a, $b, $c, $d); )*
        };
        (@ 2 $bc:tt ; $( $a:expr ; $d:tt ; )*) => {
            $( in_range_tableau!(@ 1 $a ; $bc ; $d); )*
        };
        (@ 3 $( $bc:tt ),* ; $( $a:expr ; $( $d:ident )* ; )* ) => {
            in_range_tableau!(@ 2 ( $($bc),* ) ; $( $a ; ( $($d),* ) ; )* );
        };
        ($( ($b:expr, $c:expr) )* ; $($x:tt)+ ) => {
            in_range_tableau!(@ 3 $( ($b, $c) ),* ; $($x)+);
        }
    }

    #[rustfmt::skip]
    #[test]
    fn in_range() {
        // Some especially interesting edge cases:
        fn buf_index(x: usize) -> BufIndex<16> {
            BufIndex::new(x)
        }
        const MM: usize = trim_top_bit(M);

        assert!(!(buf_index(0).is_in_range(buf_index(0), 0)));
        assert!(!(buf_index(17).is_in_range(buf_index(17), 0)));
        assert!(buf_index(16).is_in_range(buf_index(1), MM));
        assert!(buf_index(17).is_in_range(buf_index(16), MM-2));
        assert!(buf_index(16).is_in_range(buf_index(16), MM-15));

        //in_range_tableau!(@ 0 0, 0, 1, T);
        //in_range_tableau!(@ 1 0 ; (0, 0) (0, 1) (1, 1) ; F T F);

        // Test in bulk:
        in_range_tableau!(
                   (0,0) (0,1) (0,2) (0,3) (1,0) (1,1) (1,2) (2,0) (2,1) (2,2) ;
             0   ;   F     T     T     T     F     F     F     F     F     F   ;
             1   ;   F     F     T     T     F     T     T     F     F     F   ;
             2   ;   F     F     F     T     F     F     T     F     T     T   ;
             3   ;   F     F     F     F     F     F     F     F     F     T   ;
             4   ;   F     F     F     F     F     F     F     F     F     F   ;
             5   ;   F     F     F     F     F     F     F     F     F     F   ;
             15  ;   F     F     F     F     F     F     F     F     F     F   ;
             16  ;   F     F     F     F     F     F     F     F     F     F   ;
             17  ;   F     F     F     F     F     F     F     F     F     F   ;
             31  ;   F     F     F     F     F     F     F     F     F     F   ;
             32  ;   F     F     F     F     F     F     F     F     F     F   ;
             33  ;   F     F     F     F     F     F     F     F     F     F   ;
            M-16 ;   F     F     F     F     F     F     F     F     F     F   ;
            M-15 ;   F     F     F     F     F     F     F     F     F     F   ;
            M-14 ;   F     F     F     F     F     F     F     F     F     F   ;
            M-1  ;   F     F     F     F     F     F     F     F     F     F   ;
             M   ;   F     F     F     F     F     F     F     F     F     F   ;
        );

        in_range_tableau!(
                   (0,15) (0,16) (0,17) (0,M-18) (0,M-16) (0,M-15) (0,M-14) (0,M-1) (0,M) ;
             0   ;   T      T      T      T        T        T        T        T       T   ;
             1   ;   T      T      T      T        T        T        T        T       T   ;
             2   ;   T      T      T      T        T        T        T        T       T   ;
             3   ;   T      T      T      T        T        T        T        T       T   ;
             5   ;   T      T      T      T        T        T        T        T       T   ;
             15  ;   F      T      T      T        T        T        T        T       T   ;
             16  ;   F      F      T      T        T        T        T        T       T   ;
             17  ;   F      F      F      T        T        T        T        T       T   ;
             31  ;   F      F      F      T        T        T        T        T       T   ;
             32  ;   F      F      F      T        T        T        T        T       T   ;
             33  ;   F      F      F      T        T        T        T        T       T   ;
            M-32 ;   F      F      F      T        T        T        T        T       T   ;
            M-31 ;   F      F      F      T        T        T        T        T       T   ;
            M-30 ;   F      F      F      T        T        T        T        T       T   ;
            M-17 ;   F      F      F      F        T        T        T        T       T   ;
            M-16 ;   F      F      F      F        F        T        T        T       T   ;
            M-15 ;   F      F      F      F        F        F        T        T       T   ;
            M-14 ;   F      F      F      F        F        F        F        T       T   ;
            M-2  ;   F      F      F      F        F        F        F        T       T   ;
            M-1  ;   F      F      F      F        F        F        F        F       T   ;
             M   ;   F      F      F      F        F        F        F        F       F   ;
        );

        in_range_tableau!(
                   (1,4) (1,5) (1,15) (1,16) (1,17) (1,20) (2,5) (2,12) (2,20) ;
             0   ;   F     F     F      F      F      F      F     F      F    ;
             1   ;   T     T     T      T      T      T      F     F      F    ;
             2   ;   T     T     T      T      T      T      T     T      T    ;
             3   ;   T     T     T      T      T      T      T     T      T    ;
             5   ;   F     T     T      T      T      T      T     T      T    ;
             15  ;   F     F     T      T      T      T      F     F      T    ;
             16  ;   F     F     F      T      T      T      F     F      T    ;
             17  ;   F     F     F      F      T      T      F     F      T    ;
             31  ;   F     F     F      F      F      F      F     F      F    ;
             32  ;   F     F     F      F      F      F      F     F      F    ;
             33  ;   F     F     F      F      F      F      F     F      F    ;
            M-32 ;   F     F     F      F      F      F      F     F      F    ;
            M-31 ;   F     F     F      F      F      F      F     F      F    ;
            M-30 ;   F     F     F      F      F      F      F     F      F    ;
            M-17 ;   F     F     F      F      F      F      F     F      F    ;
            M-16 ;   F     F     F      F      F      F      F     F      F    ;
            M-15 ;   F     F     F      F      F      F      F     F      F    ;
            M-14 ;   F     F     F      F      F      F      F     F      F    ;
            M-2  ;   F     F     F      F      F      F      F     F      F    ;
            M-1  ;   F     F     F      F      F      F      F     F      F    ;
             M   ;   F     F     F      F      F      F      F     F      F    ;
        );

        in_range_tableau!(
                   (1,M-32) (1,M-31) (1,M-16) (1,M-15) (1,M-14) (1,M-4) (1,M-1) (1,M) ;
             0   ;   F        F        F        F        F        F       F       F   ;
             1   ;   T        T        T        T        T        T       T       T   ;
             2   ;   T        T        T        T        T        T       T       T   ;
             3   ;   T        T        T        T        T        T       T       T   ;
             5   ;   T        T        T        T        T        T       T       T   ;
             15  ;   T        T        T        T        T        T       T       T   ;
             16  ;   T        T        T        T        T        T       T       T   ;
             17  ;   T        T        T        T        T        T       T       T   ;
             31  ;   T        T        T        T        T        T       T       T   ;
             32  ;   T        T        T        T        T        T       T       T   ;
             33  ;   T        T        T        T        T        T       T       T   ;
            M-32 ;   T        T        T        T        T        T       T       T   ;
            M-31 ;   F        T        T        T        T        T       T       T   ;
            M-30 ;   F        F        T        T        T        T       T       T   ;
            M-17 ;   F        F        T        T        T        T       T       T   ;
            M-16 ;   F        F        T        T        T        T       T       T   ;
            M-15 ;   F        F        F        T        T        T       T       T   ;
            M-14 ;   F        F        F        F        T        T       T       T   ;
            M-2  ;   F        F        F        F        F        F       T       T   ;
            M-1  ;   F        F        F        F        F        F       T       T   ;
             M   ;   F        F        F        F        F        F       F       T   ;
        );

        in_range_tableau!(
                   (2,5) (2,14) (2,15) (2,16)  (2,30) (2,M-32) (2,M-20) (2,M-10) (2,M-2) (2,M-1) (2,M) ;
             0   ;   F     F      F      F       F      F        F        F        F       F       F   ;
             1   ;   F     F      F      F       F      F        F        F        F       F       F   ;
             2   ;   T     T      T      T       T      T        T        T        T       T       T   ;
             3   ;   T     T      T      T       T      T        T        T        T       T       T   ;
             5   ;   T     T      T      T       T      T        T        T        T       T       T   ;
             15  ;   F     T      T      T       T      T        T        T        T       T       T   ;
             16  ;   F     F      T      T       T      T        T        T        T       T       T   ;
             17  ;   F     F      F      T       T      T        T        T        T       T       T   ;
             31  ;   F     F      F      F       T      T        T        T        T       T       T   ;
             32  ;   F     F      F      F       F      T        T        T        T       T       T   ;
             33  ;   F     F      F      F       F      T        T        T        T       T       T   ;
            M-32 ;   F     F      F      F       F      T        T        T        T       T       T   ;
            M-31 ;   F     F      F      F       F      T        T        T        T       T       T   ;
            M-30 ;   F     F      F      F       F      F        T        T        T       T       T   ;
            M-17 ;   F     F      F      F       F      F        F        T        T       T       T   ;
            M-16 ;   F     F      F      F       F      F        F        T        T       T       T   ;
            M-15 ;   F     F      F      F       F      F        F        T        T       T       T   ;
            M-14 ;   F     F      F      F       F      F        F        T        T       T       T   ;
            M-2  ;   F     F      F      F       F      F        F        F        T       T       T   ;
            M-1  ;   F     F      F      F       F      F        F        F        T       T       T   ;
             M   ;   F     F      F      F       F      F        F        F        F       T       T   ;
        );

        in_range_tableau!(
                   (15,0) (15,1) (15,5) (15,17) (15,M-30) (15,M-16) (15,M-15) (15,M-14) (15,M-1) (15,M) ;
             0   ;    F      F      F      F       F         F         F         F         F        F   ;
             1   ;    F      F      F      F       F         F         F         F         F        F   ;
             5   ;    F      F      F      F       F         F         F         F         F        F   ;
             15  ;    F      T      T      T       T         T         T         T         T        T   ;
             16  ;    F      F      T      T       T         T         T         T         T        T   ;
             17  ;    F      F      T      T       T         T         T         T         T        T   ;
             31  ;    F      F      F      T       T         T         T         T         T        T   ;
             32  ;    F      F      F      F       T         T         T         T         T        T   ;
             33  ;    F      F      F      F       T         T         T         T         T        T   ;
            M-17 ;    F      F      F      F       T         T         T         T         T        T   ;
            M-16 ;    F      F      F      F       T         T         T         T         T        T   ;
            M-15 ;    F      F      F      F       F         T         T         T         T        T   ;
            M-14 ;    F      F      F      F       F         T         T         T         T        T   ;
            M-2  ;    F      F      F      F       F         T         T         T         T        T   ;
            M-1  ;    F      F      F      F       F         F         T         T         T        T   ;
             M   ;    F      F      F      F       F         F         F         T         T        T   ;
        );

        in_range_tableau!(
                   (16,0) (16,1) (16,2) (16,16) (16,17) (16,M-17) (16,M-16) (16,M-15) (16,M-1) (16,M) ;
             0   ;    F      F      F      F       F       F         F         F         F        F   ;
             1   ;    F      F      F      F       F       F         F         F         F        F   ;
             15  ;    F      F      F      F       F       F         F         F         F        F   ;
             16  ;    F      T      T      T       T       T         T         T         T        T   ;
             17  ;    F      F      T      T       T       T         T         T         T        T   ;
             31  ;    F      F      F      T       T       T         T         T         T        T   ;
             32  ;    F      F      F      F       T       T         T         T         T        T   ;
             33  ;    F      F      F      F       F       T         T         T         T        T   ;
            M-16 ;    F      F      F      F       F       T         T         T         T        T   ;
            M-15 ;    F      F      F      F       F       T         T         T         T        T   ;
            M-14 ;    F      F      F      F       F       T         T         T         T        T   ;
            M-2  ;    F      F      F      F       F       T         T         T         T        T   ;
            M-1  ;    F      F      F      F       F       F         T         T         T        T   ;
             M   ;    F      F      F      F       F       F         F         T         T        T   ;
        );

        in_range_tableau!(
                   (18,0) (18,1) (18,2) (18,15) (18,16) (18,17) ;
             0   ;    F      F      F      F       F       F    ;
             1   ;    F      F      F      F       F       F    ;
             2   ;    F      F      F      F       F       F    ;
             3   ;    F      F      F      F       F       F    ;
             5   ;    F      F      F      F       F       F    ;
             15  ;    F      F      F      F       F       F    ;
             16  ;    F      F      F      F       F       F    ;
             17  ;    F      F      F      F       F       F    ;
             18  ;    F      T      T      T       T       T    ;
             19  ;    F      F      T      T       T       T    ;
             20  ;    F      F      F      T       T       T    ;
             32  ;    F      F      F      T       T       T    ;
             33  ;    F      F      F      F       T       T    ;
             34  ;    F      F      F      F       F       T    ;
             35  ;    F      F      F      F       F       F    ;
            M-2  ;    F      F      F      F       F       F    ;
            M-1  ;    F      F      F      F       F       F    ;
             M   ;    F      F      F      F       F       F    ;
        );

        in_range_tableau!(
                   (18,M-19) (18,M-18) (18,M-17) (18,M-16) (18,M-15) (18,M-14) (18,M-1) (18,M) ;
             0   ;    F         F         F         F         F         F         F        F   ;
             1   ;    F         F         F         F         F         F         F        F   ;
             2   ;    F         F         F         F         F         F         F        F   ;
             3   ;    F         F         F         F         F         F         F        F   ;
             5   ;    F         F         F         F         F         F         F        F   ;
             15  ;    F         F         F         F         F         F         F        F   ;
             16  ;    F         F         F         T         T         T         T        T   ;
             17  ;    F         F         F         F         T         T         T        T   ;
             18  ;    T         T         T         T         T         T         T        T   ;
             19  ;    T         T         T         T         T         T         T        T   ;
             31  ;    T         T         T         T         T         T         T        T   ;
             32  ;    T         T         T         T         T         T         T        T   ;
             33  ;    T         T         T         T         T         T         T        T   ;
             34  ;    T         T         T         T         T         T         T        T   ;
             35  ;    T         T         T         T         T         T         T        T   ;
            M-2  ;    T         T         T         T         T         T         T        T   ;
            M-1  ;    F         T         T         T         T         T         T        T   ;
             M   ;    F         F         T         T         T         T         T        T   ;
        );

        in_range_tableau!(
                   (31,1) (31,2) (31,3) (31,4) (32,0) (32,1) (32,2) (32,3) (33,0) (33,1) (33,2) ;
             0   ;    F      F      F      F      F      F      F      F      F      F      F   ;
             15  ;    F      F      F      F      F      F      F      F      F      F      F   ;
             16  ;    F      F      F      F      F      F      F      F      F      F      F   ;
             17  ;    F      F      F      F      F      F      F      F      F      F      F   ;
             31  ;    T      T      T      T      F      F      F      F      F      F      F   ;
             32  ;    F      T      T      T      F      T      T      T      F      F      F   ;
             33  ;    F      F      T      T      F      F      T      T      F      T      T   ;
            M-2  ;    F      F      F      F      F      F      F      F      F      F      F   ;
            M-1  ;    F      F      F      F      F      F      F      F      F      F      F   ;
             M   ;    F      F      F      F      F      F      F      F      F      F      F   ;
        );

        in_range_tableau!(
                   (31,M-32) (31,M-31) (31,M-30) (31,M-29) (31,M-28) ;
             0   ;    F         F         F         F         F      ;
             15  ;    F         F         F         F         F      ;
             16  ;    F         F         F         T         T      ;
             17  ;    F         F         F         F         T      ;
             18  ;    F         F         F         F         F      ;
             31  ;    T         T         T         T         T      ;
             32  ;    T         T         T         T         T      ;
             33  ;    T         T         T         T         T      ;
            M-2  ;    T         T         T         T         T      ;
            M-1  ;    F         T         T         T         T      ;
             M   ;    F         F         T         T         T      ;
        );

        in_range_tableau!(
                   (31,M-17) (31,M-16) (31,M-15) (31,M-14) (31,M-1) (31,M) ;
             0   ;    F         F         F         F         F        F   ;
             15  ;    F         F         F         F         F        F   ;
             16  ;    T         T         T         T         T        T   ;
             17  ;    T         T         T         T         T        T   ;
             28  ;    T         T         T         T         T        T   ;
             29  ;    F         T         T         T         T        T   ;
             30  ;    F         F         T         T         T        T   ;
             31  ;    T         T         T         T         T        T   ;
             32  ;    T         T         T         T         T        T   ;
             33  ;    T         T         T         T         T        T   ;
            M-2  ;    T         T         T         T         T        T   ;
            M-1  ;    T         T         T         T         T        T   ;
             M   ;    T         T         T         T         T        T   ;
        );

        in_range_tableau!(
                   (M-3,0) (M-3,1) (M-3,2) (M-3,3) (M-3,4) (M-3,5) (M-3,6) (M-3,19) (M-3,20) (M-3,21) ;
             0   ;     F       F       F       F       F       F       F       F        F        F    ;
             15  ;     F       F       F       F       F       F       F       F        F        F    ;
            M-3  ;     F       T       T       T       T       T       T       T        T        T    ;
            M-2  ;     F       F       T       T       T       T       T       T        T        T    ;
            M-1  ;     F       F       F       T       T       T       T       T        T        T    ;
             M   ;     F       F       F       F       T       T       T       T        T        T    ;
             16  ;     F       F       F       F       F       T       T       T        T        T    ;
             17  ;     F       F       F       F       F       F       T       T        T        T    ;
             18  ;     F       F       F       F       F       F       F       T        T        T    ;
             30  ;     F       F       F       F       F       F       F       T        T        T    ;
             31  ;     F       F       F       F       F       F       F       F        T        T    ;
             32  ;     F       F       F       F       F       F       F       F        F        T    ;
             33  ;     F       F       F       F       F       F       F       F        F        F    ;
            M-21 ;     F       F       F       F       F       F       F       F        F        F    ;
            M-20 ;     F       F       F       F       F       F       F       F        F        F    ;
            M-19 ;     F       F       F       F       F       F       F       F        F        F    ;
            M-18 ;     F       F       F       F       F       F       F       F        F        F    ;
            M-17 ;     F       F       F       F       F       F       F       F        F        F    ;
            M-16 ;     F       F       F       F       F       F       F       F        F        F    ;
            M-7  ;     F       F       F       F       F       F       F       F        F        F    ;
            M-6  ;     F       F       F       F       F       F       F       F        F        F    ;
            M-5  ;     F       F       F       F       F       F       F       F        F        F    ;
            M-4  ;     F       F       F       F       F       F       F       F        F        F    ;
        );

        in_range_tableau!(
                   (M-3,M-29) (M-3,M-28) (M-3,M-27) (M-3,M-26) (M-3,M-18) (M-3,M-17) (M-3,M-16) ;
             0   ;     F          F          F          F          F          F          F      ;
             15  ;     F          F          F          F          F          F          F      ;
            M-3  ;     T          T          T          T          T          T          T      ;
            M-2  ;     T          T          T          T          T          T          T      ;
            M-1  ;     T          T          T          T          T          T          T      ;
             M   ;     T          T          T          T          T          T          T      ;
             16  ;     T          T          T          T          T          T          T      ;
             17  ;     T          T          T          T          T          T          T      ;
             18  ;     T          T          T          T          T          T          T      ;
             31  ;     T          T          T          T          T          T          T      ;
             32  ;     T          T          T          T          T          T          T      ;
             33  ;     T          T          T          T          T          T          T      ;
            M-18 ;     T          T          T          T          T          T          T      ;
            M-17 ;     F          T          T          T          T          T          T      ;
            M-16 ;     F          F          T          T          T          T          T      ;
            M-15 ;     F          F          F          T          T          T          T      ;
            M-14 ;     F          F          F          F          T          T          T      ;
            M-7  ;     F          F          F          F          T          T          T      ;
            M-6  ;     F          F          F          F          F          T          T      ;
            M-5  ;     F          F          F          F          F          F          T      ;
            M-4  ;     F          F          F          F          F          F          F      ;
        );

        in_range_tableau!(
                   (M-3,M-15) (M-3,M-14) (M-3,M-2) (M-3,M-1) (M-3,M) ;
             0   ;     F          F          F         F         F   ;
             15  ;     F          F          F         F         F   ;
            M-3  ;     T          T          T         T         T   ;
            M-2  ;     T          T          T         T         T   ;
            M-1  ;     T          T          T         T         T   ;
             M   ;     T          T          T         T         T   ;
             16  ;     T          T          T         T         T   ;
             17  ;     T          T          T         T         T   ;
             18  ;     T          T          T         T         T   ;
             31  ;     T          T          T         T         T   ;
             32  ;     T          T          T         T         T   ;
             33  ;     T          T          T         T         T   ;
            M-21 ;     T          T          T         T         T   ;
            M-20 ;     T          T          T         T         T   ;
            M-19 ;     T          T          T         T         T   ;
            M-18 ;     T          T          T         T         T   ;
            M-17 ;     T          T          T         T         T   ;
            M-16 ;     T          T          T         T         T   ;
            M-7  ;     T          T          T         T         T   ;
            M-6  ;     T          T          T         T         T   ;
            M-5  ;     T          T          T         T         T   ;
            M-4  ;     T          T          T         T         T   ;
        );
    }
}
