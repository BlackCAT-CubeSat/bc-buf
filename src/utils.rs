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
        #[allow(non_snake_case)]
        let LOOP_LENGTH: usize = usize::MAX - SIZE + 1;

        if base < SIZE {
            let (end_idx, overflow) = base.overflowing_add(len);
            (base <= self) && (overflow || (self < end_idx))
        } else if len >= LOOP_LENGTH {
            SIZE <= self
        } else {
            let end_idx = base.add_index::<SIZE>(len);

            if end_idx >= base {
                (base <= self) && (self < end_idx)
            } else {
                (base <= self) || ((SIZE <= self) && (self < end_idx))
            }
        }
    }
}

#[cfg(test)]
mod index_tests {
    use super::IndexMath;

    const M: usize = usize::MAX;

    trait UsizeExt: IndexMath {
        fn add_index16(self, increment: usize) -> Self {
            self.add_index::<16>(increment)
        }

        fn sub_index16(self, decrement: usize) -> Self {
            self.sub_index::<16>(decrement)
        }
    }

    impl UsizeExt for usize {}

    #[test]
    fn add_index_from_runup_no_wrap() {
        assert_eq!(0usize.add_index16(0),  0usize);
        assert_eq!(5usize.add_index16(9),  14usize);
        assert_eq!(12usize.add_index16(7), 19usize);
        assert_eq!(7usize.add_index16(12), 19usize);
        assert_eq!(0usize.add_index16(16), 16usize);

        assert_eq!(0usize.add_index16(M-2), M-2);
        assert_eq!(0usize.add_index16(M-1), M-1);
        assert_eq!(0usize.add_index16(M), M);

        assert_eq!(5usize.add_index16(M-6), M-1);
        assert_eq!(5usize.add_index16(M-5), M);

        assert_eq!(10usize.add_index16(M-11), M-1);
        assert_eq!(10usize.add_index16(M-10), M);
    }

    #[test]
    fn add_index_from_runup_wrap() {
        assert_eq!(1usize.add_index16(M),    0x10usize);

        assert_eq!(10usize.add_index16(M-9), 0x10usize);
        assert_eq!(10usize.add_index16(M-8), 0x11usize);
        assert_eq!(10usize.add_index16(M-2), 0x17usize);
        assert_eq!(10usize.add_index16(M),   0x19usize);

        assert_eq!(15usize.add_index16(M-14), 0x10usize);
        assert_eq!(15usize.add_index16(M),    0x1Eusize);
    }

    #[test]
    fn add_index_from_loop_no_wrap() {
        assert_eq!(16usize.add_index16(0),    16usize);
        assert_eq!(16usize.add_index16(4),    20usize);
        assert_eq!(16usize.add_index16(M-33), M-17);
        assert_eq!(16usize.add_index16(M-32), M-16);
        assert_eq!(16usize.add_index16(M-30), M-14);
        assert_eq!(16usize.add_index16(M-17), M-1);
        assert_eq!(16usize.add_index16(M-16), M);

        assert_eq!(18usize.add_index16(0),    18usize);
        assert_eq!(18usize.add_index16(8),    26usize);
        assert_eq!(18usize.add_index16(M-20), M-2);
        assert_eq!(18usize.add_index16(M-18), M);

        assert_eq!((M-10).add_index16(0),  M-10);
        assert_eq!((M-10).add_index16(7),  M-3);
        assert_eq!((M-10).add_index16(10), M);

        assert_eq!((M-1).add_index16(0), M-1);
        assert_eq!((M-1).add_index16(1), M);

        assert_eq!(M.add_index16(0), M);
    }

    #[test]
    fn add_index_from_loop_one_wrap() {
        assert_eq!(16usize.add_index16(M-15), 0x10usize);
        assert_eq!(16usize.add_index16(M-12), 0x13usize);
        assert_eq!(16usize.add_index16(M-2),  0x1Dusize);
        assert_eq!(16usize.add_index16(M),    0x1Fusize);

        assert_eq!(20usize.add_index16(M-19), 0x10usize);
        assert_eq!(20usize.add_index16(M-18), 0x11usize);
        assert_eq!(20usize.add_index16(M),    0x23usize);

        assert_eq!((M-2).add_index16(3),    0x10usize);
        assert_eq!((M-2).add_index16(4),    0x11usize);
        assert_eq!((M-2).add_index16(16),   0x1Dusize);
        assert_eq!((M-2).add_index16(M-15), M-2);
        assert_eq!((M-2).add_index16(M-14), M-1);
        assert_eq!((M-2).add_index16(M-13), M);

        assert_eq!(M.add_index16(1),    0x10usize);
        assert_eq!(M.add_index16(11),   0x1Ausize);
        assert_eq!(M.add_index16(32),   0x2Fusize);
        assert_eq!(M.add_index16(M-17), M-2);
        assert_eq!(M.add_index16(M-15), M);
    }

    #[test]
    fn add_index_from_loop_two_wraps() {
        assert_eq!((M-14).add_index16(M), 0x10usize);

        assert_eq!((M-12).add_index16(M-2), 0x10usize);
        assert_eq!((M-12).add_index16(M-1), 0x11usize);
        assert_eq!((M-12).add_index16(M),   0x12usize);

        assert_eq!((M-5).add_index16(M-9), 0x10usize);
        assert_eq!((M-5).add_index16(M-6), 0x13usize);
        assert_eq!((M-5).add_index16(M),   0x19usize);

        assert_eq!(M.add_index16(M-14), 0x10usize);
        assert_eq!(M.add_index16(M-13), 0x11usize);
        assert_eq!(M.add_index16(M-2),  0x1Cusize);
        assert_eq!(M.add_index16(M),    0x1Eusize);
    }

    #[test]
    fn sub_index_from_runup_no_sat() {
        assert_eq!(0usize.sub_index16(0), 0usize);

        assert_eq!(1usize.sub_index16(0), 1usize);
        assert_eq!(1usize.sub_index16(1), 0usize);

        assert_eq!(5usize.sub_index16(0), 5usize);
        assert_eq!(5usize.sub_index16(1), 4usize);
        assert_eq!(5usize.sub_index16(4), 1usize);
        assert_eq!(5usize.sub_index16(5), 0usize);

        assert_eq!(15usize.sub_index16(0),  15usize);
        assert_eq!(15usize.sub_index16(4),  11usize);
        assert_eq!(15usize.sub_index16(13), 2usize);
        assert_eq!(15usize.sub_index16(15), 0usize);
    }

    #[test]
    fn sub_index_from_runup_sat() {
        assert_eq!(0usize.sub_index16(1),  0usize);
        assert_eq!(0usize.sub_index16(4),  0usize);
        assert_eq!(0usize.sub_index16(15), 0usize);
        assert_eq!(0usize.sub_index16(16), 0usize);
        assert_eq!(0usize.sub_index16(17), 0usize);
        assert_eq!(0usize.sub_index16(M-4), 0usize);
        assert_eq!(0usize.sub_index16(M-1), 0usize);
        assert_eq!(0usize.sub_index16(M), 0usize);

        assert_eq!(1usize.sub_index16(2),  0usize);
        assert_eq!(1usize.sub_index16(5),  0usize);
        assert_eq!(1usize.sub_index16(15), 0usize);
        assert_eq!(1usize.sub_index16(16), 0usize);
        assert_eq!(1usize.sub_index16(17), 0usize);
        assert_eq!(1usize.sub_index16(M-4), 0usize);
        assert_eq!(1usize.sub_index16(M),  0usize);

        assert_eq!(5usize.sub_index16(6), 0usize);
        assert_eq!(5usize.sub_index16(10), 0usize);
        assert_eq!(5usize.sub_index16(11), 0usize);
        assert_eq!(5usize.sub_index16(32), 0usize);
        assert_eq!(5usize.sub_index16(M),  0usize);

        assert_eq!(15usize.sub_index16(16),  0usize);
        assert_eq!(15usize.sub_index16(17),  0usize);
        assert_eq!(15usize.sub_index16(32),  0usize);
        assert_eq!(15usize.sub_index16(100), 0usize);
        assert_eq!(15usize.sub_index16(M-5), 0usize);
        assert_eq!(15usize.sub_index16(M),   0usize);
    }

    #[test]
    fn sub_index_from_loop_no_wrap() {
        assert_eq!(16usize.sub_index16(0), 16usize);

        assert_eq!(17usize.sub_index16(0), 17usize);
        assert_eq!(17usize.sub_index16(1), 16usize);

        assert_eq!(32usize.sub_index16(0),  32usize);
        assert_eq!(32usize.sub_index16(1),  31usize);
        assert_eq!(32usize.sub_index16(15), 17usize);
        assert_eq!(32usize.sub_index16(16), 16usize);

        assert_eq!((M-16).sub_index16(0),  M-16);
        assert_eq!((M-16).sub_index16(1),  M-17);
        assert_eq!((M-16).sub_index16(16), M-32);
        assert_eq!((M-16).sub_index16(17), M-33);
        assert_eq!((M-16).sub_index16(M-34), 18usize);
        assert_eq!((M-16).sub_index16(M-32), 16usize);

        assert_eq!(M.sub_index16(0),  M);
        assert_eq!(M.sub_index16(1),  M-1);
        assert_eq!(M.sub_index16(14), M-14);
        assert_eq!(M.sub_index16(15), M-15);
        assert_eq!(M.sub_index16(16), M-16);
        assert_eq!(M.sub_index16(M-32), 32usize);
        assert_eq!(M.sub_index16(M-31), 31usize);
        assert_eq!(M.sub_index16(M-20), 20usize);
        assert_eq!(M.sub_index16(M-18), 18usize);
        assert_eq!(M.sub_index16(M-16), 16usize);
    }

    #[test]
    fn sub_index_from_loop_one_wrap() {
        assert_eq!(16usize.sub_index16(1),  M);
        assert_eq!(16usize.sub_index16(2),  M-1);
        assert_eq!(16usize.sub_index16(15), M-14);
        assert_eq!(16usize.sub_index16(16), M-15);
        assert_eq!(16usize.sub_index16(17), M-16);
        assert_eq!(16usize.sub_index16(M-31), 32usize);
        assert_eq!(16usize.sub_index16(M-16), 17usize);
        assert_eq!(16usize.sub_index16(M-15), 16usize);

        assert_eq!(17usize.sub_index16(2), M);
        assert_eq!(17usize.sub_index16(3), M-1);
        assert_eq!(17usize.sub_index16(16), M-14);
        assert_eq!(17usize.sub_index16(17), M-15);
        assert_eq!(17usize.sub_index16(18), M-16);
        assert_eq!(17usize.sub_index16(M-30), 32usize);
        assert_eq!(17usize.sub_index16(M-29), 31usize);
        assert_eq!(17usize.sub_index16(M-15), 17usize);
        assert_eq!(17usize.sub_index16(M-14), 16usize);

        assert_eq!(31usize.sub_index16(M-16), 32usize);
        assert_eq!(31usize.sub_index16(M-15), 31usize);
        assert_eq!(31usize.sub_index16(M),    16usize);

        assert_eq!(32usize.sub_index16(17), M);
        assert_eq!(32usize.sub_index16(19), M-2);
        assert_eq!(32usize.sub_index16(M-16), 33usize);
        assert_eq!(32usize.sub_index16(M-15), 32usize);
        assert_eq!(32usize.sub_index16(M), 17usize);

        assert_eq!((M-16).sub_index16(M-31), M);
        assert_eq!((M-16).sub_index16(M-30), M-1);
        assert_eq!((M-16).sub_index16(M-17), M-14);
        assert_eq!((M-16).sub_index16(M-16), M-15);

        assert_eq!(M.sub_index16(M-15), M);
        assert_eq!(M.sub_index16(M-14), M-1);
        assert_eq!(M.sub_index16(M-1),  M-14);
        assert_eq!(M.sub_index16(M),    M-15);
    }

    #[test]
    fn sub_index_from_loop_two_wraps() {
        assert_eq!(16usize.sub_index16(M-14), M);
        assert_eq!(16usize.sub_index16(M-13), M-1);
        assert_eq!(16usize.sub_index16(M-1), M-13);
        assert_eq!(16usize.sub_index16(M), M-14);

        assert_eq!(17usize.sub_index16(M-13), M);
        assert_eq!(17usize.sub_index16(M-12), M-1);
        assert_eq!(17usize.sub_index16(M-1),  M-12);
        assert_eq!(17usize.sub_index16(M),    M-13);

        assert_eq!(29usize.sub_index16(M-1), M);
        assert_eq!(29usize.sub_index16(M),   M-1);

        assert_eq!(30usize.sub_index16(M), M);
    }

    macro_rules! in_range_tableau {
        (@ 0 $a:expr , $b:expr, $c:expr, T) => {
            assert!(($a as usize).in_range::<16>($b, $c) == true);
        };
        (@ 0 $a:expr , $b:expr, $c:expr, F) => {
            assert!(($a as usize).in_range::<16>($b, $c) == false);
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
        assert!(!(0usize.in_range::<16>(0, 0)));
        assert!(!(17usize.in_range::<16>(17, 0)));
        assert!(16usize.in_range::<16>(1, M));
        assert!(17usize.in_range::<16>(16, M-2));
        assert!(16usize.in_range::<16>(16, M-15));

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
