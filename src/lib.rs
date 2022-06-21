#![no_std]
#![feature(generic_const_exprs)]

use core::sync::atomic::{fence, AtomicUsize, Ordering::SeqCst};
use core::ptr::write_volatile;

pub const fn unwrap(opt: Option<usize>) -> usize {
    match opt {
        Some(val) => val,
        None => {
            panic!("exponent is too large for indices to be represented as usize");
        }
    }
}

#[repr(C)]
pub struct CBuf<T, const EXP: u32>
where
    T: Sized + Copy + 'static,
    [(); unwrap(1usize.checked_shl(EXP))]: Sized,
{
    /// The array where items are actually stored.
    buf: [T; unwrap(1usize.checked_shl(EXP))],

    /// Index of the first element available (modulo SIZE) (unless first == last == 0).
    first: AtomicUsize,

    /// Index just after the last element available (modulo SIZE) (unless last == 0).
    last: AtomicUsize,
}

impl<T, const EXP: u32> CBuf<T, EXP>
where
    T: Sized + Copy + 'static,
    [(); unwrap(1usize.checked_shl(EXP))]: Sized,
{
    const SIZE: usize = unwrap(1usize.checked_shl(EXP));
    const IDX_MASK: usize = Self::SIZE - 1;
}

#[derive(Clone, Copy)]
struct BufIndex<const EXP: u32> where [(); unwrap(1usize.checked_shl(EXP))]: Sized {
    n: usize
}

impl<const EXP: u32> BufIndex<EXP> where [(); unwrap(1usize.checked_shl(EXP))]: Sized {
    pub fn new(n: usize) -> Self {
        BufIndex { n: n }
    }

    // TODO: figure out proper, harder-to-misuse API
    pub fn as_idx(self) -> usize {
        self.n & CBuf::<(), EXP>::IDX_MASK
    }

    // TODO: figure out proper, harder-to-misuse API
    pub fn as_usize(self) -> usize { self.n }

    pub fn is_in_first_round(self) -> bool {
        (self.n & !CBuf::<(), EXP>::IDX_MASK) == 0
    }
}

impl<const EXP: u32> core::ops::Add<usize> for BufIndex<EXP> where [(); unwrap(1usize.checked_shl(EXP))]: Sized {
    type Output = Self;

    fn add(self, rhs: usize) -> Self {
        let (next_n, wrapped) = self.n.overflowing_add(rhs);

        if !wrapped {
            BufIndex { n: next_n }
        } else {
            BufIndex { n: next_n.wrapping_add(CBuf::<(), EXP>::SIZE) }
        }
    }
}

impl<const EXP: u32> core::ops::AddAssign<usize> for BufIndex<EXP> where [(); unwrap(1usize.checked_shl(EXP))]: Sized {
    fn add_assign(&mut self, rhs: usize) {
        self.n = (*self + rhs).n;
    }
}

pub struct CBufWriter<T, const EXP: u32>
where
    T: Sized + Copy + 'static,
    [(); unwrap(1usize.checked_shl(EXP))]: Sized,
{
    cbuf: &'static mut CBuf<T, EXP>,
    first: usize,  // TODO: change these to BufIndex
    last: usize,
}

// TODO: remove once unused
const fn next_idx<const EXP: u32>(i: usize) -> usize where [(); unwrap(1usize.checked_shl(EXP))]: Sized {
    let (next_i, wrapped) = i.overflowing_add(1);

    if !wrapped { next_i } else { next_i.wrapping_add(CBuf::<(), EXP>::SIZE) }
}

impl<T, const EXP: u32> CBufWriter<T, EXP>
where
    T: Sized + Copy + 'static,
    [(); unwrap(1usize.checked_shl(EXP))]: Sized,
{
    pub unsafe fn from_ptr_init(cbuf: *mut CBuf<T, EXP>) -> Option<Self> {
        let cbuf: &'static mut CBuf<T, EXP> = cbuf.as_mut()?;

        cbuf.last.store(0, SeqCst);
        cbuf.first.store(0, SeqCst);

        Some(CBufWriter { cbuf: cbuf, first: 0, last: 0 })
    }

    pub fn add_item(&mut self, item: T) {
        #[allow(non_snake_case)]
        let IDX_MASK = CBuf::<T, EXP>::IDX_MASK;

        let cbuf = &mut self.cbuf;

        if (self.last & !IDX_MASK) != 0 {
            let next_first = next_idx::<EXP>(self.first);
            let next_last = next_idx::<EXP>(self.last);

            cbuf.first.store(next_first, SeqCst);
            fence(SeqCst);
            unsafe { write_volatile(&mut cbuf.buf[self.last & IDX_MASK], item) };
            fence(SeqCst);
            cbuf.last.store(next_last, SeqCst);

            self.first = next_first;
            self.last = next_last;
        } else {
            let next_last = next_idx::<EXP>(self.last);

            unsafe { write_volatile(&mut cbuf.buf[self.last & IDX_MASK], item) };
            fence(SeqCst);
            cbuf.last.store(next_last, SeqCst);

            self.last = next_last;
        }
    }
}

pub struct CBufReader<T, const EXP: u32>
where
    T: Sized + Copy + 'static,
    [(); unwrap(1usize.checked_shl(EXP))]: Sized,
{
    cbuf: &'static CBuf<T, EXP>,
    next_idx: usize, // TODO: change this to BufIndex
}

impl<T, const EXP: u32> CBufReader<T, EXP>
where
    T: Sized + Copy + 'static,
    [(); unwrap(1usize.checked_shl(EXP))]: Sized,
{
    pub unsafe fn from_ptr(cbuf: *const CBuf<T, EXP>) -> Option<Self> {
        let cbuf: &'static CBuf<T, EXP> = cbuf.as_ref()?;

        Some(CBufReader {
            cbuf: cbuf,
            next_idx: cbuf.first.load(SeqCst),
        })
    }

    pub fn read_one(&mut self) -> Option<T> {
        unimplemented!("");
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
