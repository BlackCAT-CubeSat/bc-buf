// Copyright (c) 2022 The Pennsylvania State University and the project contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Iterators related to circular buffers.

use super::*;

pub(crate) struct CBufWriterIterator<'a, 'b, T: CBufItem, const SIZE: usize> where 'a: 'b {
    pub(crate) writer: &'b mut CBufWriter<'a, T, SIZE>,
    pub(crate) idx: usize,
}

impl<'a, 'b, T: CBufItem, const SIZE: usize> Iterator for CBufWriterIterator<'a, 'b, T, SIZE> where 'a: 'b {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx == self.writer.next.as_usize() { return None; }

        let old_idx = self.idx;
        self.idx = old_idx.wrapping_add(1);
        Some(self.writer.cbuf.buf[old_idx & CBuf::<T, SIZE>::IDX_MASK])
    }
}

pub(crate) struct CBufReaderIterator<'a, 'b, T: CBufItem, const SIZE: usize> where 'a: 'b {
    pub(crate) reader: &'b mut CBufReader<'a, T, SIZE>,
    pub(crate) fast_forward: bool,
    pub(crate) is_done: bool,
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
mod iterator_tests {
    use crate::*;
    use crate::utils::AtomicIndex;

    const M4: usize = usize::MAX - 4 + 1;

    fn run_test<T, const SIZE: usize>(init_buf: [T; SIZE], init_next: usize, expected_results: &[T])
    where T: CBufItem + core::fmt::Debug + PartialEq {
        let mut cbuf: CBuf<T, SIZE> = CBuf {
            buf: init_buf,
            next: AtomicIndex::new(init_next),
        };

        {
            let mut cbuf_writer = cbuf.as_writer();
            let mut cbuf_iter = cbuf_writer.current_items();
            for i in expected_results {
                assert_eq!(cbuf_iter.next(), Some(*i));
            }
            assert_eq!(cbuf_iter.next(), None);
            assert_eq!(cbuf_iter.next(), None);
        }

        {
            let mut cbuf_reader = unsafe { CBufReader::from_ptr(&cbuf) }.unwrap();
            let mut reader_iter = cbuf_reader.available_items(false);
            assert_eq!(reader_iter.next(), None);
            assert_eq!(reader_iter.next(), None);
        }

        {
            let mut cbuf_reader = unsafe { CBufReader::from_ptr(&cbuf) }.unwrap();
            cbuf_reader.next = cbuf_reader.next - SIZE;
            let mut reader_iter = cbuf_reader.available_items(false);
            for i in expected_results {
                assert_eq!(reader_iter.next(), Some(ReadResult::Success(*i)));
            }
            assert_eq!(reader_iter.next(), None);
            assert_eq!(reader_iter.next(), None);
        }
    }

    #[test]
    fn nonfull_cbuf4() {
        let buf = [1i16, 2, 3, 4];
        run_test(buf, 0, &[]);
        run_test(buf, 1, &[1]);
        run_test(buf, 2, &[1, 2]);
        run_test(buf, 3, &[1, 2, 3]);
        run_test(buf, 4, &[1, 2, 3, 4]);
    }

    #[test]
    fn full_cbuf4() {
        let buf = [-1i16, -2, -3, -4];
        run_test(buf, 5, &[-2, -3, -4, -1]);
        run_test(buf, 6, &[-3, -4, -1, -2]);
        run_test(buf, 7, &[-4, -1, -2, -3]);
        run_test(buf, 8, &[-1, -2, -3, -4]);
        run_test(buf, 9, &[-2, -3, -4, -1]);

        run_test(buf, M4-1, &[-4, -1, -2, -3]);
        run_test(buf, M4,   &[-1, -2, -3, -4]);
        run_test(buf, M4+1, &[-2, -3, -4, -1]);
        run_test(buf, M4+2, &[-3, -4, -1, -2]);
        run_test(buf, M4+3, &[-4, -1, -2, -3]);
    }
}
