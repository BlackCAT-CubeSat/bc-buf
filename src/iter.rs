// Copyright (c) 2022 The Pennsylvania State University and the project contributors.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Iterators related to circular buffers.

use super::*;

/// The iterator returned by [`CBufWriter::current_items_iter`].
///
/// Yields the currently-stored items in the backing [`CBuf`].
pub(crate) struct WriterIterator<'a, 'b, T: CBufItem, const SIZE: usize>
where
    'a: 'b,
{
    pub(crate) _writer:     &'b mut CBufWriter<'a, T, SIZE>,
    pub(crate) writer_next: CBufIndex<SIZE>,
    pub(crate) buf:         &'a [T; SIZE],
    pub(crate) idx:         CBufIndex<SIZE>,
}

impl<'a, 'b, T: CBufItem, const SIZE: usize> Iterator for WriterIterator<'a, 'b, T, SIZE>
where
    'a: 'b,
{
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        if self.idx == self.writer_next {
            return None;
        }

        let old_idx = self.idx;
        self.idx += 1;
        Some(self.buf[old_idx.as_usize() & CBuf::<T, SIZE>::IDX_MASK])
    }
}

/// The iterator returned by [`CBufReader::available_items_iter`].
pub(crate) struct ReaderIterator<'a, 'b, T: CBufItem, const SIZE: usize>
where
    'a: 'b,
{
    pub(crate) reader:       &'b mut CBufReader<'a, T, SIZE>,
    pub(crate) fast_forward: bool,
    pub(crate) is_done:      bool,
}

impl<'a, 'b, T: CBufItem, const SIZE: usize> Iterator for ReaderIterator<'a, 'b, T, SIZE>
where
    'a: 'b,
{
    type Item = ReadResult<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.is_done {
            return None;
        }

        match self.reader.fetch_next_item(self.fast_forward) {
            ReadResult::None => {
                self.is_done = true;
                None
            }
            i => Some(i),
        }
    }
}

#[cfg(test)]
mod iterator_tests {
    use crate::utils::AtomicIndex;
    use crate::*;

    const M4: usize = usize::MAX - 4 + 1;

    fn run_test<T, const SIZE: usize>(init_buf: [T; SIZE], init_next: usize, expected_results: &[T])
    where
        T: CBufItem + core::fmt::Debug + PartialEq,
    {
        let mut cbuf: CBuf<T, SIZE> = CBuf {
            buf:  init_buf,
            next: AtomicIndex::new(init_next),
        };

        {
            let mut cbuf_writer = cbuf.as_writer();
            let mut cbuf_iter = cbuf_writer.current_items_iter();
            for i in expected_results {
                assert_eq!(cbuf_iter.next(), Some(*i));
            }
            assert_eq!(cbuf_iter.next(), None);
            assert_eq!(cbuf_iter.next(), None);
        }

        let (buf_ptr, next_ptr) = cbuf.as_ptrs();
        {
            let mut cbuf_reader: CBufReader<T, SIZE> =
                unsafe { CBufReader::new_from_ptr(buf_ptr, next_ptr) }.unwrap();
            let mut reader_iter = cbuf_reader.available_items_iter(false);
            assert_eq!(reader_iter.next(), None);
            assert_eq!(reader_iter.next(), None);
        }

        {
            let mut cbuf_reader: CBufReader<T, SIZE> =
                unsafe { CBufReader::new_from_ptr(buf_ptr, next_ptr) }.unwrap();
            cbuf_reader.next_local = cbuf_reader.next_local - (SIZE - 1);
            let mut reader_iter = cbuf_reader.available_items_iter(false);
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
        run_test(buf, 4, &[2, 3, 4]);
    }

    #[test]
    fn full_cbuf4() {
        let buf = [-0i16, -1, -2, -3];
        run_test(buf, 5, &[-2, -3, -0]);
        run_test(buf, 6, &[-3, -0, -1]);
        run_test(buf, 7, &[-0, -1, -2]);
        run_test(buf, 8, &[-1, -2, -3]);
        run_test(buf, 9, &[-2, -3, -0]);

        run_test(buf, M4 - 1, &[-0, -1, -2]);
        run_test(buf, M4, &[-1, -2, -3]);
        run_test(buf, M4 + 1, &[-2, -3, -0]);
        run_test(buf, M4 + 2, &[-3, -0, -1]);
        run_test(buf, M4 + 3, &[-0, -1, -2]);
    }
}
