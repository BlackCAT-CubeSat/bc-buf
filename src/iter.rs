//! Iterators related to circular buffers.

use super::*;

pub(crate) struct CBufWriterIterator<'a, 'b, T: CBufItem, const SIZE: usize> where 'a: 'b {
    pub(crate) writer: &'b mut CBufWriter<'a, T, SIZE>,
    pub(crate) idx: usize,
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

