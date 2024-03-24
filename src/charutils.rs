use std::io;
use std::iter::Iterator;

pub struct BufReadChars<B> {
    buffer: B,
    line: Vec<char>,
    index: usize,
}

impl<B> BufReadChars<B> {
    pub fn new(buffer: B) -> BufReadChars<B> {
        BufReadChars{buffer: buffer, line: Vec::new(), index: 0}
    }
}

impl<B> Iterator for BufReadChars<B>
where
    B: io::BufRead,
{
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.line.len() {
            self.index = 0;
            let mut b = String::new();
            if let Ok(n) = self.buffer.read_line(&mut b) {
                if n > 0 {
                    self.line = b.chars().collect();
                } else {
                    return None;
                }
            } else {
                return None;
            }
        }
        self.index += 1;
        Some(self.line[self.index - 1])
    }
}
