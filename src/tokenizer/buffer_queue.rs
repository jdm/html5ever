/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::str::CharRange;
use collections::deque::Deque;
use collections::dlist::DList;

struct Buffer {
    /// Byte position within the buffer.
    pos: uint,
    /// The buffer.
    buf: ~str,
}

/// Either a single character or a run of "data" characters: those which
/// don't trigger input stream preprocessing, or special handling in any
/// of the Data / RawData / Plaintext tokenizer states.  We do not exclude
/// characters which trigger a parse error but are otherwise handled
/// normally.
#[deriving(Eq, TotalEq, Show)]
pub enum DataRunOrChar {
    DataRun(~str),
    OneChar(char),
}

#[cfg(terrifying_microoptimizations)]
fn data_span(s: &str) -> uint {
    arch::data_span(s)
}

#[cfg(not(terrifying_microoptimizations))]
fn data_span(s: &str) -> uint {
    data_span_generic(s.as_bytes())
}

/// Count the number of bytes of data characters at the beginning of 's'.
fn data_span_generic(s: &[u8]) -> uint {
    let mut n = 0;
    for &b in s.iter() {
        match b {
        //  \0     \r     &      -      <
            0x00 | 0x0D | 0x26 | 0x2D | 0x3C => break,
            _ => n += 1,
        }
    }
    n
}

/// A queue of owned string buffers, which supports incrementally
/// consuming characters.
pub struct BufferQueue {
    /// Buffers to process.
    priv buffers: DList<Buffer>,

    /// Number of available characters.
    priv available: uint,
}

impl BufferQueue {
    /// Create an empty BufferQueue.
    pub fn new() -> BufferQueue {
        BufferQueue {
            buffers: DList::new(),
            available: 0,
        }
    }

    /// Add a buffer to the beginning of the queue.
    pub fn push_front(&mut self, buf: ~str) {
        if buf.len() == 0 {
            return;
        }
        self.account_new(buf.as_slice());
        self.buffers.push_front(Buffer {
            pos: 0,
            buf: buf,
        });
    }

    /// Add a buffer to the end of the queue.
    /// 'pos' can be non-zero to remove that many characters
    /// from the beginning.
    pub fn push_back(&mut self, buf: ~str, pos: uint) {
        if pos >= buf.len() {
            return;
        }
        self.account_new(buf.as_slice());
        self.buffers.push_back(Buffer {
            pos: pos,
            buf: buf,
        });
    }

    /// Do we have at least n characters available?
    pub fn has(&mut self, n: uint) -> bool {
        self.available >= n
    }

    /// Get multiple characters, if that many are available.
    pub fn pop_front(&mut self, n: uint) -> Option<~str> {
        if !self.has(n) {
            return None;
        }
        // FIXME: this is probably pretty inefficient
        Some(self.by_ref().take(n).collect())
    }

    /// Look at the next available character, if any.
    pub fn peek(&mut self) -> Option<char> {
        match self.buffers.front() {
            Some(&Buffer { pos, ref buf }) => Some(buf.char_at(pos)),
            None => None,
        }
    }

    /// Pop either a single character or a run of "data" characters.
    /// See `DataRunOrChar` for what this means.
    pub fn pop_data(&mut self) -> Option<DataRunOrChar> {
        let (result, now_empty) = match self.buffers.front_mut() {
            Some(&Buffer { ref mut pos, ref buf }) => {
                let n = data_span(buf.slice_from(*pos));

                // If we only have one character then it's cheaper not to allocate.
                if n > 1 {
                    let new_pos = *pos + n;
                    let out = buf.slice(*pos, new_pos).to_owned();
                    *pos = new_pos;
                    self.available -= n;
                    (Some(DataRun(out)), new_pos >= buf.len())
                } else {
                    let CharRange { ch, next } = buf.char_range_at(*pos);
                    *pos = next;
                    self.available -= 1;
                    (Some(OneChar(ch)), next >= buf.len())
                }
            }
            _ => (None, false),
        };

        if now_empty {
            self.buffers.pop_front();
        }

        result
    }

    fn account_new(&mut self, buf: &str) {
        // FIXME: We could pass through length from the initial [u8] -> ~str
        // conversion, which already must re-encode or at least scan for UTF-8
        // validity.
        self.available += buf.char_len();
    }
}

impl Iterator<char> for BufferQueue {
    /// Get the next character, if one is available.
    ///
    /// Because more data can arrive at any time, this can return Some(c) after
    /// it returns None.  That is allowed by the Iterator protocol, but it's
    /// unusual!
    fn next(&mut self) -> Option<char> {
        let (result, now_empty) = match self.buffers.front_mut() {
            None => (None, false),
            Some(&Buffer { ref mut pos, ref buf }) => {
                let CharRange { ch, next } = buf.char_range_at(*pos);
                *pos = next;
                self.available -= 1;
                (Some(ch), next >= buf.len())
            }
        };

        if now_empty {
            self.buffers.pop_front();
        }

        result
    }
}


#[cfg(terrifying_microoptimizations, target_arch="x86_64")]
mod arch {
    static non_data_chars: [u8, ..16] = [
        0x0D, 0x26, 0x2D, 0x3C, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    ];

    /// Count the number of bytes of data characters at the beginning of 's',
    /// using SSE 4.2 string instructions.
    pub fn data_span(s: &str) -> uint {
        // We have a choice between two instructions here.  pcmpestri takes a
        // string length in registers, while pcmpistri stops at a NULL byte.
        // pcmpestri is about half as fast because it executes additional uops
        // to load the lengths.  So we use pcmpistri, but we have to take care
        // because Rust strings aren't NULL-terminated and can contain interior
        // NULL characters.

        // First, round down the string length to a multiple of 16.
        let head_len = s.len() & (!0xf);

        let mut neg_remainder: uint = -head_len;
        if head_len > 0 {
            let mut off: uint;
            unsafe {
                asm!("
                    movdqu ($3), %xmm0           # load the set of bytes

                 1: movdqu ($2,$0), %xmm1        # load 16 bytes of the string
                    pcmpistri $$0, %xmm1, %xmm0
                    jbe 2f                       # exit on ZF (NULL) or CF (match)
                    add $$0x10, $0
                    jnz 1b

                 2:"
                    : "=&r"(neg_remainder), "=&{ecx}"(off)
                    : "r"((s.as_ptr() as uint) + head_len),
                      "r"(non_data_chars.as_ptr()), "0"(neg_remainder)
                    : "xmm0", "xmm1");
            }

            // If we found a match, `neg_remainder` holds the negation (as
            // two's complement unsigned) of the number of bytes remaining,
            // including the entirety of the block with the match.  And `off`
            // contains the offset of the match within that block.
            //
            // Otherwise we found a NULL, so off == 16 no matter where the NULL
            // was.  Or we reached the end, so neg_remainder == 0.

            if (neg_remainder != 0) && (off < 16) {
                return head_len + neg_remainder + off;
            }
        }

        // If we found a NULL above, do a bytewise search on that block and we
        // will find its exact position.  If we processed the first head_len
        // bytes, do a bytewise search on the remaining 0 - 15 bytes.
        //
        // It's tempting to finish the search with pcmpestri, but this would
        // involve fetching a 16-byte block that extends past the end of the
        // string.  We don't use those bytes, but we might end up reading from
        // a page that isn't mapped, which would cause a segfault.
        //
        // Using pcmpestri would save order of 10 ns in the best case, without
        // handling the segfault issue.  And this code is only reached when
        // searching the final 0 - 15 bytes before a NULL or the end of a
        // parser input chunk.

        let pos = head_len + neg_remainder;
        pos + super::data_span_generic(s.as_bytes().slice_from(pos))
    }
}


#[test]
fn smoke_test() {
    let mut bq = BufferQueue::new();
    assert_eq!(bq.has(1), false);
    assert_eq!(bq.peek(), None);
    assert_eq!(bq.next(), None);

    bq.push_back(~"abc", 0);
    assert_eq!(bq.has(1), true);
    assert_eq!(bq.has(3), true);
    assert_eq!(bq.has(4), false);

    assert_eq!(bq.peek(), Some('a'));
    assert_eq!(bq.next(), Some('a'));
    assert_eq!(bq.peek(), Some('b'));
    assert_eq!(bq.peek(), Some('b'));
    assert_eq!(bq.next(), Some('b'));
    assert_eq!(bq.peek(), Some('c'));
    assert_eq!(bq.next(), Some('c'));
    assert_eq!(bq.peek(), None);
    assert_eq!(bq.next(), None);
}

#[test]
fn can_pop_front() {
    let mut bq = BufferQueue::new();
    bq.push_back(~"abc", 0);

    assert_eq!(bq.pop_front(2), Some(~"ab"));
    assert_eq!(bq.peek(), Some('c'));
    assert_eq!(bq.pop_front(2), None);
    assert_eq!(bq.next(), Some('c'));
    assert_eq!(bq.next(), None);
}

#[test]
fn can_unconsume() {
    let mut bq = BufferQueue::new();
    bq.push_back(~"abc", 0);
    assert_eq!(bq.next(), Some('a'));

    bq.push_front(~"xy");
    assert_eq!(bq.next(), Some('x'));
    assert_eq!(bq.next(), Some('y'));
    assert_eq!(bq.next(), Some('b'));
    assert_eq!(bq.next(), Some('c'));
    assert_eq!(bq.next(), None);
}

#[test]
fn can_pop_data() {
    let mut bq = BufferQueue::new();
    bq.push_back(~"abc\0def", 0);
    assert_eq!(bq.pop_data(), Some(DataRun(~"abc")));
    assert_eq!(bq.pop_data(), Some(OneChar('\0')));
    assert_eq!(bq.pop_data(), Some(DataRun(~"def")));
    assert_eq!(bq.pop_data(), None);
}

#[test]
fn can_push_truncated() {
    let mut bq = BufferQueue::new();
    bq.push_back(~"abc", 1);
    assert_eq!(bq.next(), Some('b'));
    assert_eq!(bq.next(), Some('c'));
    assert_eq!(bq.next(), None);
}

#[test]
fn data_span_test() {
    fn pad(s: &mut ~str, n: uint) {
        for _ in range(0, n) {
            s.push_char('x');
        }
    }

    for &c in ['&', '\0'].iter() {
        for x in range(0, 48u) {
            for y in range(0, 48u) {
                let mut s = ~"";
                pad(&mut s, x);
                s.push_char(c);
                pad(&mut s, y);

                assert_eq!(x, data_span(s.as_slice()));
            }
        }
    }

    // A multi-byte character spanning a boundary between 16-byte
    // blocks, where the second block also contains a NULL.
    //
    // Make sure that the SSE4 code falls through to the byte-at-
    // a-time search in this case; otherwise we split the string
    // in the middle of a multi-byte character.
    let s = "xxxxxxxxxxxxxx\ua66e\x00xxxxxxxxxxxxxx";
    assert!(s.slice_to(data_span(s)).len() <= 17);
}
