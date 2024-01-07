//! MIT License
//!
//! Copyright (c) 2010 Serge Zaitsev
//!
//! Permission is hereby granted, free of charge, to any person obtaining a copy
//! of this software and associated documentation files (the "Software"), to deal
//! in the Software without restriction, including without limitation the rights
//! to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
//! copies of the Software, and to permit persons to whom the Software is
//! furnished to do so, subject to the following conditions:
//! The above copyright notice and this permission notice shall be included in
//! all copies or substantial portions of the Software.
//! THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//! IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//! FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//! AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//! LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
//! OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
//! SOFTWARE.
//!
//! jsmn (pronounced like 'jasmine') is Rust port of a minimalistic JSON parser.
//! It can be easily integrated into resource-limited or embedded projects.
//!
//! # Philosophy
//!
//! Most JSON parsers offer you a bunch of functions to load JSON data, parse it and
//! extract any value by its name. jsmn proves that checking the correctness of every
//! JSON packet or allocating temporary objects to store parsed JSON fields often is
//! an overkill.
//!
//! JSON format itself is extremely simple, so why should we complicate it?
//!
//! jsmn is designed to be robust (it should work fine even with erroneous data), fast
//! (it should parse data on the fly), portable. And of course, simplicity is a key feature
//! - simple code style, simple algorithm, simple integration into other projects.

use std::fmt::{Display, Formatter};

/// A JSON token to indicate where the data is stored in the JSON string.
///
/// So it's size could be reduced
/// - replacing `Option<usize>` with `Option<NonZeroSize>`, see: https://doc.rust-lang.org/std/num/struct.NonZeroUsize.html
/// - replacing usize with u32, `Option<usize>` with `i32`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Token {
    /// Token kind, e.g. object, array, string, etc.
    pub kind: Kind,
    /// The length of array or object.
    pub size: u32,

    /// Start position in JSON data string.
    pub start: i32,
    /// End position in JSON data string.
    pub end: i32,
}

impl Token {
    #[inline]
    pub fn new(kind: Kind, start: i32, end: i32) -> Self {
        Self::with_size(kind, start, end, 0)
    }

    #[inline]
    pub fn with_size(kind: Kind, start: i32, end: i32, size: u32) -> Self {
        Self {
            kind,
            start,
            end,
            size,
        }
    }
}

/// JSON token identifier
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Kind {
    Object,
    Array,
    Str,
    /// Other JSON primitive: number, boolean or null
    Primitive,
}

#[derive(Debug, PartialEq)]
pub enum Error {
    /// The string is not a full JSON packet, more bytes expected.
    Part,

    /// Invalid character inside JSON string.
    Invalid,

    /// Not enough tokens were provided. User should `extend` the
    /// tokens and call `JsonParser::parse()` again (don't create
    /// a new `JsonParser`).
    NoMemory,
}

impl std::error::Error for Error {}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Part => f.write_str("partial json"),
            Error::Invalid => f.write_str("invalid json"),
            Error::NoMemory => f.write_str("tokens is not big enough"),
        }
    }
}

/// JSON parser contains an array of token blocks available. Also stores the
/// string being parsed now and current position in that string.
#[derive(Default)]
pub struct JsonParser {
    /// Offset in the JSON string.
    pos: usize,
    /// next token to allocate.
    tok_next: usize,
    /// superior token node, e.g. parent object or array.
    tok_super: Option<usize>,
}

impl JsonParser {
    /// Run JSON parser. It parses a JSON data string into and array of tokens, each
    /// describing a single JSON object.
    ///
    /// Returns number of tokens parsed.
    ///
    /// N.B. `tokens` could be very large even than the JSON string itself, especially when the
    /// JSON string is large and complex. So `tokens` should be reused.
    pub fn parse(&mut self, data: &[u8], tokens: &mut [Token]) -> Result<usize, Error> {
        let mut count = self.tok_next;
        while self.pos < data.len() {
            let c = data[self.pos];
            match c {
                b'{' | b'[' => {
                    count += 1;
                    let i = self.alloc_token(tokens).ok_or(Error::NoMemory)?;
                    if let Some(i) = self.tok_super {
                        let t = &mut tokens[i];
                        // An object or array can't become a key
                        if let Kind::Object = t.kind {
                            return Err(Error::Invalid);
                        }
                        t.size += 1
                    }
                    let token = &mut tokens[i];
                    token.kind = if c == b'{' { Kind::Object } else { Kind::Array };
                    token.start = self.pos as i32;
                    self.tok_super = Some(self.tok_next - 1);
                }
                b'}' | b']' => {
                    let kind = if c == b'}' { Kind::Object } else { Kind::Array };
                    let mut i = (self.tok_next - 1) as isize;
                    while i >= 0 {
                        let token = &mut tokens[i as usize];
                        if token.start != -1 && token.end == -1 {
                            if token.kind != kind {
                                return Err(Error::Invalid);
                            }
                            self.tok_super = None;
                            token.end = (self.pos + 1) as i32;
                            break;
                        } else {
                            i -= 1
                        }
                    }
                    // Error if unmatched closing bracket
                    if i == -1 {
                        return Err(Error::Invalid);
                    }
                    while i >= 0 {
                        let token = &mut tokens[i as usize];
                        if token.start != -1 && token.end == -1 {
                            self.tok_super = Some(i as usize);
                            break;
                        } else {
                            i -= 1
                        }
                    }
                }
                b'"' => {
                    self.parse_string(data, tokens)?;
                    count += 1;
                    if let Some(i) = self.tok_super {
                        tokens[i].size += 1
                    }
                }
                b'\t' | b'\r' | b'\n' | b' ' => {}
                b':' => self.tok_super = Some(self.tok_next - 1),
                b',' => {
                    if let Some(i) = self.tok_super {
                        match tokens[i].kind {
                            Kind::Array | Kind::Object => {}
                            _ => {
                                for i in (0..self.tok_next).rev() {
                                    let t = &tokens[i];
                                    if let Kind::Array | Kind::Object = t.kind {
                                        if t.start != -1 && t.end == -1 {
                                            self.tok_super = Some(i);
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                b'0'..=b'9' | b'-' | b't' | b'f' | b'n' => {
                    // Primitives are: numbers and booleans and
                    // they must not be keys of the object
                    if let Some(i) = self.tok_super {
                        let t = &mut tokens[i];
                        match t.kind {
                            Kind::Object => return Err(Error::Invalid),
                            Kind::Str if t.size != 0 => return Err(Error::Invalid),
                            _ => {}
                        }
                    }
                    self.parse_primitive(data, tokens)?;
                    count += 1;
                    if let Some(i) = self.tok_super {
                        tokens[i].size += 1
                    }
                }
                _ => {
                    // Unexpected char
                    return Err(Error::Invalid);
                }
            }
            self.pos += 1;
        }
        let mut i = self.tok_next as isize - 1;
        while i >= 0 {
            // Unmatched opened object or array
            if tokens[i as usize].start != -1 && tokens[i as usize].end == -1 {
                return Err(Error::Part);
            }
            i -= 1
        }
        Ok(count)
    }

    /// Fills next available token with JSON primitive.
    fn parse_primitive(&mut self, data: &[u8], tokens: &mut [Token]) -> Result<(), Error> {
        let start = self.pos;
        while self.pos < data.len() {
            match data[self.pos] {
                b':' | b'\t' | b'\r' | b'\n' | b' ' | b',' | b']' | b'}' => break,
                _ => {}
            }

            if data[self.pos] < 32 || data[self.pos] >= 127 {
                self.pos = start as _;
                return Err(Error::Invalid);
            }
            self.pos += 1;
        }

        match self.alloc_token(tokens) {
            Some(i) => {
                tokens[i] = Token::new(Kind::Primitive, start as i32, self.pos as i32);
            }
            None => {
                self.pos = start;
                return Err(Error::NoMemory);
            }
        }

        self.pos -= 1;
        Ok(())
    }

    /// Fills next token with JSON string.
    fn parse_string(&mut self, data: &[u8], tokens: &mut [Token]) -> Result<(), Error> {
        let start = self.pos;
        self.pos += 1;
        // Skip starting quote
        while self.pos < data.len() {
            let c = data[self.pos];
            // Quote: end of string
            if c == b'\"' {
                match self.alloc_token(tokens) {
                    Some(i) => {
                        tokens[i] = Token::new(Kind::Str, (start + 1) as i32, self.pos as i32)
                    }
                    None => {
                        self.pos = start;
                        return Err(Error::NoMemory);
                    }
                };
                return Ok(());
            }

            // Backslash: Quoted symbol expected
            if c == b'\\' && (self.pos + 1) < data.len() {
                self.pos += 1;
                match data[self.pos] {
                    b'"' | b'/' | b'\\' | b'b' | b'f' | b'r' | b'n' | b't' => {}
                    b'u' => {
                        // Allows escaped symbol \uXXXX
                        self.pos += 1;
                        let mut i = 0;
                        while i < 4 && self.pos < data.len() {
                            // If it isn't a hex character we have an error
                            let is_hex = data[self.pos].is_ascii_hexdigit();
                            if !is_hex {
                                self.pos = start;
                                return Err(Error::Invalid);
                            }
                            self.pos += 1;
                            i += 1
                        }
                        self.pos -= 1;
                    }
                    _ => {
                        /* Unexpected symbol */
                        self.pos = start;
                        return Err(Error::Invalid);
                    }
                }
            }
            self.pos += 1;
        }
        self.pos = start as _;
        Err(Error::Part)
    }

    /// Allocates a fresh unused token from the token pool.
    fn alloc_token(&mut self, tokens: &mut [Token]) -> Option<usize> {
        if self.tok_next >= tokens.len() {
            return None;
        }
        let idx = self.tok_next;
        self.tok_next += 1;
        let tok = &mut tokens[idx];
        tok.end = -1;
        tok.start = tok.end;
        tok.size = 0;
        Some(idx)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem::size_of;

    #[test]
    fn size() {
        assert_eq!(size_of::<Token>(), 16)
    }

    macro_rules! parse {
        ($buf: expr, $len: expr) => {{
            let mut v = [Token::new(Kind::Str, 0, 0); $len];
            let mut parser = JsonParser::default();
            parser.parse($buf, &mut v).map(|parsed| {
                assert_eq!($len, parsed as usize);
                v
            })
        }};
    }

    #[test]
    fn parse_int() {
        let s = b"1234";
        let tokens = parse!(s, 1).unwrap();
        assert_eq!(&[Token::new(Kind::Primitive, 0, 4)], &tokens);
    }

    #[test]
    fn parse_int_negative() {
        let s = b"-1234";
        let tokens = parse!(s, 1).unwrap();
        assert_eq!(&[Token::new(Kind::Primitive, 0, 5)], &tokens);
    }

    #[test]
    fn parse_int_invalid() {
        let s = b"abc1234";
        let err = parse!(s, 1).unwrap_err();
        assert_eq!(Error::Invalid, err);
    }

    #[test]
    fn parse_string() {
        let s = br#""abcd""#;
        let tokens = parse!(s, 1).unwrap();
        assert_eq!(&[Token::new(Kind::Str, 1, 5)], &tokens);
    }

    #[test]
    fn parse_object() {
        let s = br#"{"a": "b", "c": 100}"#;
        let tokens = parse!(s, 5).unwrap();
        assert_eq!(
            &[
                Token::with_size(Kind::Object, 0, 20, 2),
                Token::with_size(Kind::Str, 2, 3, 1),
                Token::with_size(Kind::Str, 7, 8, 0),
                Token::with_size(Kind::Str, 12, 13, 1),
                Token::with_size(Kind::Primitive, 16, 19, 0)
            ],
            &tokens
        );
    }

    #[test]
    fn parse_array() {
        let s = br#"["a", "b", "c", 100]"#;
        let tokens = parse!(s, 5).unwrap();
        assert_eq!(
            &[
                Token::with_size(Kind::Array, 0, 20, 4),
                Token::with_size(Kind::Str, 2, 3, 0),
                Token::with_size(Kind::Str, 7, 8, 0),
                Token::with_size(Kind::Str, 12, 13, 0),
                Token::with_size(Kind::Primitive, 16, 19, 0)
            ],
            &tokens
        );
    }

    #[test]
    fn parse_array_oom() {
        let s = br#"["a", "b", "c", 100]"#;
        let err = parse!(s, 4).unwrap_err();
        assert_eq!(Error::NoMemory, err);
    }

    #[test]
    fn parse_array_02() {
        let s = br#"["123", {"a": 1, "b": "c"}, 123]"#;
        let tokens = parse!(s, 8).unwrap();
        assert_eq!(
            &[
                Token::with_size(Kind::Array, 0, 32, 3),
                Token::with_size(Kind::Str, 2, 5, 0),
                Token::with_size(Kind::Object, 8, 26, 2),
                Token::with_size(Kind::Str, 10, 11, 1),
                Token::with_size(Kind::Primitive, 14, 15, 0),
                Token::with_size(Kind::Str, 18, 19, 1),
                Token::with_size(Kind::Str, 23, 24, 0),
                Token::with_size(Kind::Primitive, 28, 31, 0),
            ],
            &tokens
        );
    }

    #[test]
    fn twitter() {
        let data = include_str!("../testdata/twitter.json");
        let mut tokens = Vec::with_capacity(64);
        let mut parser = JsonParser::default();

        loop {
            match parser.parse(data.as_bytes(), &mut tokens) {
                Ok(_n) => break,
                Err(err) => match err {
                    Error::NoMemory => {
                        let length = tokens.capacity();
                        tokens.resize(length * 2, Token::new(Kind::Str, 0, 0));
                        continue;
                    }
                    _ => panic!("parse error"),
                },
            }
        }
    }

    fn assert_tokens_equal(v1: &[Token], v2: &[Token], size: usize) {
        for i in 0..size {
            assert_eq!(v1[i], v2[i], "token not equal at {i}");
        }
    }

    #[test]
    fn reuse_tokens() {
        let mut tokens = Vec::new();
        tokens.resize(16, Token::new(Kind::Str, 0, 0));

        let data = br#"["123", {"a": 1, "b": "c"}, 123]"#;
        let mut parser = JsonParser::default();
        let parsed = parser.parse(data, &mut tokens).expect("ok");
        assert_eq!(parsed, 8);
        assert_tokens_equal(
            &[
                Token::with_size(Kind::Array, 0, 32, 3),
                Token::with_size(Kind::Str, 2, 5, 0),
                Token::with_size(Kind::Object, 8, 26, 2),
                Token::with_size(Kind::Str, 10, 11, 1),
                Token::with_size(Kind::Primitive, 14, 15, 0),
                Token::with_size(Kind::Str, 18, 19, 1),
                Token::with_size(Kind::Str, 23, 24, 0),
                Token::with_size(Kind::Primitive, 28, 31, 0),
            ],
            &tokens,
            parsed,
        );

        let data = br#"{"a": "b", "c": 100}"#;
        let mut parser = JsonParser::default();
        let parsed = parser.parse(data, &mut tokens).expect("ok");
        assert_eq!(parsed, 5);
        assert_tokens_equal(
            &[
                Token::with_size(Kind::Object, 0, 20, 2),
                Token::with_size(Kind::Str, 2, 3, 1),
                Token::with_size(Kind::Str, 7, 8, 0),
                Token::with_size(Kind::Str, 12, 13, 1),
                Token::with_size(Kind::Primitive, 16, 19, 0),
            ],
            &tokens,
            parsed,
        );
    }
}
