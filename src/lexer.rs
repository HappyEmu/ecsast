use std::borrow::Cow;

use crate::span::Span;

// ---------------------------------------------------------------------------
// Token
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq)]
pub enum TokenKind<'src> {
    // Literals
    Int(i64),
    Float(f64),
    Bool(bool),
    /// String literal value. Borrowed from source when no escapes are present,
    /// owned when escape sequences forced a fresh allocation.
    Str(Cow<'src, str>),

    // Identifiers / keywords
    Ident(&'src str),
    Fn,
    Inline,
    Let,
    If,
    Else,
    While,
    Return,
    Use,
    Pub,

    // Arithmetic operators
    Plus,
    Minus,
    Star,
    StarStar, // **  (power)
    Slash,
    Percent,

    // Comparison operators
    EqEq,
    BangEq,
    Lt,
    LtEq,
    Gt,
    GtEq,

    // Bitwise operators
    Amp,
    Pipe,
    Caret,
    Tilde,
    LtLt,
    GtGt,

    // Logical operators
    AmpAmp,
    PipePipe,
    Bang,

    // Assignment / punctuation
    Eq,
    Arrow, // ->
    Colon,
    ColonColon, // ::
    Comma,
    Semicolon,

    // Delimiters
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,

    // End of file
    Eof,
}

#[derive(Clone, Debug)]
pub struct Token<'src> {
    pub kind: TokenKind<'src>,
    pub span: Span,
}

// ---------------------------------------------------------------------------
// Lexer
// ---------------------------------------------------------------------------

pub struct Lexer<'a> {
    src: &'a str,
    chars: std::str::Chars<'a>,
    pos: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Self {
        Self {
            src,
            chars: src.chars(),
            pos: 0,
        }
    }

    fn peek(&self) -> Option<char> {
        self.chars.clone().next()
    }

    fn peek2(&self) -> Option<char> {
        let mut it = self.chars.clone();
        it.next();
        it.next()
    }

    fn advance(&mut self) -> Option<char> {
        let c = self.chars.next()?;
        self.pos += c.len_utf8();
        Some(c)
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            // Whitespace
            while matches!(self.peek(), Some(c) if c.is_whitespace()) {
                self.advance();
            }
            // Line comment `// ...`
            if self.peek() == Some('/') && self.peek2() == Some('/') {
                while !matches!(self.peek(), Some('\n') | None) {
                    self.advance();
                }
            } else {
                break;
            }
        }
    }

    pub fn tokenize(&mut self) -> Vec<Token<'a>> {
        let mut tokens = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            let start = self.pos as u32;
            match self.peek() {
                None => {
                    tokens.push(Token {
                        kind: TokenKind::Eof,
                        span: Span::new(start, start),
                    });
                    break;
                }
                Some(c) => {
                    let kind = self.lex_one(c);
                    tokens.push(Token {
                        kind,
                        span: Span::new(start, self.pos as u32),
                    });
                }
            }
        }
        tokens
    }

    fn lex_one(&mut self, first: char) -> TokenKind<'a> {
        match first {
            '+' => {
                self.advance();
                TokenKind::Plus
            }
            '-' => {
                self.advance();
                if self.peek() == Some('>') {
                    self.advance();
                    TokenKind::Arrow
                } else {
                    TokenKind::Minus
                }
            }
            '*' => {
                self.advance();
                if self.peek() == Some('*') {
                    self.advance();
                    TokenKind::StarStar
                } else {
                    TokenKind::Star
                }
            }
            '/' => {
                self.advance();
                TokenKind::Slash
            }
            '%' => {
                self.advance();
                TokenKind::Percent
            }
            '=' => {
                self.advance();
                if self.peek() == Some('=') {
                    self.advance();
                    TokenKind::EqEq
                } else {
                    TokenKind::Eq
                }
            }
            '!' => {
                self.advance();
                if self.peek() == Some('=') {
                    self.advance();
                    TokenKind::BangEq
                } else {
                    TokenKind::Bang
                }
            }
            '<' => {
                self.advance();
                if self.peek() == Some('<') {
                    self.advance();
                    TokenKind::LtLt
                } else if self.peek() == Some('=') {
                    self.advance();
                    TokenKind::LtEq
                } else {
                    TokenKind::Lt
                }
            }
            '>' => {
                self.advance();
                if self.peek() == Some('>') {
                    self.advance();
                    TokenKind::GtGt
                } else if self.peek() == Some('=') {
                    self.advance();
                    TokenKind::GtEq
                } else {
                    TokenKind::Gt
                }
            }
            '&' => {
                self.advance();
                if self.peek() == Some('&') {
                    self.advance();
                    TokenKind::AmpAmp
                } else {
                    TokenKind::Amp
                }
            }
            '|' => {
                self.advance();
                if self.peek() == Some('|') {
                    self.advance();
                    TokenKind::PipePipe
                } else {
                    TokenKind::Pipe
                }
            }
            '^' => {
                self.advance();
                TokenKind::Caret
            }
            '~' => {
                self.advance();
                TokenKind::Tilde
            }
            ':' => {
                self.advance();
                if self.peek() == Some(':') {
                    self.advance();
                    TokenKind::ColonColon
                } else {
                    TokenKind::Colon
                }
            }
            ',' => {
                self.advance();
                TokenKind::Comma
            }
            ';' => {
                self.advance();
                TokenKind::Semicolon
            }
            '(' => {
                self.advance();
                TokenKind::LParen
            }
            ')' => {
                self.advance();
                TokenKind::RParen
            }
            '{' => {
                self.advance();
                TokenKind::LBrace
            }
            '}' => {
                self.advance();
                TokenKind::RBrace
            }
            '[' => {
                self.advance();
                TokenKind::LBracket
            }
            ']' => {
                self.advance();
                TokenKind::RBracket
            }
            '"' => self.lex_string(),
            c if c.is_ascii_digit() => self.lex_number(),
            c if c.is_alphabetic() || c == '_' => self.lex_ident_or_keyword(),
            c => panic!("unexpected character {:?} at byte {}", c, self.pos),
        }
    }

    fn lex_string(&mut self) -> TokenKind<'a> {
        self.advance(); // opening `"`
        let body_start = self.pos;

        // Fast path: scan to closing `"` and borrow from source if we hit no
        // escapes. Falling into the slow path only happens when we see `\`.
        loop {
            match self.peek() {
                Some('"') => {
                    let end = self.pos;
                    self.advance(); // closing `"`
                    return TokenKind::Str(Cow::Borrowed(&self.src[body_start..end]));
                }
                Some('\\') => break,
                Some(_) => {
                    self.advance();
                }
                None => panic!("unterminated string literal"),
            }
        }

        // Slow path: we hit an escape — copy everything seen so far into an
        // owned String and keep going.
        let mut s = String::from(&self.src[body_start..self.pos]);
        loop {
            match self.advance() {
                Some('"') => break,
                Some('\\') => match self.advance() {
                    Some('n') => s.push('\n'),
                    Some('t') => s.push('\t'),
                    Some('"') => s.push('"'),
                    Some('\\') => s.push('\\'),
                    other => panic!("unknown escape \\{:?}", other),
                },
                Some(c) => s.push(c),
                None => panic!("unterminated string literal"),
            }
        }
        TokenKind::Str(Cow::Owned(s))
    }

    fn lex_number(&mut self) -> TokenKind<'a> {
        let start = self.pos;
        while matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
            self.advance();
        }
        // Check for a fractional part: `.` followed by at least one digit.
        if self.peek() == Some('.') && matches!(self.peek2(), Some(c) if c.is_ascii_digit()) {
            self.advance(); // `.`
            while matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
                self.advance();
            }
            TokenKind::Float(self.src[start..self.pos].parse().unwrap())
        } else {
            TokenKind::Int(self.src[start..self.pos].parse().unwrap())
        }
    }

    fn lex_ident_or_keyword(&mut self) -> TokenKind<'a> {
        let start = self.pos;
        while matches!(self.peek(), Some(c) if c.is_alphanumeric() || c == '_') {
            self.advance();
        }
        match &self.src[start..self.pos] {
            "fn" => TokenKind::Fn,
            "inline" => TokenKind::Inline,
            "let" => TokenKind::Let,
            "if" => TokenKind::If,
            "else" => TokenKind::Else,
            "while" => TokenKind::While,
            "return" => TokenKind::Return,
            "use" => TokenKind::Use,
            "pub" => TokenKind::Pub,
            "true" => TokenKind::Bool(true),
            "false" => TokenKind::Bool(false),
            word => TokenKind::Ident(word),
        }
    }
}
