use crate::span::Span;

// ---------------------------------------------------------------------------
// Token
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq)]
pub enum TokenKind {
    // Literals
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),

    // Identifiers / keywords
    Ident(String),
    Fn,
    Inline,
    Let,
    If,
    Else,
    While,
    Return,

    // Arithmetic operators
    Plus,
    Minus,
    Star,
    Slash,
    Percent,

    // Comparison operators
    EqEq,
    BangEq,
    Lt,
    LtEq,
    Gt,
    GtEq,

    // Logical operators
    AmpAmp,
    PipePipe,
    Bang,

    // Assignment / punctuation
    Eq,
    Arrow, // ->
    Colon,
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
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

// ---------------------------------------------------------------------------
// Lexer
// ---------------------------------------------------------------------------

pub struct Lexer<'a> {
    src: &'a str,
    pos: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Self {
        Self { src, pos: 0 }
    }

    fn peek(&self) -> Option<char> {
        self.src[self.pos..].chars().next()
    }

    fn peek2(&self) -> Option<char> {
        let mut it = self.src[self.pos..].chars();
        it.next();
        it.next()
    }

    fn advance(&mut self) -> Option<char> {
        let c = self.src[self.pos..].chars().next()?;
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

    pub fn tokenize(&mut self) -> Vec<Token> {
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

    fn lex_one(&mut self, first: char) -> TokenKind {
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
                TokenKind::Star
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
                if self.peek() == Some('=') {
                    self.advance();
                    TokenKind::LtEq
                } else {
                    TokenKind::Lt
                }
            }
            '>' => {
                self.advance();
                if self.peek() == Some('=') {
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
                    panic!("unexpected lone '&' at byte {}", self.pos)
                }
            }
            '|' => {
                self.advance();
                if self.peek() == Some('|') {
                    self.advance();
                    TokenKind::PipePipe
                } else {
                    panic!("unexpected lone '|' at byte {}", self.pos)
                }
            }
            ':' => {
                self.advance();
                TokenKind::Colon
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

    fn lex_string(&mut self) -> TokenKind {
        self.advance(); // opening `"`
        let mut s = String::new();
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
        TokenKind::Str(s)
    }

    fn lex_number(&mut self) -> TokenKind {
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

    fn lex_ident_or_keyword(&mut self) -> TokenKind {
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
            "true" => TokenKind::Bool(true),
            "false" => TokenKind::Bool(false),
            word => TokenKind::Ident(word.to_string()),
        }
    }
}
