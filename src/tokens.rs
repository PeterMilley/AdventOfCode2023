use std::error::Error;
use std::fmt;
use std::iter::Iterator;
use std::iter::Peekable;

use crate::operators;

#[derive(Debug)]
pub enum TokenError {
    UnexpectedChar(char),
    UnterminatedStr,
    UnknownEscape(char),
    EmptyChar,
    UnterminatedChar,
}

impl fmt::Display for TokenError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TokenError::UnexpectedChar(c) => write!(f, "unexpected char {}", c),
            TokenError::UnterminatedStr => write!(f, "unterminated string constant"),
            TokenError::UnknownEscape(c) => write!(f, "unknown escape sequence \\{}", c),
            TokenError::EmptyChar => write!(f, "empty character constant"),
            TokenError::UnterminatedChar => write!(f, "unterminated character constant"),
        }
    }
}

impl Error for TokenError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Token {
    Int(i64),
    Bool(bool),
    Char(char),
    LParen,
    RParen,
    Str(String),
    Word(String),
    OpToken(operators::Op),
}

pub struct Tokenizer<C: Iterator> {
    stream: Peekable<C>,
}

impl<C> Tokenizer<C>
where
    C: Iterator<Item = char>,
{
    pub fn new(s: C) -> Tokenizer<C> {
        Tokenizer {
            stream: s.peekable(),
        }
    }

    pub fn parse_word(&mut self) -> Token {
        let mut result = String::new();
        while let Some(c) = self.stream.peek().and_then(|c| {
            if c.is_alphanumeric() || *c == '_' {
                Some(*c)
            } else {
                None
            }
        }) {
            result.push(c);
            self.stream.next();
        }
        if result == "true" {
            Token::Bool(true)
        } else if result == "false" {
            Token::Bool(false)
        } else {
            Token::Word(result)
        }
    }

    pub fn parse_int(&mut self) -> Token {
        let mut result = 0;
        while let Some(n) = self.stream.peek().and_then(|&c| c.to_digit(10)) {
            result = 10 * result + (n as i64);
            self.stream.next();
        }
        Token::Int(result)
    }

    pub fn parse_string(&mut self) -> Result<Token, TokenError> {
        let mut result = String::new();
        let mut found_close = false;
        while let Some(c) = self.stream.peek() {
            match *c {
                '"' => {
                    found_close = true;
                    self.stream.next();
                    break;
                }
                '\\' => {
                    self.stream.next();
                    if let Some(c) = self.stream.peek() {
                        match *c {
                            '\\' => result.push('\\'),
                            'n' => result.push('\n'),
                            '"' => result.push('"'),
                            _ => return Err(TokenError::UnknownEscape(*c)),
                        }
                        self.stream.next();
                    }
                }
                _ => {
                    result.push(*c);
                    self.stream.next();
                }
            }
        }
        if !found_close {
            return Err(TokenError::UnterminatedStr);
        }
        Ok(Token::Str(result))
    }

    pub fn parse_char(&mut self) -> Result<Token, TokenError> {
        let next = self.stream.peek();
        let result: Result<char, TokenError> = if let Some(&c) = next {
            match c {
                '\\' => {
                    self.stream.next();
                    let next = self.stream.peek();
                    if let Some(&c) = next {
                        self.stream.next();
                        match c {
                            '\\' => Ok('\\'),
                            'n' => Ok('\n'),
                            '\'' => Ok('\''),
                            _ => Err(TokenError::UnknownEscape(c)),
                        }
                    } else {
                        Err(TokenError::UnterminatedChar)
                    }
                }
                '\'' => Err(TokenError::EmptyChar),
                _ => {
                    self.stream.next();
                    Ok(c)
                }
            }
        } else {
            Err(TokenError::UnterminatedChar)
        };
        let result = Token::Char(result?);
        let next = self.stream.peek();
        if let Some(&c) = next {
            match c {
                '\'' => {
                    self.stream.next();
                }
                _ => return Err(TokenError::UnterminatedChar),
            }
        } else {
            return Err(TokenError::UnterminatedChar);
        }
        Ok(result)
    }
}

impl<C> Iterator for Tokenizer<C>
where
    C: Iterator<Item = char>,
{
    type Item = Result<Token, TokenError>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(c) = self.stream.peek() {
            if c.is_whitespace() {
                self.stream.next();
                continue;
            }
            if *c == '[' {
                self.stream.next();
                while let Some(c) = self.stream.peek() {
                    let done = *c == ']';
                    self.stream.next();
                    if done {
                        break;
                    }
                }
                continue;
            }
            if c.is_alphabetic() || *c == '_' {
                return Some(Ok(self.parse_word()));
            }
            if c.is_digit(10) {
                return Some(Ok(self.parse_int()));
            }
            if *c == '(' {
                self.stream.next();
                return Some(Ok(Token::LParen));
            }
            if *c == ')' {
                self.stream.next();
                return Some(Ok(Token::RParen));
            }
            if *c == '"' {
                self.stream.next();
                return Some(self.parse_string());
            }
            if *c == '\'' {
                self.stream.next();
                return Some(self.parse_char());
            }
            if *c == '+' {
                self.stream.next();
                return Some(Ok(Token::OpToken(operators::Op::Plus)));
            }
            if *c == '*' {
                self.stream.next();
                return Some(Ok(Token::OpToken(operators::Op::Times)));
            }
            if *c == '-' {
                self.stream.next();
                return Some(Ok(Token::OpToken(operators::Op::Minus)));
            }
            if *c == '/' {
                self.stream.next();
                return Some(Ok(Token::OpToken(operators::Op::Div)));
            }
            if *c == '%' {
                self.stream.next();
                return Some(Ok(Token::OpToken(operators::Op::Mod)));
            }
            if *c == '\\' {
                self.stream.next();
                return Some(Ok(Token::OpToken(operators::Op::Lambda)));
            }
            if *c == '=' {
                self.stream.next();
                return Some(Ok(Token::OpToken(operators::Op::Eq)));
            }
            if *c == '>' {
                self.stream.next();
                return Some(Ok(Token::OpToken(operators::Op::Gt)));
            }
            return Some(Err(TokenError::UnexpectedChar(*c)));
        }
        None
    }
}
