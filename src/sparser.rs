use std::error::Error;
use std::fmt;
use std::iter::Peekable;

use crate::tokens;
use crate::operators;

#[derive(Debug)]
pub enum ParseError {
    TokenError(tokens::TokenError),
    UnexpectedEOF,
    UnexpectedRParen,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ParseError::TokenError(e) => write!(f, "{}", e),
            ParseError::UnexpectedEOF => write!(f, "unexpected end of input"),
            ParseError::UnexpectedRParen => write!(f, "unexpected right paren"),
        }
    }
}

impl Error for ParseError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            ParseError::TokenError(e) => Some(e),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub enum SExpr {
    Int(i64),
    Bool(bool),
    Char(char),
    Str(String),
    Word(String),
    OpExp(operators::Op),
    Ap(Vec<SExpr>),
}

pub fn parse<U>(tok: U) -> Result<SExpr, ParseError>
where
    U: Iterator<Item = Result<tokens::Token, tokens::TokenError>>,
{
    let mut tok = tok.peekable();
    parse_expr(&mut tok)
}

fn parse_expr<U>(tok: &mut Peekable<U>) -> Result<SExpr, ParseError>
where
    U: Iterator<Item = Result<tokens::Token, tokens::TokenError>>,
{
    if let Some(t) = tok.next() {
        let t = t.map_err(|e| ParseError::TokenError(e))?;
        match t {
            tokens::Token::Int(n) => return Ok(SExpr::Int(n)),
            tokens::Token::Bool(b) => return Ok(SExpr::Bool(b)),
            tokens::Token::Char(c) => return Ok(SExpr::Char(c)),
            tokens::Token::Str(s) => return Ok(SExpr::Str(s)),
            tokens::Token::Word(s) => return Ok(SExpr::Word(s)),
            tokens::Token::RParen => return Err(ParseError::UnexpectedRParen),
            tokens::Token::LParen => return parse_list(tok),
            tokens::Token::OpToken(o) => return Ok(SExpr::OpExp(o)),
        }
    }
    Err(ParseError::UnexpectedEOF)
}

fn parse_list<U>(tok: &mut Peekable<U>) -> Result<SExpr, ParseError>
where
    U: Iterator<Item = Result<tokens::Token, tokens::TokenError>>,
{
    let mut parts = Vec::new();
    while let Some(t) = tok.peek() {
        match t {
            Ok(tokens::Token::RParen) => break,
            _ => {
                let e = parse_expr(tok)?;
                parts.push(e);
            }
        }
    }
    tok.next();
    return Ok(SExpr::Ap(parts));
}
