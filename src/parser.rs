use std::boxed::Box;
use std::collections::VecDeque;
use std::error::Error;
use std::fmt;

use crate::keywords;
use crate::operators;
use crate::sparser;

#[derive(Debug)]
pub enum ParseError {
    LetArgCount(usize),
    LetArgParity(usize),
    LetNotVar(sparser::SExpr),
    LambdaArgCount(usize),
    LambdaNotVar(sparser::SExpr),
    IfArgCount(usize),
    IfArgParity(usize),
    TraceArgCount(usize),
    LoadArgCount(usize),
    LoadNotStr(sparser::SExpr),
    NotCallable(String),
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ParseError::LetArgCount(n) => {
                write!(f, "expected at least 3 args to 'let' construct, got {}", n)
            }
            ParseError::LetArgParity(n) => write!(
                f,
                "expected an odd number of args to 'let' construct, got {}",
                n
            ),
            ParseError::LetNotVar(e) => write!(
                f,
                "expected variable name as first arg to 'let' construct, got {:?}",
                e
            ),
            ParseError::LambdaArgCount(n) => write!(
                f,
                "expected at least 2 args to 'lambda' or 'macro' construct, got {}",
                n
            ),
            ParseError::LambdaNotVar(e) => write!(
                f,
                "expected variable name as first arg to 'lambda' or 'macro' construct, got {:?}",
                e
            ),
            ParseError::IfArgCount(n) => {
                write!(f, "expected at least 3 args to 'if' construct, got {}", n)
            }
            ParseError::IfArgParity(n) => write!(
                f,
                "expected an odd number of args to 'if' construct, got {}",
                n
            ),
            ParseError::TraceArgCount(n) => write!(
                f,
                "expected at least 2 args to 'trace' construct, got {}",
                n
            ),
            ParseError::LoadArgCount(n) => {
                write!(f, "expected at least 2 args to 'load' construct, got {}", n)
            }
            ParseError::LoadNotStr(e) => write!(
                f,
                "expected string arguments to 'load' construct, got {:?}",
                e
            ),
            ParseError::NotCallable(k) => write!(f, "keyword '{:?}' is not callable", k),
        }
    }
}

impl Error for ParseError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Expr {
    Int(i64),
    Bool(bool),
    Char(char),
    Str(String),
    Word(String),
    OpExp(operators::Op),
    Unit,
    Ap(Vec<Expr>),
    Let(String, Box<Expr>, Box<Expr>),
    Lambda(String, Box<Expr>),
    Macro(String, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Trace(Box<Expr>, Box<Expr>),
    Load(Vec<String>, Box<Expr>),
    Fail,
}

pub fn parse(sexpr: sparser::SExpr) -> Result<Expr, ParseError> {
    match sexpr {
        sparser::SExpr::Int(n) => Ok(Expr::Int(n)),
        sparser::SExpr::Bool(b) => Ok(Expr::Bool(b)),
        sparser::SExpr::Char(c) => Ok(Expr::Char(c)),
        sparser::SExpr::Str(s) => Ok(Expr::Str(s)),
        sparser::SExpr::Word(s) => match s.as_str() {
            "fail" => Ok(Expr::Fail),
            _ => Ok(Expr::Word(s)),
        },
        sparser::SExpr::OpExp(o) => Ok(Expr::OpExp(o)),
        sparser::SExpr::Ap(v) => {
            if v.is_empty() {
                return Ok(Expr::Unit);
            }
            let kw: Option<keywords::Keyword> = match &v[0] {
                sparser::SExpr::Word(head) => match head.as_str() {
                    "let" => Some(keywords::Keyword::Let),
                    "macro" => Some(keywords::Keyword::Macro),
                    "if" => Some(keywords::Keyword::If),
                    "trace" => Some(keywords::Keyword::Trace),
                    "load" => Some(keywords::Keyword::Load),
                    "fail" => Some(keywords::Keyword::Fail),
                    _ => None,
                },
                sparser::SExpr::OpExp(o) => match o {
                    operators::Op::Lambda => Some(keywords::Keyword::Lambda),
                    _ => None,
                },
                _ => None,
            };
            match kw {
                Some(keywords::Keyword::Let) => parse_let(v),
                Some(keywords::Keyword::Lambda) => parse_lambda(v),
                Some(keywords::Keyword::Macro) => parse_macro(v),
                Some(keywords::Keyword::If) => parse_if(v),
                Some(keywords::Keyword::Trace) => parse_trace(v),
                Some(keywords::Keyword::Load) => parse_load(v),
                Some(keywords::Keyword::Fail) => Err(ParseError::NotCallable("fail".to_string())),
                _ => {
                    let v = v
                        .into_iter()
                        .map(|e| parse(e))
                        .collect::<Result<Vec<Expr>, ParseError>>()?;
                    Ok(Expr::Ap(v))
                }
            }
        }
    }
}

pub fn parse_let(mut args: Vec<sparser::SExpr>) -> Result<Expr, ParseError> {
    let n = args.len();
    if n < 4 {
        return Err(ParseError::LetArgCount(n - 1));
    }
    if n % 2 != 0 {
        return Err(ParseError::LetArgParity(n - 1));
    }
    let mut body = parse(args.pop().unwrap())?;
    while args.len() > 1 {
        let v = parse(args.pop().unwrap())?;
        let k = args.pop().unwrap();
        if let sparser::SExpr::Word(key) = k {
            body = Expr::Let(key, Box::new(v), Box::new(body));
        } else {
            return Err(ParseError::LetNotVar(k));
        }
    }
    Ok(body)
}

pub fn parse_if(mut args: Vec<sparser::SExpr>) -> Result<Expr, ParseError> {
    let n = args.len();
    if n < 4 {
        return Err(ParseError::IfArgCount(n - 1));
    }
    if n % 2 != 0 {
        return Err(ParseError::IfArgParity(n - 1));
    }
    let mut default = parse(args.pop().unwrap())?;
    while args.len() > 1 {
        let branch = parse(args.pop().unwrap())?;
        let guard = parse(args.pop().unwrap())?;
        default = Expr::If(Box::new(guard), Box::new(branch), Box::new(default));
    }
    Ok(default)
}

pub fn parse_lambda(mut args: Vec<sparser::SExpr>) -> Result<Expr, ParseError> {
    let n = args.len();
    if n < 3 {
        return Err(ParseError::LambdaArgCount(n - 1));
    }
    let mut body = parse(args.pop().unwrap())?;
    while args.len() > 1 {
        let varname = args.pop().unwrap();
        if let sparser::SExpr::Word(var) = varname {
            body = Expr::Lambda(var, Box::new(body));
        } else {
            return Err(ParseError::LambdaNotVar(varname));
        }
    }
    Ok(body)
}

pub fn parse_macro(mut args: Vec<sparser::SExpr>) -> Result<Expr, ParseError> {
    let n = args.len();
    if n < 3 {
        return Err(ParseError::LambdaArgCount(n - 1));
    }
    let mut body = parse(args.pop().unwrap())?;
    while args.len() > 1 {
        let varname = args.pop().unwrap();
        if let sparser::SExpr::Word(var) = varname {
            body = Expr::Macro(var, Box::new(body));
        } else {
            return Err(ParseError::LambdaNotVar(varname));
        }
    }
    Ok(body)
}

pub fn parse_trace(args: Vec<sparser::SExpr>) -> Result<Expr, ParseError> {
    let n = args.len();
    if n < 3 {
        return Err(ParseError::TraceArgCount(n - 1));
    }
    let mut args: VecDeque<sparser::SExpr> = args.into_iter().collect();
    args.pop_front();
    let msg = parse(args.pop_front().unwrap())?;
    if args.len() == 1 {
        let body = parse(args.pop_front().unwrap())?;
        return Ok(Expr::Trace(Box::new(msg), Box::new(body)));
    }
    let args: Vec<sparser::SExpr> = args.into_iter().collect();
    let body = parse(sparser::SExpr::Ap(args))?;
    Ok(Expr::Trace(Box::new(msg), Box::new(body)))
}

pub fn parse_load(args: Vec<sparser::SExpr>) -> Result<Expr, ParseError> {
    let n = args.len();
    if n < 3 {
        return Err(ParseError::LoadArgCount(n - 1));
    }
    let mut args: VecDeque<sparser::SExpr> = args.into_iter().collect();
    args.pop_front();
    let mut fnames = Vec::new();
    while args.len() >= 2 {
        let fname = args.pop_front().unwrap();
        if let sparser::SExpr::Str(f) = fname {
            fnames.push(f);
        } else {
            return Err(ParseError::LoadNotStr(fname));
        }
    }
    let body = parse(args.pop_front().unwrap())?;
    Ok(Expr::Load(fnames, Box::new(body)))
}
