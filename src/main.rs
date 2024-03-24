use std::env;
use std::error::Error;
use std::fmt;
use std::fs::File;
use std::io;
use std::rc::Rc;

mod builtins;
mod charutils;
mod eval;
mod keywords;
mod operators;
mod parser;
mod sparser;
mod tokens;
mod value;
mod varenv;

#[derive(Debug)]
enum MyError {
    IOError(usize, io::Error),
    SParseFailedError(usize, sparser::ParseError),
    ParseFailedError(usize, parser::ParseError),
    EvalFailedError(usize, eval::EvalError),
}

impl fmt::Display for MyError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MyError::IOError(n, e) => write!(f, "Error on line {}: {:?}", n, e),
            MyError::SParseFailedError(n, e) => {
                write!(f, "Parse error on line {}: {}", n, e)
            }
            MyError::ParseFailedError(n, e) => {
                write!(f, "Parse error on line {}: {}", n, e)
            }
            MyError::EvalFailedError(n, e) => {
                write!(f, "Evaluation error on line {}: {}", n, e)
            }
        }
    }
}

impl Error for MyError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            MyError::IOError(_, e) => Some(e),
            MyError::SParseFailedError(_, e) => Some(e),
            MyError::ParseFailedError(_, e) => Some(e),
            MyError::EvalFailedError(_, e) => Some(e),
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut run_result = Ok(value::Value::Unit);
    if args.len() <= 1 {
        let stdin = io::stdin();
        let handle = stdin.lock();
        run_result = run(handle, true);
        if let Err(e) = run_result {
            println!("{}", e);
            std::process::exit(1);
        }
    } else {
        for arg in &args[1..] {
            let file = File::open(arg).unwrap();
            run_result = run(io::BufReader::new(file), false);
            if let Err(e) = run_result {
                println!("{}", e);
                std::process::exit(1);
            }
        }
    }
    if let Ok(result) = run_result {
        println!("{}", result.to_string());
    }
}

fn run<T>(b: T, interactive: bool) -> Result<value::Value, MyError>
where
    T: io::BufRead,
{
    // Read stdin in as a collection of lines
    let mut env = Rc::new(varenv::Env::new());
    let mut eval_result = value::Value::Unit;
    if interactive {
        for (i, l) in b.lines().enumerate() {
            let s = l.map_err(|e| MyError::IOError(i + 1, e))?;
            let t = tokens::Tokenizer::new(s.chars());
            let result = sparser::parse(t)
                .or_else(|e| Err(MyError::SParseFailedError(i + 1, e)))
                .and_then(|sexp| {
                    parser::parse(sexp).map_err(|e| MyError::ParseFailedError(i + 1, e))
                })
                .and_then(|exp| {
                    eval::eval_with_env(exp, &mut env)
                        .map_err(|e| MyError::EvalFailedError(i + 1, e))
                });
            if let Ok((value, new_env)) = result {
                println!("{:?}", value);
                eval_result = value;
                env = new_env;
            } else if let Err(ref err) = result {
                println!("Error: {}", err);
            }
        }
    } else {
        let charbuf = charutils::BufReadChars::new(b);
        let t = tokens::Tokenizer::new(charbuf);
        let result = sparser::parse(t)
            .or_else(|e| Err(MyError::SParseFailedError(1, e)))
            .and_then(|sexp| parser::parse(sexp).map_err(|e| MyError::ParseFailedError(1, e)))
            .and_then(|exp| {
                eval::eval_with_env(exp, &mut env).map_err(|e| MyError::EvalFailedError(1, e))
            });
        match result {
            Err(ref err) => {
                println!("Error: {}", err);
            }
            Ok((val, _)) => {
                eval_result = val;
            }
        }
    }
    Ok(eval_result)
}
