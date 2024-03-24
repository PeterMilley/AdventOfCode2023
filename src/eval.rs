use std::boxed::Box;
use std::collections::VecDeque;
use std::error::Error;
use std::fmt;
use std::fs::File;
use std::io::BufReader;
use std::rc::Rc;

use crate::builtins;
use crate::charutils;
use crate::operators;
use crate::parser;
use crate::sparser;
use crate::tokens;
use crate::value;
use crate::varenv;

#[derive(Debug)]
pub enum EvalError {
    ExpectedNum(value::Value),
    ExpectedBool(value::Value),
    ExpectedChar(value::Value),
    ExpectedStr(value::Value),
    ExpectedUnit(value::Value),
    ExpectedComparable(value::Value),
    ExpectedOrdered(value::Value),
    UndefinedVar(String),
    DivByZero,
    ExpectedArgc(usize, usize),
    MissingArgs,
    ExpectedFn(value::Value),
    FailedCharCast(i64),
    Builtin(builtins::BuiltinError),
    SParseError(sparser::ParseError),
    ParseError(parser::ParseError),
    Fail,
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            EvalError::ExpectedNum(e) => write!(f, "expected numeric value, got {:?}", e),
            EvalError::ExpectedBool(e) => write!(f, "expected boolean value, got {:?}", e),
            EvalError::ExpectedChar(e) => write!(f, "expected character value, got {:?}", e),
            EvalError::ExpectedStr(e) => write!(f, "expected string value, got {:?}", e),
            EvalError::ExpectedUnit(e) => write!(f, "expected unit value, got {:?}", e),
            EvalError::ExpectedComparable(e) => write!(f, "expected comparable value, got {:?}", e),
            EvalError::ExpectedOrdered(e) => write!(f, "expected orderable value, got {:?}", e),
            EvalError::UndefinedVar(s) => write!(f, "undefined variable: {}", s),
            EvalError::DivByZero => write!(f, "division by zero"),
            EvalError::ExpectedArgc(n, m) => write!(f, "expected {} args, got {}", n, m),
            EvalError::MissingArgs => write!(f, "expected arguments"),
            EvalError::ExpectedFn(e) => write!(f, "expected a function, got {:?}", e),
            EvalError::FailedCharCast(n) => write!(f, "can't cast {} to char", n),
            EvalError::Builtin(e) => e.fmt(f),
            EvalError::SParseError(e) => e.fmt(f),
            EvalError::ParseError(e) => e.fmt(f),
            EvalError::Fail => write!(f, "fail encountered"),
        }
    }
}

impl Error for EvalError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            EvalError::Builtin(e) => Some(e),
            EvalError::SParseError(e) => Some(e),
            EvalError::ParseError(e) => Some(e),
            _ => None,
        }
    }
}

pub fn get_int(e: value::Value) -> Result<i64, EvalError> {
    match e {
        value::Value::Int(n) => Ok(n),
        _ => Err(EvalError::ExpectedNum(e)),
    }
}

pub fn get_bool(e: value::Value) -> Result<bool, EvalError> {
    match e {
        value::Value::Bool(b) => Ok(b),
        _ => Err(EvalError::ExpectedBool(e)),
    }
}

pub fn get_char(e: value::Value) -> Result<char, EvalError> {
    match e {
        value::Value::Char(c) => Ok(c),
        _ => Err(EvalError::ExpectedChar(e)),
    }
}

pub fn get_str(e: value::Value) -> Result<String, EvalError> {
    match e {
        value::Value::Str(s) => Ok(s),
        value::Value::Char(c) => Ok(c.to_string()),
        _ => Err(EvalError::ExpectedStr(e)),
    }
}

pub enum ExprOrValue {
    Expr(parser::Expr),
    Value(value::Value),
}

// What to do with the result of an evaluated expression.
pub enum Callback {
    // Return the result.
    Return,

    // Restore an old environment before continuing.
    Restore(Rc<varenv::Env>, Box<Callback>),

    // Update the environment with the result then continue evaluation.
    Update(String, ExprOrValue, Box<Callback>),

    // Discard the immediate result and continue evaluation.
    DropResult(ExprOrValue, Box<Callback>),

    // Branch based on the result.
    Branch(ExprOrValue, ExprOrValue, Box<Callback>),

    // Print the result, then continue.
    Print(ExprOrValue, Box<Callback>),

    // Apply the result to a sequence of arguments.
    Apply(VecDeque<ExprOrValue>, Box<Callback>),

    // Evaluate the body of a function with the given value as an argument.
    // Like Update, but applies to a saved environment.
    Body(String, Rc<varenv::Env>, ExprOrValue, Box<Callback>),

    // Accumulate the result into a partial sum.
    PartialSum(i64, VecDeque<ExprOrValue>, Box<Callback>),

    // Accumulate the result into a partial product.
    PartialProduct(i64, VecDeque<ExprOrValue>, Box<Callback>),

    // Accumulate the result into a sequence of values.
    Sequence(Vec<value::Value>, VecDeque<ExprOrValue>, Box<Callback>),

    // Consume a sequence of values as arguments to an operator.
    Minus(Box<Callback>),
    Div(Box<Callback>),
    Mod(Box<Callback>),
    Eq(Box<Callback>),
    Gt(Box<Callback>),

    // Consume a sequence of values as arguments to a built-in function.
    Builtin(builtins::Builtin, Box<Callback>),

    // Consume a sequence of strings as filenames, evaluate the code in those
    // files, the continue evaluating the expression.
    Load(VecDeque<String>, ExprOrValue, Box<Callback>),

    // Special handling (i.e. extreme hackery) for folding over constant lists
    // such as native string data.
    // 'Fold' is a callback that expects the value to be a sequence of arguments
    // consisting of a fold function (i.e. a->b->b) and an accumulator (i.e. b),
    // and 'returns'
    // a callable object that acts like a foldr over a list of values.
    // 'HandleFold' is a helper object that performs the resulting fold.
    Fold(Rc<Vec<value::Value>>, usize, Box<Callback>),
    HandleFold(Rc<Vec<value::Value>>, usize, value::Value, Box<Callback>),
}

// A piece of evaluation work to do.
pub struct Work {
    expr: ExprOrValue,
    env: Rc<varenv::Env>,
    callback: Callback,
}

// The result of doing a piece of work.
pub enum Outcome {
    Done(value::Value, Rc<varenv::Env>),
    Continue(Work),
}

fn cont(expr: ExprOrValue, env: Rc<varenv::Env>, callback: Callback) -> Result<Outcome, EvalError> {
    Ok(Outcome::Continue(Work {
        expr: expr,
        env: env,
        callback: callback,
    }))
}

fn wait(cb: Callback, env: Rc<varenv::Env>, v: value::Value) -> Result<Outcome, EvalError> {
    Ok(Outcome::Continue(Work {
        expr: ExprOrValue::Value(v),
        env: env,
        callback: cb,
    }))
}

fn run_cb(cb: Callback, env: Rc<varenv::Env>, v: value::Value) -> Result<Outcome, EvalError> {
    match cb {
        Callback::Return => Ok(Outcome::Done(v, env)),

        Callback::Restore(old_env, next) => wait(*next, old_env, v),

        Callback::Update(var, body, next) => {
            let mut env = env;
            varenv::update(&mut env, var, v);
            cont(body, env, *next)
        }

        Callback::DropResult(body, next) => cont(body, env, *next),

        Callback::Branch(iftrue, iffalse, next) => {
            if let value::Value::Bool(b) = v {
                cont(if b { iftrue } else { iffalse }, env, *next)
            } else {
                Err(EvalError::ExpectedBool(v))
            }
        }

        Callback::Print(body, next) => {
            if let value::Value::Str(s) = v {
                println!("{}", s);
                cont(body, env, *next)
            } else {
                Err(EvalError::ExpectedStr(v))
            }
        }

        Callback::Apply(args, next) => {
            let mut args = args;
            let mut next = next;
            if args.is_empty() {
                return Err(EvalError::MissingArgs);
            }
            let arg1 = args.pop_front().unwrap();
            match v {
                value::Value::Builtin(b) => cont(
                    arg1,
                    env,
                    Callback::Sequence(Vec::new(), args, Box::new(Callback::Builtin(b, next))),
                ),
                value::Value::Op(operators::Op::Plus) => {
                    cont(arg1, env, Callback::PartialSum(0, args, next))
                }
                value::Value::Op(operators::Op::Times) => {
                    cont(arg1, env, Callback::PartialProduct(1, args, next))
                }
                value::Value::Op(operators::Op::Minus) => cont(
                    arg1,
                    env,
                    Callback::Sequence(Vec::new(), args, Box::new(Callback::Minus(next))),
                ),
                value::Value::Op(operators::Op::Div) => cont(
                    arg1,
                    env,
                    Callback::Sequence(Vec::new(), args, Box::new(Callback::Div(next))),
                ),
                value::Value::Op(operators::Op::Mod) => cont(
                    arg1,
                    env,
                    Callback::Sequence(Vec::new(), args, Box::new(Callback::Mod(next))),
                ),
                value::Value::Op(operators::Op::Eq) => cont(
                    arg1,
                    env,
                    Callback::Sequence(Vec::new(), args, Box::new(Callback::Eq(next))),
                ),
                value::Value::Op(operators::Op::Gt) => cont(
                    arg1,
                    env,
                    Callback::Sequence(Vec::new(), args, Box::new(Callback::Gt(next))),
                ),
                value::Value::Lambda(var, e, body) => {
                    if !args.is_empty() {
                        next = Box::new(Callback::Apply(args, next));
                    }
                    cont(
                        arg1,
                        env,
                        Callback::Body(var, e, ExprOrValue::Expr(*body), next),
                    )
                }
                value::Value::Macro(var, env2, body) => {
                    if !args.is_empty() {
                        next = Box::new(Callback::Apply(args, next));
                    }
                    let mut env2 = env2;
                    let cloned = env.clone();
                    match arg1 {
                        ExprOrValue::Expr(e) => {
                            varenv::update(
                                &mut env2,
                                var,
                                value::Value::Thunk(cloned, Box::new(e)),
                            );
                        }
                        ExprOrValue::Value(v) => {
                            varenv::update(&mut env2, var, v);
                        }
                    }
                    cont(ExprOrValue::Expr(*body), env2, Callback::Restore(env, next))
                }
                value::Value::ConstSeq(seq, n) => cont(
                    arg1,
                    env,
                    Callback::Sequence(Vec::new(), args, Box::new(Callback::Fold(seq, n, next))),
                ),
                _ => Err(EvalError::ExpectedFn(v)),
            }
        }

        Callback::Body(var, e, body, next) => {
            let mut e = e;
            varenv::update(&mut e, var, v);
            cont(body, e, Callback::Restore(env, next))
        }

        Callback::PartialSum(result, args, next) => {
            let mut result = result;
            let mut args = args;
            if let value::Value::Int(n) = v {
                result += n
            } else {
                return Err(EvalError::ExpectedNum(v));
            }
            if !args.is_empty() {
                let arg = args.pop_front().unwrap();
                cont(arg, env, Callback::PartialSum(result, args, next))
            } else {
                wait(*next, env, value::Value::Int(result))
            }
        }

        Callback::PartialProduct(result, args, next) => {
            let mut result = result;
            let mut args = args;
            if let value::Value::Int(n) = v {
                result *= n
            } else {
                return Err(EvalError::ExpectedNum(v));
            }
            if !args.is_empty() {
                let arg = args.pop_front().unwrap();
                cont(arg, env, Callback::PartialProduct(result, args, next))
            } else {
                wait(*next, env, value::Value::Int(result))
            }
        }

        Callback::Sequence(results, args, next) => {
            let mut results = results;
            let mut args = args;
            results.push(v);
            if !args.is_empty() {
                let arg = args.pop_front().unwrap();
                cont(arg, env, Callback::Sequence(results, args, next))
            } else {
                wait(*next, env, value::Value::Seq(results))
            }
        }

        Callback::Minus(next) => {
            if let value::Value::Seq(args) = v {
                let n = args.len();
                if n != 2 {
                    return Err(EvalError::ExpectedArgc(2, n));
                }
                let args = args
                    .into_iter()
                    .map(get_int)
                    .collect::<Result<Vec<i64>, EvalError>>()?;
                wait(*next, env, value::Value::Int(args[0] - args[1]))
            } else {
                Err(EvalError::ExpectedArgc(2, 0))
            }
        }

        Callback::Div(next) => {
            if let value::Value::Seq(args) = v {
                let n = args.len();
                if n != 2 {
                    return Err(EvalError::ExpectedArgc(2, n));
                }
                let args = args
                    .into_iter()
                    .map(get_int)
                    .collect::<Result<Vec<i64>, EvalError>>()?;
                if args[1] == 0 {
                    Err(EvalError::DivByZero)
                } else {
                    wait(*next, env, value::Value::Int(args[0] / args[1]))
                }
            } else {
                Err(EvalError::ExpectedArgc(2, 0))
            }
        }

        Callback::Mod(next) => {
            if let value::Value::Seq(args) = v {
                let n = args.len();
                if n != 2 {
                    return Err(EvalError::ExpectedArgc(2, n));
                }
                let args = args
                    .into_iter()
                    .map(get_int)
                    .collect::<Result<Vec<i64>, EvalError>>()?;
                if args[1] == 0 {
                    Err(EvalError::DivByZero)
                } else {
                    wait(*next, env, value::Value::Int(args[0] % args[1]))
                }
            } else {
                Err(EvalError::ExpectedArgc(2, 0))
            }
        }

        Callback::Eq(next) => {
            if let value::Value::Seq(mut args) = v {
                let n = args.len();
                if n != 2 {
                    return Err(EvalError::ExpectedArgc(2, n));
                }
                let arg2 = args.pop().unwrap();
                let arg1 = args.pop().unwrap();
                match arg1 {
                    value::Value::Int(v1) => {
                        let v2 = get_int(arg2)?;
                        wait(*next, env, value::Value::Bool(v1 == v2))
                    }
                    value::Value::Bool(v1) => {
                        let v2 = get_bool(arg2)?;
                        wait(*next, env, value::Value::Bool(v1 == v2))
                    }
                    value::Value::Char(v1) => {
                        let v2 = get_char(arg2)?;
                        wait(*next, env, value::Value::Bool(v1 == v2))
                    }
                    value::Value::Str(v1) => {
                        let v2 = get_str(arg2)?;
                        wait(*next, env, value::Value::Bool(v1 == v2))
                    }
                    value::Value::Unit => match arg2 {
                        value::Value::Unit => wait(*next, env, value::Value::Bool(true)),
                        _ => Err(EvalError::ExpectedUnit(arg2)),
                    },
                    _ => Err(EvalError::ExpectedComparable(arg1)),
                }
            } else {
                Err(EvalError::ExpectedArgc(2, 0))
            }
        }

        Callback::Gt(next) => {
            if let value::Value::Seq(mut args) = v {
                let n = args.len();
                if n != 2 {
                    return Err(EvalError::ExpectedArgc(2, n));
                }
                let arg2 = args.pop().unwrap();
                let arg1 = args.pop().unwrap();
                match arg1 {
                    value::Value::Int(v1) => {
                        let v2 = get_int(arg2)?;
                        wait(*next, env, value::Value::Bool(v1 > v2))
                    }
                    value::Value::Char(v1) => {
                        let v2 = get_char(arg2)?;
                        wait(*next, env, value::Value::Bool(v1 > v2))
                    }
                    value::Value::Str(v1) => {
                        let v2 = get_str(arg2)?;
                        wait(*next, env, value::Value::Bool(v1 > v2))
                    }
                    value::Value::Unit => match arg2 {
                        value::Value::Unit => wait(*next, env, value::Value::Bool(false)),
                        _ => Err(EvalError::ExpectedUnit(arg2)),
                    },
                    _ => Err(EvalError::ExpectedOrdered(arg1)),
                }
            } else {
                Err(EvalError::ExpectedArgc(2, 0))
            }
        }

        Callback::Builtin(b, next) => {
            if let value::Value::Seq(args) = v {
                b.argc_matches(args.len())
                    .map_err(|e| EvalError::Builtin(e))?;
                match b {
                    builtins::Builtin::Print => {
                        let pieces = args
                            .into_iter()
                            .map(get_str)
                            .collect::<Result<Vec<String>, EvalError>>()?;
                        for s in pieces {
                            print!("{}", s)
                        }
                        wait(*next, env, value::Value::Unit)
                    }
                    builtins::Builtin::IToA => {
                        let args = args
                            .into_iter()
                            .map(get_int)
                            .collect::<Result<Vec<i64>, EvalError>>()?;
                        wait(*next, env, value::Value::Str(format!("{}", args[0])))
                    }
                    builtins::Builtin::StrCat => {
                        let pieces = args
                            .into_iter()
                            .map(get_str)
                            .collect::<Result<Vec<String>, EvalError>>()?;
                        let result = pieces.into_iter().fold(String::new(), |acc, s| acc + &s);
                        wait(*next, env, value::Value::Str(result))
                    }
                    builtins::Builtin::Ord => {
                        let args = args
                            .into_iter()
                            .map(get_char)
                            .collect::<Result<Vec<char>, EvalError>>()?;
                        wait(*next, env, value::Value::Int(args[0] as i64))
                    }
                    builtins::Builtin::Chr => {
                        let args = args
                            .into_iter()
                            .map(get_int)
                            .collect::<Result<Vec<i64>, EvalError>>()?;
                        let x = u32::try_from(args[0]).ok().and_then(|n| char::from_u32(n));
                        if let Some(c) = x {
                            wait(*next, env, value::Value::Char(c))
                        } else {
                            Err(EvalError::FailedCharCast(args[0]))
                        }
                    }
                    builtins::Builtin::Chars => {
                        let mut args = args;
                        if args.len() == 3 {
                            let f = args.pop().unwrap();
                            let k = args.pop().unwrap();
                            let arg1 = get_str(args.pop().unwrap())?;
                            let chars: Rc<Vec<value::Value>> =
                                Rc::new(arg1.chars().map(|c| value::Value::Char(c)).collect());
                            let n = chars.len();
                            wait(Callback::HandleFold(chars, n, k, next), env, f)
                        } else {
                            let arg = get_str(args.pop().unwrap())?;
                            let chars: Rc<Vec<value::Value>> =
                                Rc::new(arg.chars().map(|c| value::Value::Char(c)).collect());
                            let n = chars.len();
                            wait(*next, env, value::Value::ConstSeq(chars, n))
                        }
                    }
                    builtins::Builtin::List => {
                        let n = args.len();
                        wait(*next, env, value::Value::ConstSeq(Rc::new(args), n))
                    }
                }
            } else {
                Err(EvalError::ExpectedArgc(2, 0))
            }
        }

        Callback::Load(rest, body, next) => {
            if let value::Value::Str(first) = v {
                let file = File::open(first).unwrap();
                let buffer = charutils::BufReadChars::new(BufReader::new(file));
                let t = tokens::Tokenizer::new(buffer);
                let expr = sparser::parse(t)
                    .or_else(|e| Err(EvalError::SParseError(e)))
                    .and_then(|sexp| parser::parse(sexp).map_err(|e| EvalError::ParseError(e)))?;
                if rest.is_empty() {
                    cont(
                        ExprOrValue::Expr(expr),
                        env,
                        Callback::DropResult(body, next),
                    )
                } else {
                    let mut rest = rest;
                    let first = rest.pop_front().unwrap();
                    cont(
                        ExprOrValue::Expr(expr),
                        env,
                        Callback::DropResult(
                            ExprOrValue::Value(value::Value::Str(first)),
                            Box::new(Callback::Load(rest, body, next)),
                        ),
                    )
                }
            } else {
                Err(EvalError::ExpectedStr(v))
            }
        }

        Callback::Fold(values, num_values, next) => {
            if let value::Value::Seq(mut args) = v {
                let n = args.len();
                if n != 2 {
                    return Err(EvalError::ExpectedArgc(2, n));
                }
                let f = args.pop().unwrap();
                let k = args.pop().unwrap();
                if n == 0 {
                    wait(*next, env, f)
                } else {
                    wait(Callback::HandleFold(values, num_values, k, next), env, f)
                }
            } else {
                Err(EvalError::ExpectedArgc(2, 0))
            }
        }

        Callback::HandleFold(values, n, k, next) => {
            if n == 0 {
                return wait(*next, env, v);
            }
            let n = n - 1;
            let val = &values[n];
            let kclone = k.clone();
            wait(
                Callback::Apply(
                    VecDeque::from(vec![ExprOrValue::Value(val.clone()), ExprOrValue::Value(v)]),
                    Box::new(Callback::HandleFold(values, n, k, next)),
                ),
                env,
                kclone,
            )
        }
    }
}

pub fn do_one_step(w: Work) -> Result<Outcome, EvalError> {
    let env = w.env;
    match w.expr {
        ExprOrValue::Value(v) => run_cb(w.callback, env, v),
        ExprOrValue::Expr(parser::Expr::Int(n)) => run_cb(w.callback, env, value::Value::Int(n)),
        ExprOrValue::Expr(parser::Expr::Bool(b)) => run_cb(w.callback, env, value::Value::Bool(b)),
        ExprOrValue::Expr(parser::Expr::Char(c)) => run_cb(w.callback, env, value::Value::Char(c)),
        ExprOrValue::Expr(parser::Expr::Str(s)) => run_cb(w.callback, env, value::Value::Str(s)),
        ExprOrValue::Expr(parser::Expr::OpExp(o)) => run_cb(w.callback, env, value::Value::Op(o)),
        ExprOrValue::Expr(parser::Expr::Unit) => run_cb(w.callback, env, value::Value::Unit),
        ExprOrValue::Expr(parser::Expr::Word(var)) => match env.get(&var) {
            Some(v) => {
                if let value::Value::Thunk(e, body) = v {
                    cont(
                        ExprOrValue::Expr(*body),
                        e,
                        Callback::Restore(env, Box::new(w.callback)),
                    )
                } else {
                    run_cb(w.callback, env, v)
                }
            }
            None => match builtins::Builtin::from_str(&var) {
                Some(b) => run_cb(w.callback, env, value::Value::Builtin(b)),
                _ => Err(EvalError::UndefinedVar(var.to_string())),
            },
        },
        ExprOrValue::Expr(parser::Expr::Ap(args)) => {
            let mut args: VecDeque<ExprOrValue> = args.into_iter().map(ExprOrValue::Expr).collect();
            let head = args.pop_front().unwrap();
            cont(head, env, Callback::Apply(args, Box::new(w.callback)))
        }
        ExprOrValue::Expr(parser::Expr::Let(var, e1, e2)) => cont(
            ExprOrValue::Expr(*e1),
            env,
            Callback::Update(var, ExprOrValue::Expr(*e2), Box::new(w.callback)),
        ),
        ExprOrValue::Expr(parser::Expr::Lambda(var, body)) => {
            let cloned = env.clone();
            run_cb(w.callback, env, value::Value::Lambda(var, cloned, body))
        }
        ExprOrValue::Expr(parser::Expr::Macro(var, body)) => {
            let cloned = env.clone();
            run_cb(w.callback, env, value::Value::Macro(var, cloned, body))
        }
        ExprOrValue::Expr(parser::Expr::If(guard, branch, default)) => cont(
            ExprOrValue::Expr(*guard),
            env,
            Callback::Branch(
                ExprOrValue::Expr(*branch),
                ExprOrValue::Expr(*default),
                Box::new(w.callback),
            ),
        ),
        ExprOrValue::Expr(parser::Expr::Trace(msg, body)) => cont(
            ExprOrValue::Expr(*msg),
            env,
            Callback::Print(ExprOrValue::Expr(*body), Box::new(w.callback)),
        ),
        ExprOrValue::Expr(parser::Expr::Load(files, body)) => {
            let mut files: VecDeque<String> = files.into();
            if files.is_empty() {
                return cont(ExprOrValue::Expr(*body), env, w.callback);
            }
            let first = files.pop_front().unwrap();
            cont(
                ExprOrValue::Value(value::Value::Str(first)),
                env,
                Callback::Load(files, ExprOrValue::Expr(*body), Box::new(w.callback)),
            )
        }
        ExprOrValue::Expr(parser::Expr::Fail) => Err(EvalError::Fail),
    }
}

pub fn eval_with_env(
    e: parser::Expr,
    env: &mut Rc<varenv::Env>,
) -> Result<(value::Value, Rc<varenv::Env>), EvalError> {
    let mut w = Work {
        expr: ExprOrValue::Expr(e),
        env: env.clone(),
        callback: Callback::Return,
    };
    loop {
        let result = do_one_step(w)?;
        match result {
            Outcome::Done(v, env) => {
                return Ok((v, env));
            }
            Outcome::Continue(next) => {
                w = next;
            }
        }
    }
}
