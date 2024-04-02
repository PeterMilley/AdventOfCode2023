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
    // Restore an old environment before continuing.
    Restore(Rc<varenv::Env>),

    // Update the environment with the result then continue evaluation.
    Update(String, ExprOrValue),

    // Discard the immediate result and continue evaluation.
    DropResult(ExprOrValue),

    // Branch based on the result.
    Branch(ExprOrValue, ExprOrValue),

    // Print the result, then continue.
    Print(ExprOrValue),

    // Apply the result to a sequence of arguments.
    Apply(VecDeque<ExprOrValue>),

    // Evaluate the body of a function with the given value as an argument.
    // Like Update, but applies to a saved environment.
    Body(String, Rc<varenv::Env>, ExprOrValue),

    // Accumulate the result into a partial sum.
    PartialSum(i64, VecDeque<ExprOrValue>),

    // Accumulate the result into a partial product.
    PartialProduct(i64, VecDeque<ExprOrValue>),

    // Accumulate the result into a sequence of values.
    Sequence(Vec<value::Value>, VecDeque<ExprOrValue>),

    // Consume a sequence of values as arguments to an operator.
    Minus,
    Div,
    Mod,
    Eq,
    Gt,

    // Consume a sequence of values as arguments to a built-in function.
    Builtin(builtins::Builtin),

    // Consume a sequence of strings as filenames, evaluate the code in those
    // files, the continue evaluating the expression.
    Load(VecDeque<String>, ExprOrValue),

    // Special handling (i.e. extreme hackery) for folding over constant lists
    // such as native string data.
    // 'Fold' is a callback that expects the value to be a sequence of arguments
    // consisting of a fold function (i.e. a->b->b) and an accumulator (i.e. b),
    // and 'returns'
    // a callable object that acts like a foldr over a list of values.
    // 'HandleFold' is a helper object that performs the resulting fold.
    Fold(Rc<Vec<value::Value>>, usize),
    HandleFold(Rc<Vec<value::Value>>, usize, value::Value),
}

// A piece of evaluation work to do.
pub struct Work {
    expr: ExprOrValue,
    env: Rc<varenv::Env>,
}

// The result of doing a piece of work.
pub enum Outcome {
    Done(value::Value, Rc<varenv::Env>),
    Continue(Work),
}

fn cont(expr: ExprOrValue, env: Rc<varenv::Env>) -> Result<Outcome, EvalError> {
    Ok(Outcome::Continue(Work {
        expr: expr,
        env: env,
    }))
}

fn wait(env: Rc<varenv::Env>, v: value::Value) -> Result<Outcome, EvalError> {
    Ok(Outcome::Continue(Work {
        expr: ExprOrValue::Value(v),
        env: env,
    }))
}

fn run_cb(
    stack: &mut Vec<Callback>,
    env: Rc<varenv::Env>,
    v: value::Value,
) -> Result<Outcome, EvalError> {
    if stack.is_empty() {
        return Ok(Outcome::Done(v, env));
    }
    let cb = stack.pop().unwrap();
    match cb {
        Callback::Restore(old_env) => wait(old_env, v),

        Callback::Update(var, body) => {
            let mut env = env;
            varenv::update(&mut env, var, v);
            cont(body, env)
        }

        Callback::DropResult(body) => cont(body, env),

        Callback::Branch(iftrue, iffalse) => {
            if let value::Value::Bool(b) = v {
                cont(if b { iftrue } else { iffalse }, env)
            } else {
                Err(EvalError::ExpectedBool(v))
            }
        }

        Callback::Print(body) => {
            if let value::Value::Str(s) = v {
                println!("{}", s);
                cont(body, env)
            } else {
                Err(EvalError::ExpectedStr(v))
            }
        }

        Callback::Apply(args) => {
            let mut args = args;
            if args.is_empty() {
                return Err(EvalError::MissingArgs);
            }
            let arg1 = args.pop_front().unwrap();
            match v {
                value::Value::Builtin(b) => {
                    stack.push(Callback::Builtin(b));
                    stack.push(Callback::Sequence(Vec::new(), args));
                    cont(arg1, env)
                }
                value::Value::Op(operators::Op::Plus) => {
                    stack.push(Callback::PartialSum(0, args));
                    cont(arg1, env)
                }
                value::Value::Op(operators::Op::Times) => {
                    stack.push(Callback::PartialProduct(1, args));
                    cont(arg1, env)
                }
                value::Value::Op(operators::Op::Minus) => {
                    stack.push(Callback::Minus);
                    stack.push(Callback::Sequence(Vec::new(), args));
                    cont(arg1, env)
                }
                value::Value::Op(operators::Op::Div) => {
                    stack.push(Callback::Div);
                    stack.push(Callback::Sequence(Vec::new(), args));
                    cont(arg1, env)
                }
                value::Value::Op(operators::Op::Mod) => {
                    stack.push(Callback::Mod);
                    stack.push(Callback::Sequence(Vec::new(), args));
                    cont(arg1, env)
                }
                value::Value::Op(operators::Op::Eq) => {
                    stack.push(Callback::Eq);
                    stack.push(Callback::Sequence(Vec::new(), args));
                    cont(arg1, env)
                }
                value::Value::Op(operators::Op::Gt) => {
                    stack.push(Callback::Gt);
                    stack.push(Callback::Sequence(Vec::new(), args));
                    cont(arg1, env)
                }
                value::Value::Lambda(var, e, body) => {
                    if !args.is_empty() {
                        stack.push(Callback::Apply(args));
                    }
                    stack.push(Callback::Body(var, e, ExprOrValue::Expr(*body)));
                    cont(arg1, env)
                }
                value::Value::Macro(var, env2, body) => {
                    if !args.is_empty() {
                        stack.push(Callback::Apply(args));
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
                    stack.push(Callback::Restore(env));
                    cont(ExprOrValue::Expr(*body), env2)
                }
                value::Value::ConstSeq(seq, n) => {
                    stack.push(Callback::Fold(seq, n));
                    stack.push(Callback::Sequence(Vec::new(), args));
                    cont(arg1, env)
                }
                _ => Err(EvalError::ExpectedFn(v)),
            }
        }

        Callback::Body(var, e, body) => {
            let mut e = e;
            varenv::update(&mut e, var, v);
            stack.push(Callback::Restore(env));
            cont(body, e)
        }

        Callback::PartialSum(result, args) => {
            let mut result = result;
            let mut args = args;
            if let value::Value::Int(n) = v {
                result += n
            } else {
                return Err(EvalError::ExpectedNum(v));
            }
            if !args.is_empty() {
                let arg = args.pop_front().unwrap();
                stack.push(Callback::PartialSum(result, args));
                cont(arg, env)
            } else {
                wait(env, value::Value::Int(result))
            }
        }

        Callback::PartialProduct(result, args) => {
            let mut result = result;
            let mut args = args;
            if let value::Value::Int(n) = v {
                result *= n
            } else {
                return Err(EvalError::ExpectedNum(v));
            }
            if !args.is_empty() {
                let arg = args.pop_front().unwrap();
                stack.push(Callback::PartialProduct(result, args));
                cont(arg, env)
            } else {
                wait(env, value::Value::Int(result))
            }
        }

        Callback::Sequence(results, args) => {
            let mut results = results;
            let mut args = args;
            results.push(v);
            if !args.is_empty() {
                let arg = args.pop_front().unwrap();
                stack.push(Callback::Sequence(results, args));
                cont(arg, env)
            } else {
                wait(env, value::Value::Seq(results))
            }
        }

        Callback::Minus => {
            if let value::Value::Seq(args) = v {
                let n = args.len();
                if n != 2 {
                    return Err(EvalError::ExpectedArgc(2, n));
                }
                let args = args
                    .into_iter()
                    .map(get_int)
                    .collect::<Result<Vec<i64>, EvalError>>()?;
                wait(env, value::Value::Int(args[0] - args[1]))
            } else {
                Err(EvalError::ExpectedArgc(2, 0))
            }
        }

        Callback::Div => {
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
                    wait(env, value::Value::Int(args[0] / args[1]))
                }
            } else {
                Err(EvalError::ExpectedArgc(2, 0))
            }
        }

        Callback::Mod => {
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
                    wait(env, value::Value::Int(args[0] % args[1]))
                }
            } else {
                Err(EvalError::ExpectedArgc(2, 0))
            }
        }

        Callback::Eq => {
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
                        wait(env, value::Value::Bool(v1 == v2))
                    }
                    value::Value::Bool(v1) => {
                        let v2 = get_bool(arg2)?;
                        wait(env, value::Value::Bool(v1 == v2))
                    }
                    value::Value::Char(v1) => {
                        let v2 = get_char(arg2)?;
                        wait(env, value::Value::Bool(v1 == v2))
                    }
                    value::Value::Str(v1) => {
                        let v2 = get_str(arg2)?;
                        wait(env, value::Value::Bool(v1 == v2))
                    }
                    value::Value::Unit => match arg2 {
                        value::Value::Unit => wait(env, value::Value::Bool(true)),
                        _ => Err(EvalError::ExpectedUnit(arg2)),
                    },
                    _ => Err(EvalError::ExpectedComparable(arg1)),
                }
            } else {
                Err(EvalError::ExpectedArgc(2, 0))
            }
        }

        Callback::Gt => {
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
                        wait(env, value::Value::Bool(v1 > v2))
                    }
                    value::Value::Char(v1) => {
                        let v2 = get_char(arg2)?;
                        wait(env, value::Value::Bool(v1 > v2))
                    }
                    value::Value::Str(v1) => {
                        let v2 = get_str(arg2)?;
                        wait(env, value::Value::Bool(v1 > v2))
                    }
                    value::Value::Unit => match arg2 {
                        value::Value::Unit => wait(env, value::Value::Bool(false)),
                        _ => Err(EvalError::ExpectedUnit(arg2)),
                    },
                    _ => Err(EvalError::ExpectedOrdered(arg1)),
                }
            } else {
                Err(EvalError::ExpectedArgc(2, 0))
            }
        }

        Callback::Builtin(b) => {
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
                        wait(env, value::Value::Unit)
                    }
                    builtins::Builtin::IToA => {
                        let args = args
                            .into_iter()
                            .map(get_int)
                            .collect::<Result<Vec<i64>, EvalError>>()?;
                        wait(env, value::Value::Str(format!("{}", args[0])))
                    }
                    builtins::Builtin::StrCat => {
                        let pieces = args
                            .into_iter()
                            .map(get_str)
                            .collect::<Result<Vec<String>, EvalError>>()?;
                        let result = pieces.into_iter().fold(String::new(), |acc, s| acc + &s);
                        wait(env, value::Value::Str(result))
                    }
                    builtins::Builtin::Ord => {
                        let args = args
                            .into_iter()
                            .map(get_char)
                            .collect::<Result<Vec<char>, EvalError>>()?;
                        wait(env, value::Value::Int(args[0] as i64))
                    }
                    builtins::Builtin::Chr => {
                        let args = args
                            .into_iter()
                            .map(get_int)
                            .collect::<Result<Vec<i64>, EvalError>>()?;
                        let x = u32::try_from(args[0]).ok().and_then(|n| char::from_u32(n));
                        if let Some(c) = x {
                            wait(env, value::Value::Char(c))
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
                            stack.push(Callback::HandleFold(chars, n, k));
                            wait(env, f)
                        } else {
                            let arg = get_str(args.pop().unwrap())?;
                            let chars: Rc<Vec<value::Value>> =
                                Rc::new(arg.chars().map(|c| value::Value::Char(c)).collect());
                            let n = chars.len();
                            wait(env, value::Value::ConstSeq(chars, n))
                        }
                    }
                    builtins::Builtin::List => {
                        let n = args.len();
                        wait(env, value::Value::ConstSeq(Rc::new(args), n))
                    }
                }
            } else {
                Err(EvalError::ExpectedArgc(2, 0))
            }
        }

        Callback::Load(rest, body) => {
            if let value::Value::Str(first) = v {
                let file = File::open(first).unwrap();
                let buffer = charutils::BufReadChars::new(BufReader::new(file));
                let t = tokens::Tokenizer::new(buffer);
                let expr = sparser::parse(t)
                    .or_else(|e| Err(EvalError::SParseError(e)))
                    .and_then(|sexp| parser::parse(sexp).map_err(|e| EvalError::ParseError(e)))?;
                if rest.is_empty() {
                    stack.push(Callback::DropResult(body));
                    cont(ExprOrValue::Expr(expr), env)
                } else {
                    let mut rest = rest;
                    let first = rest.pop_front().unwrap();
                    stack.push(Callback::Load(rest, body));
                    stack.push(Callback::DropResult(ExprOrValue::Value(value::Value::Str(
                        first,
                    ))));
                    cont(ExprOrValue::Expr(expr), env)
                }
            } else {
                Err(EvalError::ExpectedStr(v))
            }
        }

        Callback::Fold(values, num_values) => {
            if let value::Value::Seq(mut args) = v {
                let n = args.len();
                if n != 2 {
                    return Err(EvalError::ExpectedArgc(2, n));
                }
                let f = args.pop().unwrap();
                let k = args.pop().unwrap();
                stack.push(Callback::HandleFold(values, num_values, k));
                wait(env, f)
            } else {
                Err(EvalError::ExpectedArgc(2, 0))
            }
        }

        Callback::HandleFold(values, n, k) => {
            if n == 0 {
                return wait(env, v);
            }
            let n = n - 1;
            let val = values[n].clone();
            let kclone = k.clone();
            stack.push(Callback::HandleFold(values, n, k));
            stack.push(Callback::Apply(VecDeque::from(vec![
                ExprOrValue::Value(val),
                ExprOrValue::Value(v),
            ])));
            wait(env, kclone)
        }
    }
}

pub fn do_one_step(w: Work, stack: &mut Vec<Callback>) -> Result<Outcome, EvalError> {
    let env = w.env;
    match w.expr {
        ExprOrValue::Value(v) => run_cb(stack, env, v),
        ExprOrValue::Expr(parser::Expr::Int(n)) => run_cb(stack, env, value::Value::Int(n)),
        ExprOrValue::Expr(parser::Expr::Bool(b)) => run_cb(stack, env, value::Value::Bool(b)),
        ExprOrValue::Expr(parser::Expr::Char(c)) => run_cb(stack, env, value::Value::Char(c)),
        ExprOrValue::Expr(parser::Expr::Str(s)) => run_cb(stack, env, value::Value::Str(s)),
        ExprOrValue::Expr(parser::Expr::OpExp(o)) => run_cb(stack, env, value::Value::Op(o)),
        ExprOrValue::Expr(parser::Expr::Unit) => run_cb(stack, env, value::Value::Unit),
        ExprOrValue::Expr(parser::Expr::Word(var)) => match env.get(&var) {
            Some(v) => {
                if let value::Value::Thunk(e, body) = v {
                    stack.push(Callback::Restore(env));
                    cont(ExprOrValue::Expr(*body), e)
                } else {
                    run_cb(stack, env, v)
                }
            }
            None => match builtins::Builtin::from_str(&var) {
                Some(b) => run_cb(stack, env, value::Value::Builtin(b)),
                _ => Err(EvalError::UndefinedVar(var.to_string())),
            },
        },
        ExprOrValue::Expr(parser::Expr::Ap(args)) => {
            let mut args: VecDeque<ExprOrValue> = args.into_iter().map(ExprOrValue::Expr).collect();
            let head = args.pop_front().unwrap();
            stack.push(Callback::Apply(args));
            cont(head, env)
        }
        ExprOrValue::Expr(parser::Expr::Let(var, e1, e2)) => {
            stack.push(Callback::Update(var, ExprOrValue::Expr(*e2)));
            cont(ExprOrValue::Expr(*e1), env)
        }
        ExprOrValue::Expr(parser::Expr::Lambda(var, body)) => {
            let cloned = env.clone();
            run_cb(stack, env, value::Value::Lambda(var, cloned, body))
        }
        ExprOrValue::Expr(parser::Expr::Macro(var, body)) => {
            let cloned = env.clone();
            run_cb(stack, env, value::Value::Macro(var, cloned, body))
        }
        ExprOrValue::Expr(parser::Expr::If(guard, branch, default)) => {
            stack.push(Callback::Branch(
                ExprOrValue::Expr(*branch),
                ExprOrValue::Expr(*default),
            ));
            cont(ExprOrValue::Expr(*guard), env)
        }
        ExprOrValue::Expr(parser::Expr::Trace(msg, body)) => {
            stack.push(Callback::Print(ExprOrValue::Expr(*body)));
            cont(ExprOrValue::Expr(*msg), env)
        }
        ExprOrValue::Expr(parser::Expr::Load(files, body)) => {
            let mut files: VecDeque<String> = files.into();
            if files.is_empty() {
                return cont(ExprOrValue::Expr(*body), env);
            }
            let first = files.pop_front().unwrap();
            stack.push(Callback::Load(files, ExprOrValue::Expr(*body)));
            cont(ExprOrValue::Value(value::Value::Str(first)), env)
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
    };
    let mut stack = Vec::new();
    loop {
        let result = do_one_step(w, &mut stack)?;
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
