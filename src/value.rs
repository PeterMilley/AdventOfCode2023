use std::boxed::Box;
use std::rc::Rc;

use crate::builtins;
use crate::operators;
use crate::parser;
use crate::varenv;

#[derive(Debug, Clone)]
pub enum Value {
    Int(i64),
    Bool(bool),
    Char(char),
    Str(String),
    Op(operators::Op),
    Lambda(String, Rc<varenv::Env>, Box<parser::Expr>),
    Macro(String, Rc<varenv::Env>, Box<parser::Expr>),
    Thunk(Rc<varenv::Env>, Box<parser::Expr>),
    ConstSeq(Rc<Vec<Value>>, usize),
    Builtin(builtins::Builtin),
    Unit,
    Seq(Vec<Value>),
}

impl Value {
    pub fn to_string(&self) -> String {
        match self {
            Value::Int(n) => format!("{}", n),
            Value::Bool(b) => {
                if *b {
                    "true".to_string()
                } else {
                    "false".to_string()
                }
            }
            Value::Char(c) => format!("{}", c),
            Value::Str(s) => s.clone(),
            Value::Op(o) => match o {
                operators::Op::Plus => "+".to_string(),
                operators::Op::Times => "*".to_string(),
                operators::Op::Minus => "-".to_string(),
                operators::Op::Div => "/".to_string(),
                operators::Op::Mod => "%".to_string(),
                operators::Op::Lambda => "\\".to_string(),
                operators::Op::Eq => "=".to_string(),
                operators::Op::Gt => ">".to_string(),
            },
            Value::Lambda(s, _, _) => format!("\\{} -> (...)", s),
            Value::Macro(s, _, _) => format!("macro {} -> (...)", s),
            Value::Thunk(_, _) => "#thunk#".to_string(),
            Value::ConstSeq(v, _) => format!("{:?}", v.as_ref()),
            Value::Builtin(b) => b.to_string(),
            Value::Unit => "()".to_string(),
            Value::Seq(s) => {
                let mut result = String::new();
                for (i, part) in s.iter().enumerate() {
                    if i > 0 {
                        result.push_str(", ");
                    }
                    result.push_str(&part.to_string());
                }
                result
            }
        }
    }
}
