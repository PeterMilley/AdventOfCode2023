use std::error::Error;
use std::fmt;

#[derive(Debug, Clone, Copy)]
pub enum Argc {
    AtLeast(usize),
    Exactly(usize),
    Either(usize, usize),
}

impl Argc {
    pub fn to_string(self) -> String {
        match self {
            Argc::AtLeast(n) => format!("at least {} args", n),
            Argc::Exactly(n) => format!("exactly {} args", n),
            Argc::Either(n, m) => format!("either {} or {} args", n, m),
        }
    }

    pub fn matches(self, n: usize) -> bool {
        match self {
            Argc::AtLeast(m) => n >= m,
            Argc::Exactly(m) => n == m,
            Argc::Either(u, v) => (n == u) || (n == v),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Builtin {
    Print,
    IToA,
    StrCat,
    Ord,
    Chr,
    Chars,
    List,
}

impl Builtin {
    pub fn to_string(self) -> String {
        match self {
            Builtin::Print => "print".to_string(),
            Builtin::IToA => "itoa".to_string(),
            Builtin::StrCat => "strcat".to_string(),
            Builtin::Ord => "ord".to_string(),
            Builtin::Chr => "chr".to_string(),
            Builtin::Chars => "chars".to_string(),
            Builtin::List => "list".to_string(),
        }
    }

    pub fn from_str(s: &str) -> Option<Builtin> {
        match s {
            "print" => Some(Builtin::Print),
            "itoa" => Some(Builtin::IToA),
            "strcat" => Some(Builtin::StrCat),
            "ord" => Some(Builtin::Ord),
            "chr" => Some(Builtin::Chr),
            "chars" => Some(Builtin::Chars),
            "list" => Some(Builtin::List),
            _ => None,
        }
    }

    pub fn argc(self) -> Argc {
        match self {
            Builtin::Print => Argc::AtLeast(1),
            Builtin::IToA => Argc::Exactly(1),
            Builtin::StrCat => Argc::AtLeast(0),
            Builtin::Ord => Argc::Exactly(1),
            Builtin::Chr => Argc::Exactly(1),
            Builtin::Chars => Argc::Either(1, 3),
            Builtin::List => Argc::AtLeast(0),
        }
    }

    pub fn argc_matches(self, n: usize) -> Result<(), BuiltinError> {
        let c = self.argc();
        if !c.matches(n) {
            return Err(BuiltinError::BadArgc(self, n, c));
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub enum BuiltinError {
    BadArgc(Builtin, usize, Argc),
}

impl fmt::Display for BuiltinError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BuiltinError::BadArgc(b, n, c) => write!(
                f,
                "expected {} for {}, got {}",
                c.to_string(),
                b.to_string(),
                n
            ),
        }
    }
}

impl Error for BuiltinError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}
