#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Op {
    Plus,   // +
    Times,  // *
    Minus,  // -
    Div,    // /
    Mod,    // %
    Lambda, // \
    Eq,     // =
    Gt,     // >
}
