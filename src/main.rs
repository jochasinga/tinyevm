mod memory;
pub mod opcode;
mod stack;
mod storage;
mod types;
pub use stack::{eval_opcode, lex_bytecode};

fn main() {}
