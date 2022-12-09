use std::num::ParseIntError;

use crate::{opcode::Opcode, storage::Storage};

#[derive(PartialEq, Debug)]
pub struct Stack(Vec<u8>);

impl Stack {
    pub const EMPTY: Stack = Stack(vec![]);

    pub fn get(&self, i: usize) -> Option<&u8> {
        self.0.get(i)
    }

    pub fn new() -> Self {
        Stack(Vec::<u8>::new())
    }

    pub fn push(&mut self, val: u8) {
        self.0.push(val);
    }

    pub fn pop(&mut self) -> (Option<u8>, &Self) {
        (self.0.pop(), self)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }
}

/// Evaluate a vector of opcodes and return the stack.
pub fn eval_opcode(opcode: Vec<Opcode>) -> Stack {
    let mut stack = Stack::new();
    let mut storage = Storage::new();
    let mut sum = 0x00;
    let mut prod = 0x01;
    let mut opcodes = opcode.into_iter();

    while let Some(code) = opcodes.next() {
        match code {
            Opcode::PUSH1 => {
                if let Some(Opcode(n)) = opcodes.next() {
                    stack.push(n);
                }
            }
            Opcode::DUP2 => {
                if stack.len() < 2 {
                    panic!(
                        "Expect stack to have at least two elements. Instead found {}",
                        stack.len()
                    );
                }
                if let Some(el) = stack.get(stack.len() - 2) {
                    stack.push(*el);
                }
            }
            Opcode::POP => {
                stack.pop();
            }
            Opcode::SSTORE => {
                if stack.len() < 2 {
                    panic!(
                        "Expect stack to have at least two elements. Instead found {}",
                        stack.len()
                    );
                }
                if let (Some(first), _) = stack.pop() {
                    if let (Some(second), _) = stack.pop() {
                        storage.insert(first, second);
                    }
                }
            }
            Opcode::SWAP1 => {
                if stack.len() < 2 {
                    panic!(
                        "Expect stack to have at least two elements. Instead found {}",
                        stack.len()
                    );
                }

                if let (Some(first), _) = stack.pop() {
                    if let (Some(second), _) = stack.pop() {
                        stack.push(first);
                        stack.push(second);
                    }
                }
            }
            Opcode::ADD => {
                while let (Some(v), _) = stack.pop() {
                    sum += v;
                }
                stack.push(sum);
            }
            Opcode::MUL => {
                while let (Some(v), _) = stack.pop() {
                    prod *= v;
                }
                stack.push(prod);
            }
            _ => todo!(),
        }
    }
    stack
}

/// Lex the bytecode, byte by byte, and return a vector of opcodes.
pub fn lex_bytecode(bytecode: &str) -> Result<Vec<Opcode>, ParseIntError> {
    let input = bytecode.trim_start_matches("0x");
    let mut chars = input.chars().into_iter();
    let mut tokens = Vec::<Opcode>::new();

    while let (Some(c1), Some(c2)) = (chars.next(), chars.next()) {
        let hex = format!("0x{}{}", c1, c2);
        let result = hex.parse::<Opcode>();
        if let Err(e) = result {
            return Err(e);
        }

        let opcode = result.unwrap();
        match opcode {
            Opcode::PUSH1 => {
                tokens.push(Opcode::PUSH1);
                if let (Some(c1), Some(c2)) = (chars.next(), chars.next()) {
                    let s = format!("0x{}{}", c1, c2);
                    let result = s.parse::<Opcode>();
                    if let Err(e) = result {
                        return Err(e);
                    } else {
                        tokens.push(result.unwrap());
                    }
                }
            }
            Opcode::ADD => tokens.push(Opcode::ADD),
            Opcode::MUL => tokens.push(Opcode::MUL),
            Opcode::DUP2 => tokens.push(Opcode::DUP2),
            Opcode::POP => tokens.push(Opcode::POP),
            Opcode::SWAP1 => tokens.push(Opcode::SWAP1),
            Opcode::SSTORE => tokens.push(Opcode::SSTORE),
            op => tokens.push(op),
        }
    }
    Ok(tokens)
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_stack() {
        let mut s = Stack::new();
        s.push(0x01);
        s.push(0x02);
        s.push(0x03);
        assert_eq!(s, Stack(vec![0x01, 0x02, 0x03]));

        let (hd, tl) = s.pop();
        assert_eq!(hd.unwrap(), 0x03);
        assert_eq!(*tl, Stack(vec![0x01, 0x02]));
    }

    #[test]
    fn test_lex_bytecode_add() {
        let result = lex_bytecode("0x6001600101").unwrap();
        assert_eq!(
            result,
            vec![
                Opcode::PUSH1,
                Opcode(0x01),
                Opcode::PUSH1,
                Opcode(0x01),
                Opcode::ADD,
            ],
        );
    }

    #[test]
    fn test_lex_bytecode_mul() {
        let result = lex_bytecode("0x6002600202").unwrap();
        assert_eq!(
            result,
            vec![
                Opcode::PUSH1,
                Opcode(0x02),
                Opcode::PUSH1,
                Opcode(0x02),
                Opcode::MUL,
            ],
        );
    }

    #[test]
    fn test_lex_bytecode_2() {
        let result = lex_bytecode("0x6001600081905550").unwrap();
        assert_eq!(
            result,
            vec![
                Opcode::PUSH1,
                Opcode(0x01),
                Opcode::PUSH1,
                Opcode(0x00),
                Opcode::DUP2,
                Opcode::SWAP1,
                Opcode::SSTORE,
                Opcode::POP,
            ],
        );
    }

    /// Basically testing 1 + 1 = 2.
    #[test]
    fn test_eval_add() {
        let result = lex_bytecode("0x6001600101").unwrap();
        println!("{:?}", result);
        let mut stack = eval_opcode(result);
        let (hd, tl) = stack.pop();
        assert_eq!(hd.unwrap(), 0x02);
        assert_eq!(*tl, Stack::EMPTY);
    }

    /// Basically testing 2 * 2 = 4.
    #[test]
    fn test_eval_mul() {
        let result = lex_bytecode("0x6002600202").unwrap();
        println!("{:?}", result);

        let mut stack = eval_opcode(result);
        let (hd, tl) = stack.pop();
        assert_eq!(hd.unwrap(), 0x04);
        assert_eq!(*tl, Stack::EMPTY);
    }

    #[test]
    fn test_eval_2() {
        let result = lex_bytecode("0x6001600081905550").unwrap();
        let mut stack = eval_opcode(result);
        let (hd, _) = stack.pop();
        assert!(hd.is_none());
    }
}
