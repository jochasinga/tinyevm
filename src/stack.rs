use crate::types::UInt256;
use std::num::ParseIntError;

use crate::{opcode::Opcode, storage::Storage};

#[derive(PartialEq, Debug)]
pub struct Stack(Vec<UInt256>);

impl Stack {
    pub const EMPTY: Stack = Stack(vec![]);

    pub fn get(&self, i: usize) -> Option<&UInt256> {
        self.0.get(i)
    }

    pub fn top(&self) -> Option<&UInt256> {
        self.0.last()
    }

    pub fn new() -> Self {
        Stack(Vec::<UInt256>::new())
    }

    pub fn push1(&mut self, val: u8) -> Result<(), String> {
        if self.size() == 1024 {
            return Err("Stack overflow".to_string());
        }

        let v = UInt256::from_little_endian(&[val]);
        self.0.push(v);
        Ok(())
    }

    pub fn pop(&mut self) -> (Option<UInt256>, &Self) {
        (self.0.pop(), self)
    }

    pub fn size(&self) -> usize {
        self.0.len()
    }
}

/// Evaluate a vector of opcodes and return the stack.
pub fn eval_opcode(opcode: Vec<Opcode>) -> (Stack, Storage) {
    let mut stack = Stack::new();
    let mut storage = Storage::new();
    let mut sum = UInt256::zero();
    let mut prod = UInt256::one();
    let mut opcodes = opcode.into_iter();

    while let Some(code) = opcodes.next() {
        match code {
            Opcode::PUSH1 => {
                if let Some(Opcode(n)) = opcodes.next() {
                    if let Err(e) = stack.push1(n) {
                        panic!("{}", e);
                    }
                }
            }
            Opcode::ISZERO => {
                if let Some(top) = stack.top() {
                    if top.is_zero() {
                        stack.push1(0x01).unwrap();
                    } else {
                        stack.push1(0x00).unwrap();
                    }
                } else {
                    panic!(
                        "Expect stack to have at least one element. Instead found {}",
                        stack.size()
                    );
                }
            }
            Opcode::DUP1 => {
                if stack.size() < 1 {
                    panic!(
                        "Expect stack to have at least two elements. Instead found {}",
                        stack.size()
                    );
                }

                // Get the last element of the stack and push it back on top
                if let Some(el) = stack.get(stack.size() - 1) {
                    let mut bytes = [0x00; 32];
                    el.to_little_endian(&mut bytes);
                    if let Err(e) = stack.push1(bytes[0]) {
                        panic!("{}", e);
                    }
                }
            }
            Opcode::DUP2 => {
                if stack.size() < 2 {
                    panic!(
                        "Expect stack to have at least two elements. Instead found {}",
                        stack.size()
                    );
                }

                // Get the 2nd last element of the stack and push it back on top
                if let Some(el) = stack.get(stack.size() - 2) {
                    let mut bytes = [0x00; 32];
                    el.to_little_endian(&mut bytes);
                    if let Err(e) = stack.push1(bytes[0]) {
                        panic!("{}", e);
                    }
                }
            }
            Opcode::POP => {
                stack.pop();
            }
            Opcode::SSTORE => {
                if stack.size() < 2 {
                    panic!(
                        "Expect stack to have at least two elements. Instead found {}",
                        stack.size()
                    );
                }
                if let (Some(first), _) = stack.pop() {
                    if let (Some(second), _) = stack.pop() {
                        storage.store(first, second);
                    }
                }
            }
            Opcode::SWAP1 => {
                if stack.size() < 2 {
                    panic!(
                        "Expect stack to have at least two elements. Instead found {}",
                        stack.size()
                    );
                }

                if let (Some(first), _) = stack.pop() {
                    if let (Some(second), _) = stack.pop() {
                        let mut first_bytes = [0x00; 32];
                        let mut second_bytes = [0x00; 32];
                        first.to_little_endian(&mut first_bytes);
                        second.to_little_endian(&mut second_bytes);
                        if let (Err(e1), Err(_)) =
                            (stack.push1(first_bytes[0]), stack.push1(second_bytes[0]))
                        {
                            panic!("{}", e1);
                        }
                    }
                }
            }
            Opcode::ADD => {
                while let (Some(v), _) = stack.pop() {
                    sum += v;
                }

                let mut bytes = [0x00; 32];
                sum.to_little_endian(&mut bytes);
                if let Err(e) = stack.push1(bytes[0]) {
                    panic!("{}", e);
                }
            }
            Opcode::MUL => {
                while let (Some(v), _) = stack.pop() {
                    prod *= v;
                }

                let mut bytes = [0x00; 32];
                prod.to_little_endian(&mut bytes);
                if let Err(e) = stack.push1(bytes[0]) {
                    panic!("{}", e);
                }
            }
            _ => todo!(),
        }
    }
    (stack, storage)
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
        let _ = s.push1(0x01);
        let _ = s.push1(0x02);
        let _ = s.push1(0x03);
        assert_eq!(
            s,
            Stack(vec![
                UInt256::from_little_endian(&[0x01]),
                UInt256::from_little_endian(&[0x02]),
                UInt256::from_little_endian(&[0x03]),
            ])
        );

        let (hd, tl) = s.pop();
        assert_eq!(hd.unwrap(), UInt256::from_little_endian(&[0x03]));
        assert_eq!(
            *tl,
            Stack(vec![
                UInt256::from_little_endian(&[0x01]),
                UInt256::from_little_endian(&[0x02]),
            ])
        );
    }

    #[test]
    fn test_test_stack_overflow() {
        let mut s = Stack::new();
        for _ in 0..=1024 {
            let _ = s.push1(0x60);
        }

        let (_, _) = s.pop();
        assert_eq!(s.size(), 1023);
        let _ = s.push1(0x02);
        assert_eq!(s.size(), 1024);

        if let Err(_) = s.push1(0x03) {
            assert!(true);
        } else {
            assert!(false);
        }
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
    fn test_lex_bytecode_iszero() {
        let result = lex_bytecode("0x600015").unwrap();
        assert_eq!(result, vec![Opcode::PUSH1, Opcode(0x00), Opcode::ISZERO],);
    }

    #[test]
    fn test_lex_bytecode_push1_dup2_swap1_sstore_pop() {
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
        let (mut stack, _) = eval_opcode(result);
        let (hd, tl) = stack.pop();
        assert_eq!(hd.unwrap(), UInt256::from_little_endian(&[0x02]));
        assert_eq!(*tl, Stack::EMPTY);
    }

    /// Basically testing 2 * 2 = 4.
    #[test]
    fn test_eval_mul() {
        let result = lex_bytecode("0x6002600202").unwrap();
        println!("{:?}", result);

        let (mut stack, _) = eval_opcode(result);
        let (hd, tl) = stack.pop();
        assert_eq!(hd.unwrap(), UInt256::from_little_endian(&[0x04]));
        assert_eq!(*tl, Stack::EMPTY);
    }

    #[test]
    fn test_eval_iszero() {
        let result = lex_bytecode("0x600015").unwrap();
        let (mut stack, _) = eval_opcode(result);
        let (hd, tl) = stack.pop();

        // We should end up with 0x01 on the stack for "true".
        assert_eq!(hd.unwrap(), UInt256::from_little_endian(&[0x01]));
        assert_eq!(*tl, Stack(vec![UInt256::from_little_endian(&[0x00])]));
    }

    #[test]
    fn test_eval_push1_dup2_swap1_sstore_pop() {
        let result = lex_bytecode("0x6001600081905550").unwrap();
        let (mut stack, storage) = eval_opcode(result);
        let (hd, _) = stack.pop();
        assert!(hd.is_none());
        let val = storage.load(UInt256::from_little_endian(&[0x00]));
        assert_eq!(*val, UInt256::from_little_endian(&[0x01]));
    }
}
