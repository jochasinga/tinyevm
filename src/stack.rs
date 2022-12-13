use crate::types::UInt256;
use std::num::ParseIntError;

use crate::{memory::Memory, opcode::Opcode, storage::Storage};

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

    pub fn push(&mut self, val: UInt256) -> Result<(), String> {
        if self.size() == 1024 {
            return Err("Stack overflow".to_string());
        }

        // let v = UInt256::from_little_endian(&[val]);
        self.0.push(val);
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
pub fn eval_opcode(opcode: Vec<Opcode>) -> (Stack, Storage, Memory) {
    let mut stack = Stack::new();
    let mut storage = Storage::new();
    let mut memory = Memory::new();
    let mut opcodes = opcode.into_iter();

    while let Some(code) = opcodes.next() {
        match code {
            Opcode::PUSH1 => {
                if let Some(Opcode(n)) = opcodes.next() {
                    if let Err(e) = stack.push(UInt256::from_little_endian(&[n])) {
                        panic!("{}", e);
                    }
                }
            }
            Opcode::PUSH2 => {
                if let (Some(Opcode(m)), Some(Opcode(n))) = (opcodes.next(), opcodes.next()) {
                    let a = format!("0x{}", format!("{:02x}", m) + &format!("{:02x}", n));
                    let res = UInt256::from_str_radix(&a, 16).unwrap();
                    if let Err(e) = stack.push(res) {
                        panic!("{}", e);
                    }
                }
            }
            Opcode::PUSH3 => {
                if let (Some(Opcode(a)), Some(Opcode(b)), Some(Opcode(c))) =
                    (opcodes.next(), opcodes.next(), opcodes.next())
                {
                    let a = format!(
                        "0x{}",
                        format!("{:02x}", a) + &format!("{:02x}", b) + &format!("{:02x}", c)
                    );
                    let res = UInt256::from_str_radix(&a, 16).unwrap();
                    if let Err(e) = stack.push(res) {
                        panic!("{}", e);
                    }
                }
            }
            Opcode::ISZERO => {
                if let Some(top) = stack.top() {
                    if top.is_zero() {
                        stack.push(UInt256::from_little_endian(&[0x01])).unwrap();
                    } else {
                        stack.push(UInt256::from_little_endian(&[0x00])).unwrap();
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
                    // let mut bytes = [0x00; 32];
                    // el.to_little_endian(&mut bytes);
                    if let Err(e) = stack.push(*el) {
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
                    // let mut bytes = [0x00; 32];
                    // el.to_little_endian(&mut bytes);
                    if let Err(e) = stack.push(*el) {
                        panic!("{}", e);
                    }
                }
            }
            Opcode::POP => {
                stack.pop();
            }
            Opcode::MSTORE => {
                if stack.size() < 2 {
                    panic!(
                        "Expect stack to have at least two elements. Instead found {}",
                        stack.size()
                    );
                }
                if let (Some(last), _) = stack.pop() {
                    if let (Some(second_last), _) = stack.pop() {
                        memory.store(last.as_usize(), second_last);
                    }
                }
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
                        // let mut first_bytes = [0x00; 32];
                        // let mut second_bytes = [0x00; 32];
                        // first.to_little_endian(&mut first_bytes);
                        // second.to_little_endian(&mut second_bytes);
                        if let (Err(e1), Err(_)) = (stack.push(first), stack.push(second)) {
                            panic!("{}", e1);
                        }
                    }
                }
            }
            Opcode::ADD => {
                if stack.size() < 2 {
                    panic!(
                        "Expect stack to have at least two elements. Instead found {}",
                        stack.size()
                    );
                }
                if let (Some(last), _) = stack.pop() {
                    if let (Some(second_last), _) = stack.pop() {
                        let sum = last + second_last;
                        // let mut bytes = [0x00; 32];
                        // sum.to_little_endian(&mut bytes);
                        if let Err(e) = stack.push(sum) {
                            panic!("{}", e);
                        }
                    }
                }
            }
            Opcode::MUL => {
                if stack.size() < 2 {
                    panic!(
                        "Expect stack to have at least two elements. Instead found {}",
                        stack.size()
                    );
                }
                if let (Some(last), _) = stack.pop() {
                    if let (Some(second_last), _) = stack.pop() {
                        let prod = last * second_last;
                        // let mut bytes = [0x00; 32];
                        // prod.to_little_endian(&mut bytes);
                        if let Err(e) = stack.push(prod) {
                            panic!("{}", e);
                        }
                    }
                }
            }
            Opcode::SUB => {
                if stack.size() < 2 {
                    panic!(
                        "Expect stack to have at least two elements. Instead found {}",
                        stack.size()
                    );
                }
                if let (Some(last), _) = stack.pop() {
                    if let (Some(second_last), _) = stack.pop() {
                        let diff = last - second_last;
                        // let mut bytes = [0x00; 32];
                        // diff.to_little_endian(&mut bytes);
                        if let Err(e) = stack.push(diff) {
                            panic!("{}", e);
                        }
                    }
                }
            }
            Opcode::DIV => {
                if stack.size() < 2 {
                    panic!(
                        "Expect stack to have at least two elements. Instead found {}",
                        stack.size()
                    );
                }
                if let (Some(last), _) = stack.pop() {
                    if let (Some(second_last), _) = stack.pop() {
                        let div = last / second_last;
                        if let Err(e) = stack.push(div) {
                            panic!("{}", e);
                        }
                    }
                }
            }
            _ => todo!(),
        }
    }
    (stack, storage, memory)
}

fn scan_bytecode(
    mut bytecodes: std::str::Chars,
    mut opcodes: Vec<Opcode>,
) -> Result<Vec<Opcode>, ParseIntError> {
    if bytecodes.clone().count() == 0 {
        return Ok(opcodes);
    }

    if let (Some(c1), Some(c2)) = (bytecodes.next(), bytecodes.next()) {
        let hex = format!("0x{}{}", c1, c2);
        let result = hex.parse::<Opcode>();
        if let Err(e) = result {
            return Err(e);
        }

        let opcode = result.unwrap();
        match opcode {
            Opcode::PUSH1 => {
                opcodes.push(Opcode::PUSH1);
                if let (Some(c1), Some(c2)) = (bytecodes.next(), bytecodes.next()) {
                    let s = format!("0x{}{}", c1, c2);
                    let result = s.parse::<Opcode>();
                    if let Err(e) = result {
                        return Err(e);
                    } else {
                        opcodes.push(result.unwrap());
                    }
                }
            }
            Opcode::PUSH2 => {
                opcodes.push(Opcode::PUSH2);
                if let (Some(c1), Some(c2), Some(c3), Some(c4)) = (
                    bytecodes.next(),
                    bytecodes.next(),
                    bytecodes.next(),
                    bytecodes.next(),
                ) {
                    let s1 = format!("0x{}{}", c1, c2);
                    let result1 = s1.parse::<Opcode>();
                    let s2 = format!("0x{}{}", c3, c4);
                    let result2 = s2.parse::<Opcode>();
                    if let (Err(e), Err(_)) = (result1.clone(), result2.clone()) {
                        return Err(e);
                    } else {
                        opcodes.push(result1.unwrap());
                        opcodes.push(result2.unwrap());
                    }
                }
            }
            Opcode::PUSH3 => {
                opcodes.push(Opcode::PUSH3);
                if let (Some(c1), Some(c2), Some(c3), Some(c4), Some(c5), Some(c6)) = (
                    bytecodes.next(),
                    bytecodes.next(),
                    bytecodes.next(),
                    bytecodes.next(),
                    bytecodes.next(),
                    bytecodes.next(),
                ) {
                    let s1 = format!("0x{}{}", c1, c2);
                    let s2 = format!("0x{}{}", c3, c4);
                    let s3 = format!("0x{}{}", c5, c6);
                    let result1 = s1.parse::<Opcode>();
                    let result2 = s2.parse::<Opcode>();
                    let result3 = s3.parse::<Opcode>();
                    if let (Err(e), Err(_), Err(_)) =
                        (result1.clone(), result2.clone(), result3.clone())
                    {
                        return Err(e);
                    } else {
                        opcodes.push(result1.unwrap());
                        opcodes.push(result2.unwrap());
                        opcodes.push(result3.unwrap());
                    }
                }
            }
            Opcode::ADD => opcodes.push(Opcode::ADD),
            Opcode::MUL => opcodes.push(Opcode::MUL),
            Opcode::SUB => opcodes.push(Opcode::SUB),
            Opcode::DIV => opcodes.push(Opcode::DIV),
            Opcode::DUP2 => opcodes.push(Opcode::DUP2),
            Opcode::POP => opcodes.push(Opcode::POP),
            Opcode::SWAP1 => opcodes.push(Opcode::SWAP1),
            Opcode::SSTORE => opcodes.push(Opcode::SSTORE),
            op => opcodes.push(op),
        }
        scan_bytecode(bytecodes, opcodes)
    } else {
        Ok(opcodes)
    }
}

/// Lex the bytecode, byte by byte, and return a vector of opcodes.
pub fn lex_bytecode(bytecode: &str) -> Result<Vec<Opcode>, ParseIntError> {
    let input = bytecode.trim_start_matches("0x");
    let chars = input.chars();
    let tokens = Vec::<Opcode>::new();
    scan_bytecode(chars, tokens)
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_stack() {
        let mut s = Stack::new();
        let _ = s.push(0x01.into());
        let _ = s.push(0x02.into());
        let _ = s.push(0x03.into());
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
            let _ = s.push(0x60.into());
        }

        let (_, _) = s.pop();
        assert_eq!(s.size(), 1023);
        let _ = s.push(0x02.into());
        assert_eq!(s.size(), 1024);

        if let Err(_) = s.push(0x03.into()) {
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
    fn test_lex_bytecode_div() {
        let result = lex_bytecode("0x6002600404").unwrap();
        assert_eq!(
            result,
            vec![
                Opcode::PUSH1,
                Opcode(0x02),
                Opcode::PUSH1,
                Opcode(0x04),
                Opcode::DIV,
            ],
        );
    }

    #[test]
    fn test_lex_bytecode_push2() {
        let result = lex_bytecode("0x610100600101").unwrap();
        assert_eq!(
            result,
            vec![
                Opcode::PUSH2,
                Opcode(0x01),
                Opcode(0x00),
                Opcode::PUSH1,
                Opcode(0x01),
                Opcode::ADD,
            ],
        );
    }

    #[test]
    fn test_lex_bytecode_push3() {
        let result = lex_bytecode("0x6101006201302f01").unwrap();
        assert_eq!(
            result,
            vec![
                Opcode::PUSH2,
                Opcode(0x01),
                Opcode(0x00),
                Opcode::PUSH3,
                Opcode(0x01),
                Opcode(0x30),
                Opcode(0x2f),
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
    fn test_lex_bytecode_sub() {
        let result = lex_bytecode("0x6001600203").unwrap();
        assert_eq!(
            result,
            vec![
                Opcode::PUSH1,
                Opcode(0x01),
                Opcode::PUSH1,
                Opcode(0x02),
                Opcode::SUB,
            ],
        );
    }

    #[test]
    fn test_lex_bytecode_iszero() {
        let result = lex_bytecode("0x600015").unwrap();
        assert_eq!(result, vec![Opcode::PUSH1, Opcode(0x00), Opcode::ISZERO],);
    }

    #[test]
    fn test_lex_bytecode_mstore() {
        let result = lex_bytecode("0x6060604052").unwrap();
        assert_eq!(
            result,
            vec![
                Opcode::PUSH1,
                Opcode(0x60),
                Opcode::PUSH1,
                Opcode(0x40),
                Opcode::MSTORE,
            ],
        );
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
        let (mut stack, _, _) = eval_opcode(lex_bytecode("0x6001600101").unwrap());
        let (hd, tl) = stack.pop();
        assert_eq!(hd.unwrap(), UInt256::from_little_endian(&[0x02]));
        assert_eq!(*tl, Stack::EMPTY);
    }

    #[test]
    fn test_eval_div() {
        let (mut stack, _, _) = eval_opcode(lex_bytecode("0x6002600404").unwrap());
        let (last, rest) = stack.pop();
        assert_eq!(last.unwrap(), UInt256::from_little_endian(&[0x02]));
        assert_eq!(*rest, Stack::EMPTY);
    }

    #[test]
    fn test_eval_push2() {
        let opcodes = lex_bytecode("0x610100600101").unwrap();
        let (mut stack, _, _) = eval_opcode(opcodes);
        let (last, rest) = stack.pop();
        assert_eq!(
            last.unwrap(),
            UInt256::from_str_radix("0x0101", 16).unwrap()
        );
        assert_eq!(*rest, Stack::EMPTY);
    }

    #[test]
    fn test_eval_push3() {
        let opcodes = lex_bytecode("0x6101006201302f01").unwrap();
        let (mut stack, _, _) = eval_opcode(opcodes);
        let (last, rest) = stack.pop();
        // 0x01302f + 0x0100
        let expected = &format!("{:x}", 77871 + 256);
        assert_eq!(
            last.unwrap(),
            UInt256::from_str_radix(expected, 16).unwrap()
        );
        assert_eq!(*rest, Stack::EMPTY);
    }

    /// Basically testing 2 * 2 = 4.
    #[test]
    fn test_eval_mul() {
        let (mut stack, _, _) = eval_opcode(lex_bytecode("0x6002600202").unwrap());
        let (hd, tl) = stack.pop();
        assert_eq!(hd.unwrap(), UInt256::from_little_endian(&[0x04]));
        assert_eq!(*tl, Stack::EMPTY);
    }

    #[test]
    fn test_eval_sub() {
        let (mut stack, _, _) = eval_opcode(lex_bytecode("0x6001600203").unwrap());
        let (last, rest) = stack.pop();
        assert_eq!(last.unwrap(), UInt256::from_little_endian(&[0x01]));
        assert_eq!(*rest, Stack::EMPTY);
    }

    #[test]
    fn test_eval_iszero() {
        let result = lex_bytecode("0x600015").unwrap();
        let (mut stack, _, _) = eval_opcode(result);
        let (hd, tl) = stack.pop();

        // We should end up with 0x01 on the stack for "true".
        assert_eq!(hd.unwrap(), UInt256::from_little_endian(&[0x01]));
        assert_eq!(*tl, Stack(vec![UInt256::from_little_endian(&[0x00])]));
    }

    #[test]
    fn test_eval_mstore() {
        let result = lex_bytecode("0x6060604052").unwrap();
        let (mut stack, _, memory) = eval_opcode(result);
        let (hd, _) = stack.pop();
        assert!(hd.is_none());
        let value: UInt256 = memory.load(0x40_usize);
        let mut bytes = [0x00; 32];
        value.to_little_endian(&mut bytes);
        assert_eq!(bytes[0], 0x60);
    }

    #[test]
    fn test_eval_push1_dup2_swap1_sstore_pop() {
        let result = lex_bytecode("0x6001600081905550").unwrap();
        let (mut stack, storage, _) = eval_opcode(result);
        let (hd, _) = stack.pop();
        assert!(hd.is_none());
        let val = storage.load(UInt256::from_little_endian(&[0x00]));
        assert_eq!(*val, UInt256::from_little_endian(&[0x01]));
    }
}
