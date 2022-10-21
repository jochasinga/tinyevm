use std::num::ParseIntError;

use crate::opcode::Opcode;

#[derive(PartialEq, Debug)]
pub struct Stack(Vec<u8>);

impl Stack {

    pub const EMPTY: Stack = Stack(vec![]);

    pub fn new() -> Self {
        Stack(Vec::<u8>::new())
    }

    pub fn push(&mut self, val: u8) {
        self.0.push(val);
    }

    pub fn pop(&mut self) -> (Option<u8>, &Self) {
        (self.0.pop(), self)
    }
}

fn eval_opcode(opcode: Vec<Opcode>) -> Stack {
    let mut stack = Stack::new();
    let mut sum = 0x00;
    let mut opcodes = opcode.into_iter();

    while let Some(code) = opcodes.next() {
        if code == Opcode::PUSH1 {
            if let Some(Opcode(n)) = opcodes.next() {
                stack.push(n);
            }
        } else if code == Opcode::ADD {
            while let (Some(v), _) = stack.pop() {
                sum += v;
            }
            stack.push(sum);
        }
    }
    stack
}

/// Lex the bytecode, byte by byte.
fn lex_bytecode(bytecode: &str) -> Result<Vec<Opcode>, ParseIntError> {
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
            },
            Opcode::ADD => tokens.push(Opcode::ADD),
            _ => todo!(),
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
    fn test_lex() {
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
    fn test_eval() {
        let result = lex_bytecode("0x6001600101").unwrap();
        let mut stack = eval_opcode(result);
        let (hd, tl) = stack.pop();
        assert_eq!(hd.unwrap(), 0x02);
        assert_eq!(*tl, Stack::EMPTY);
    }
}

