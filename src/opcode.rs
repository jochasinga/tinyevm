use std::{num::ParseIntError, str::FromStr};

#[derive(PartialEq, Eq, Debug)]
pub struct Opcode(pub u8);

impl Opcode {
    pub const ADD: Opcode = Opcode(0x01);
    pub const MUL: Opcode = Opcode(0x02);
    pub const SUB: Opcode = Opcode(0x03);
    pub const DIV: Opcode = Opcode(0x04);
    pub const ISZERO: Opcode = Opcode(0x15);
    pub const POP: Opcode = Opcode(0x50);
    pub const MSTORE: Opcode = Opcode(0x52);
    pub const SSTORE: Opcode = Opcode(0x55);
    pub const PUSH1: Opcode = Opcode(0x60);
    pub const PUSH2: Opcode = Opcode(0x61);
    pub const PUSH3: Opcode = Opcode(0x62);
    pub const DUP1: Opcode = Opcode(0x80);
    pub const DUP2: Opcode = Opcode(0x81);
    pub const SWAP1: Opcode = Opcode(0x90);

    /// Read opcodes from a file generated by solc.
    pub fn from_file(filename: &str) -> Vec<Opcode> {
        let mut opcodes = Vec::new();
        let file = std::fs::read_to_string(filename).unwrap();
        let mut it = file.split_whitespace().into_iter();
        while let Some(s) = it.next() {
            let opcode = s.parse::<Opcode>().unwrap();
            opcodes.push(opcode);
            if s == "PUSH2" {
                let mut b = it.next().unwrap();
                b = b.trim_start_matches("0x");
                let b1 = b[0..2].to_string();
                let b2 = b[2..4].to_string();
                opcodes.push(format!("0x{}", b1).parse::<Opcode>().unwrap());
                opcodes.push(format!("0x{}", b2).parse::<Opcode>().unwrap());
            }
            if s == "PUSH3" {
                let mut b = it.next().unwrap();
                b = b.trim_start_matches("0x");
                let b1 = b[0..2].to_string();
                let b2 = b[2..4].to_string();
                let b3 = b[4..6].to_string();
                opcodes.push(format!("0x{}", b1).parse::<Opcode>().unwrap());
                opcodes.push(format!("0x{}", b2).parse::<Opcode>().unwrap());
                opcodes.push(format!("0x{}", b3).parse::<Opcode>().unwrap());
            }
        }
        opcodes
    }
}

impl FromStr for Opcode {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim_start_matches("0x");
        match u8::from_str_radix(s, 16) {
            Ok(u) => match u {
                0x01 => Ok(Self::ADD),
                0x02 => Ok(Self::MUL),
                0x03 => Ok(Self::SUB),
                0x04 => Ok(Self::DIV),
                0x15 => Ok(Self::ISZERO),
                0x50 => Ok(Self::POP),
                0x52 => Ok(Self::MSTORE),
                0x55 => Ok(Self::SSTORE),
                0x60 => Ok(Self::PUSH1),
                0x61 => Ok(Self::PUSH2),
                0x63 => Ok(Self::PUSH3),
                0x80 => Ok(Self::DUP1),
                0x81 => Ok(Self::DUP2),
                0x90 => Ok(Self::SWAP1),
                v => Ok(Self(v)),
            },
            Err(e) => match s {
                "ADD" => Ok(Self::ADD),
                "MUL" => Ok(Self::MUL),
                "SUB" => Ok(Self::SUB),
                "DIV" => Ok(Self::DIV),
                "ISZERO" => Ok(Self::ISZERO),
                "POP" => Ok(Self::POP),
                "MSTORE" => Ok(Self::MSTORE),
                "SSTORE" => Ok(Self::SSTORE),
                "PUSH1" => Ok(Self::PUSH1),
                "PUSH2" => Ok(Self::PUSH2),
                "PUSH3" => Ok(Self::PUSH3),
                "DUP1" => Ok(Self::DUP1),
                "DUP2" => Ok(Self::DUP2),
                "SWAP1" => Ok(Self::SWAP1),
                _ => Err(e),
            },
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_from_file() {
        let opcodes = Opcode::from_file("tests/Example.opcode");
        assert_eq!(opcodes.len(), 5);
        assert_eq!(opcodes[0], Opcode::PUSH1);
        assert_eq!(opcodes[1], Opcode(0x80));
        assert_eq!(opcodes[2], Opcode::PUSH1);
        assert_eq!(opcodes[3], Opcode(0x40));
        assert_eq!(opcodes[4], Opcode::ISZERO);

        let opcodes = Opcode::from_file("tests/Example2.opcode");
        assert_eq!(opcodes.len(), 6);
        assert_eq!(opcodes[0], Opcode::PUSH1);
        assert_eq!(opcodes[1], Opcode(0x80));
        assert_eq!(opcodes[2], Opcode::PUSH2);
        assert_eq!(opcodes[3], Opcode(0x40));
        assert_eq!(opcodes[4], Opcode(0x50));
        assert_eq!(opcodes[5], Opcode::ISZERO);

        let opcodes = Opcode::from_file("tests/Example3.opcode");
        assert_eq!(opcodes.len(), 8);
        assert_eq!(opcodes[0], Opcode::PUSH3);
        assert_eq!(opcodes[1], Opcode(0x80));
        assert_eq!(opcodes[2], Opcode(0x30));
        assert_eq!(opcodes[3], Opcode(0xff));
        assert_eq!(opcodes[4], Opcode::PUSH2);
        assert_eq!(opcodes[5], Opcode(0x40));
        assert_eq!(opcodes[6], Opcode(0x50));
        assert_eq!(opcodes[7], Opcode::ISZERO);
    }

    #[test]
    fn test_from_str() {
        let mut add = "0x01".parse::<Opcode>().unwrap();
        assert_eq!(add, Opcode::ADD);
        add = "01".parse::<Opcode>().unwrap();
        assert_eq!(add, Opcode::ADD);
        add = "ADD".parse::<Opcode>().unwrap();
        assert_eq!(add, Opcode::ADD);

        let mut mul = "0x02".parse::<Opcode>().unwrap();
        assert_eq!(mul, Opcode::MUL);
        mul = "02".parse::<Opcode>().unwrap();
        assert_eq!(mul, Opcode::MUL);
        mul = "MUL".parse::<Opcode>().unwrap();
        assert_eq!(mul, Opcode::MUL);

        let mut sub = "0x03".parse::<Opcode>().unwrap();
        assert_eq!(sub, Opcode::SUB);
        sub = "03".parse::<Opcode>().unwrap();
        assert_eq!(sub, Opcode::SUB);
        sub = "SUB".parse::<Opcode>().unwrap();
        assert_eq!(sub, Opcode::SUB);

        let mut div = "0x04".parse::<Opcode>().unwrap();
        assert_eq!(div, Opcode::DIV);
        div = "04".parse::<Opcode>().unwrap();
        assert_eq!(div, Opcode::DIV);
        div = "DIV".parse::<Opcode>().unwrap();
        assert_eq!(div, Opcode::DIV);

        let mut iszero = "0x15".parse::<Opcode>().unwrap();
        assert_eq!(iszero, Opcode::ISZERO);
        iszero = "15".parse::<Opcode>().unwrap();
        assert_eq!(iszero, Opcode::ISZERO);
        iszero = "ISZERO".parse::<Opcode>().unwrap();
        assert_eq!(iszero, Opcode::ISZERO);

        let mut pop = "0x50".parse::<Opcode>().unwrap();
        assert_eq!(pop, Opcode::POP);
        pop = "50".parse::<Opcode>().unwrap();
        assert_eq!(pop, Opcode::POP);
        pop = "POP".parse::<Opcode>().unwrap();
        assert_eq!(pop, Opcode::POP);

        let mut sstore = "0x55".parse::<Opcode>().unwrap();
        assert_eq!(sstore, Opcode::SSTORE);
        sstore = "55".parse::<Opcode>().unwrap();
        assert_eq!(sstore, Opcode::SSTORE);
        sstore = "SSTORE".parse::<Opcode>().unwrap();
        assert_eq!(sstore, Opcode::SSTORE);

        let mut push1 = "0x60".parse::<Opcode>().unwrap();
        assert_eq!(push1, Opcode::PUSH1);
        push1 = "60".parse::<Opcode>().unwrap();
        assert_eq!(push1, Opcode::PUSH1);
        push1 = "PUSH1".parse::<Opcode>().unwrap();
        assert_eq!(push1, Opcode::PUSH1);

        let mut push2 = "0x61".parse::<Opcode>().unwrap();
        assert_eq!(push2, Opcode::PUSH2);
        push2 = "61".parse::<Opcode>().unwrap();
        assert_eq!(push2, Opcode::PUSH2);
        push2 = "PUSH2".parse::<Opcode>().unwrap();
        assert_eq!(push2, Opcode::PUSH2);

        let mut push3 = "0x62".parse::<Opcode>().unwrap();
        assert_eq!(push3, Opcode::PUSH3);
        push3 = "62".parse::<Opcode>().unwrap();
        assert_eq!(push3, Opcode::PUSH3);
        push3 = "PUSH3".parse::<Opcode>().unwrap();
        assert_eq!(push3, Opcode::PUSH3);

        let mut dup1 = "0x80".parse::<Opcode>().unwrap();
        assert_eq!(dup1, Opcode::DUP1);
        dup1 = "80".parse::<Opcode>().unwrap();
        assert_eq!(dup1, Opcode::DUP1);
        dup1 = "DUP1".parse::<Opcode>().unwrap();
        assert_eq!(dup1, Opcode::DUP1);

        let mut dup2 = "0x81".parse::<Opcode>().unwrap();
        assert_eq!(dup2, Opcode::DUP2);
        dup2 = "81".parse::<Opcode>().unwrap();
        assert_eq!(dup2, Opcode::DUP2);
        dup2 = "DUP2".parse::<Opcode>().unwrap();
        assert_eq!(dup2, Opcode::DUP2);

        let mut swap1 = "0x90".parse::<Opcode>().unwrap();
        assert_eq!(swap1, Opcode::SWAP1);
        swap1 = "90".parse::<Opcode>().unwrap();
        assert_eq!(swap1, Opcode::SWAP1);
        swap1 = "SWAP1".parse::<Opcode>().unwrap();
        assert_eq!(swap1, Opcode::SWAP1);
    }
}
