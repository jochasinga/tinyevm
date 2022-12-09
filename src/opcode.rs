use std::{num::ParseIntError, str::FromStr};

#[derive(PartialEq, Eq, Debug)]
pub struct Opcode(pub u8);

impl Opcode {
    pub const ADD: Opcode = Opcode(0x01);
    pub const MUL: Opcode = Opcode(0x02);
    pub const ISZERO: Opcode = Opcode(0x15);
    pub const POP: Opcode = Opcode(0x50);
    pub const SSTORE: Opcode = Opcode(0x55);
    pub const PUSH1: Opcode = Opcode(0x60);
    pub const DUP1: Opcode = Opcode(0x80);
    pub const DUP2: Opcode = Opcode(0x81);
    pub const SWAP1: Opcode = Opcode(0x90);
}

impl FromStr for Opcode {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim_start_matches("0x");
        match u8::from_str_radix(s, 16) {
            Ok(u) => match u {
                0x01 => Ok(Self::ADD),
                0x02 => Ok(Self::MUL),
                0x15 => Ok(Self::ISZERO),
                0x50 => Ok(Self::POP),
                0x55 => Ok(Self::SSTORE),
                0x60 => Ok(Self::PUSH1),
                0x80 => Ok(Self::DUP1),
                0x81 => Ok(Self::DUP2),
                0x90 => Ok(Self::SWAP1),
                v => Ok(Self(v)),
            },
            Err(e) => Err(e),
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_from_str() {
        let add = "0x01".parse::<Opcode>().unwrap();
        assert_eq!(add, Opcode::ADD);
        let add = "01".parse::<Opcode>().unwrap();
        assert_eq!(add, Opcode::ADD);

        let mul = "0x02".parse::<Opcode>().unwrap();
        assert_eq!(mul, Opcode::MUL);
        let mul = "02".parse::<Opcode>().unwrap();
        assert_eq!(mul, Opcode::MUL);

        let pop = "0x50".parse::<Opcode>().unwrap();
        assert_eq!(pop, Opcode::POP);
        let pop = "50".parse::<Opcode>().unwrap();
        assert_eq!(pop, Opcode::POP);

        let sstore = "0x55".parse::<Opcode>().unwrap();
        assert_eq!(sstore, Opcode::SSTORE);
        let sstore = "55".parse::<Opcode>().unwrap();
        assert_eq!(sstore, Opcode::SSTORE);

        let push1 = "0x60".parse::<Opcode>().unwrap();
        assert_eq!(push1, Opcode::PUSH1);
        let push1 = "60".parse::<Opcode>().unwrap();
        assert_eq!(push1, Opcode::PUSH1);

        let dup2 = "0x81".parse::<Opcode>().unwrap();
        assert_eq!(dup2, Opcode::DUP2);
        let dup2 = "81".parse::<Opcode>().unwrap();
        assert_eq!(dup2, Opcode::DUP2);

        let swap1 = "0x90".parse::<Opcode>().unwrap();
        assert_eq!(swap1, Opcode::SWAP1);
        let swap1 = "90".parse::<Opcode>().unwrap();
        assert_eq!(swap1, Opcode::SWAP1);
    }
}
