use std::{str::FromStr, num::ParseIntError};

#[derive(PartialEq, Eq, Debug)]
pub struct Opcode(pub u8);

impl Opcode {
    pub const ADD: Opcode = Opcode(0x01);
    pub const PUSH1: Opcode = Opcode(0x60);
}

impl FromStr for Opcode {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim_start_matches("0x");
        match u8::from_str_radix(s, 16) {
            Ok(u) => {
                match u {
                    0x01 => Ok(Self::ADD),
                    0x60 => Ok(Self::PUSH1),
                    v => Ok(Self(v)),
                }
            }
            Err(e) => Err(e),
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_from_str() {
        let result = "0x60".parse::<Opcode>().unwrap();
        assert_eq!(result, Opcode::PUSH1);
        let result = "60".parse::<Opcode>().unwrap();
        assert_eq!(result, Opcode::PUSH1);
    }
}

