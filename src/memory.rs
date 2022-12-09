use std::u8;

use crate::types::UInt256;

/// TODO: What is the limit of memory? Put 128 for now.
pub struct Memory([u8; 128]);

impl Memory {
    pub fn new() -> Self {
        Memory([0x00; 128])
    }

    /// Public interface to MLOAD.
    /// Reads a uint256 from memory.
    pub fn load(self, offset: usize) -> UInt256 {
        let mut bytes = [0x00; 32];
        for (i, byte) in self.0[offset..offset + 32].iter().enumerate() {
            bytes[i] = *byte;
        }
        UInt256::from_little_endian(&bytes)
    }

    /// Public interface to MSTORE8.
    /// Store a byte in memory.
    pub fn store8(&mut self, offset: usize, val: u8) {
        self.0[offset] = val & 0xff;
    }

    /// Public interface to MSTORE.
    /// Store a 256-bit integer in memory.
    pub fn store(&mut self, offset: usize, val: UInt256) {
        let mut bytes = [0x00; 32];
        val.to_little_endian(&mut bytes);
        for (i, byte) in bytes.iter().enumerate() {
            self.0[offset + i] = *byte;
        }
    }

    /// Public interface to MSIZE.
    /// Size of memory for this contract execution, in bytes.
    pub fn size(&self) -> usize {
        self.0.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_store8() {
        let mut memory = Memory::new();
        memory.store8(0, 0x01);
        let value = memory.load(0);
        let expected = UInt256::from_little_endian(&[0x01]);
        assert_eq!(value, expected);
    }

    /// Test storing 1,000,000,000 in memory as uint256.
    #[test]
    fn test_memory_store() {
        let mut memory = Memory::new();
        let billion = "0x3b9aca00";
        let val = UInt256::from_str_radix(billion, 16).unwrap();
        memory.store(0, val);
        let value = memory.load(0);
        let expected = val;
        assert_eq!(value, expected);
    }
}
