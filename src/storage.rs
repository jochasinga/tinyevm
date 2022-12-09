use crate::types::UInt256;
use std::collections::HashMap;

#[derive(PartialEq, Debug)]
pub struct Storage(HashMap<UInt256, UInt256>);

impl Storage {
    pub fn new() -> Self {
        Storage(HashMap::new())
    }

    /// Public interface for SLOAD.
    pub fn load(&self, k: UInt256) -> &UInt256 {
        self.get(k).unwrap()
    }

    /// Public interface for SSTORE.
    pub fn store(&mut self, k: UInt256, v: UInt256) {
        self.insert(k, v);
    }

    fn insert(&mut self, k: UInt256, v: UInt256) {
        self.0.insert(k, v);
    }

    fn get(&self, k: UInt256) -> Option<&UInt256> {
        self.0.get(&k)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_storage_private_methods() {
        let mut storage = Storage::new();
        let k = UInt256::from_little_endian(&[0x00]);
        let v = UInt256::from_little_endian(&[0x01]);
        storage.insert(k, v);
        assert_eq!(storage.get(k), Some(&v));
    }

    #[test]
    fn test_storage_public_methods() {
        let mut storage = Storage::new();
        let k = UInt256::from_little_endian(&[0x00]);
        let v = UInt256::from_little_endian(&[0x01]);
        storage.store(k, v);
        assert_eq!(storage.load(k), &v);
    }
}
