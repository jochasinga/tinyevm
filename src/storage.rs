use std::collections::HashMap;
use crate::types::UInt256;

#[derive(PartialEq, Debug)]
pub struct Storage(HashMap<UInt256, UInt256>);

impl Storage {
    pub fn new() -> Self {
        Storage(HashMap::new())
    }

    pub fn insert(&mut self, k: UInt256, v: UInt256) {
        self.0.insert(k, v);
    }

    pub fn get(&self, k: UInt256) -> Option<&UInt256> {
        self.0.get(&k)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_storage() {
        let mut storage = Storage::new();
        let k = UInt256::from_little_endian(&[0x00]);
        let v = UInt256::from_little_endian(&[0x01]);
        storage.insert(k, v);
        assert_eq!(storage.get(k), Some(&v));
    }
}
