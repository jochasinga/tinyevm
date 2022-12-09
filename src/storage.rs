use std::collections::HashMap;

#[derive(PartialEq, Debug)]
pub struct Storage(HashMap<u8, u8>);

impl Storage {
    pub fn new() -> Self {
        Storage(HashMap::new())
    }

    pub fn insert(&mut self, k: u8, v: u8) {
        self.0.insert(k, v);
    }

    pub fn get(&self, k: u8) -> Option<&u8> {
        self.0.get(&k)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_storage() {
        let mut storage = Storage::new();
        storage.insert(0x00, 0x01);
        storage.insert(0x01, 0x02);
        storage.insert(0x02, 0x03);
        assert_eq!(storage.get(0x00), Some(&0x01));
        assert_eq!(storage.get(0x01), Some(&0x02));
        assert_eq!(storage.get(0x02), Some(&0x03));
    }
}
