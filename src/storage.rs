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
