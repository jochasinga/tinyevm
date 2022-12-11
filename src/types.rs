use primitive_types::U256;

/// Just an alias for `primitive_types::U256`.
pub type UInt256 = U256;

pub enum Endian {
    Little,
    Big,
}

pub fn to_uint256(bytes: &[u8], endian: Endian) -> UInt256 {
    match endian {
        Endian::Little => UInt256::from_little_endian(bytes),
        Endian::Big => UInt256::from_big_endian(bytes),
    }
}
