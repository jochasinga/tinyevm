use std::{ops::{Add, Div, Mul, Sub}, str::FromStr};

pub enum Endian {
    Little,
    Big,
}

pub fn to_uint256(bytes: &[u8], endian: Endian) -> UInt256 {
    match endian {
        Endian::Little => UInt256::from_le(bytes),
        Endian::Big => UInt256::from_be(bytes),
    }
}

impl Default for Endian {
    fn default() -> Self {
        DEFAULT_ENDIAN
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UInt256 {
    high: u128,
    low: u128,
}

impl Div for UInt256 {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        if other.high == 0 && other.low == 0 {
            panic!("Division by zero");
        }

        let mut quotient = UInt256 { high: 0, low: 0 };
        let mut remainder = UInt256 { high: self.high, low: self.low };

        for i in (0..256).rev() {
            // Shift remainder left by 1 to make space for the next bit
            remainder = UInt256 {
                high: (remainder.high << 1) | (remainder.low >> 127),
                low: remainder.low << 1,
            };

            // Set the current bit in the quotient
            if remainder >= other {
                remainder = remainder - other;
                if i >= 128 {
                    quotient.high |= 1 << (i - 128);
                } else {
                    quotient.low |= 1 << i;
                }
            }
        }

        quotient
    }
}

impl Add for UInt256 {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let (low, carry) = self.low.overflowing_add(other.low);
        let high = self.high + other.high + if carry { 1 } else { 0 };
        UInt256 { high, low }
    }
}

impl Sub for UInt256 {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        let (low, borrow) = self.low.overflowing_sub(other.low);
        let high = if borrow {
            self.high - other.high - 1
        } else {
            self.high - other.high
        };

        UInt256 { high, low }
    }
}

impl Mul for UInt256 {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        // Split the values into high and low parts for each operand
        let a_low = self.low;
        let a_high = self.high;
        let b_low = other.low;
        let b_high = other.high;

        // Calculate the partial products
        let low_low = a_low as u128 * b_low as u128; // Low * Low part (128-bit)
        let low_high = a_low as u128 * b_high as u128; // Low * High part (128-bit)
        let high_low = a_high as u128 * b_low as u128; // High * Low part (128-bit)
        let high_high = a_high as u128 * b_high as u128; // High * High part (128-bit)

        // Combine the partial products, managing overflow
        let (low, carry1) = low_low.overflowing_add((low_high << 64) as u128);
        let (low, carry2) = low.overflowing_add((high_low << 64) as u128);
        let high = high_high + (low_high >> 64) + (high_low >> 64) + carry1 as u128 + carry2 as u128;

        UInt256 { high, low }
    }
}

const DEFAULT_RADIX: u32 = 16;
const DEFAULT_ENDIAN: Endian = Endian::Big;

impl FromStr for UInt256 {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.strip_prefix("0x").unwrap_or(s);
        Self::from_str_radix(s, DEFAULT_RADIX)
    }
}

impl From<usize> for UInt256 {
    fn from(value: usize) -> Self {
        UInt256 {
            high: 0,
            low: value as u128,
        }
    }
}

impl TryInto<usize> for UInt256 {
    type Error = String;

    fn try_into(self) -> Result<usize, Self::Error> {
        self.as_usize()
    }
}

impl UInt256 {
    pub fn new(high: u128, low: u128) -> Self {
        UInt256 { high, low }
    }

    pub fn zero() -> Self {
        UInt256 { high: 0, low: 0 }
    }

    pub fn one() -> Self {
        UInt256 { high: 0, low: 1 }
    }

    pub fn max() -> Self {
        UInt256 {
            high: u128::MAX,
            low: u128::MAX,
        }
    }

    pub fn is_zero(&self) -> bool {
        self.high == 0 && self.low == 0
    }

    pub fn as_usize(&self) -> Result<usize, String> {
        let max_usize = Self::from(usize::MAX);
        if self.high != 0 || self.low > max_usize.low {
            return Err("Value too large".to_string());
        }
        Ok(self.low as usize)
    }

    pub fn from_str_radix(s: &str, radix: u32) -> Result<Self, &'static str> {
        let s = s.trim();
        if s.len() != 64 {
            return Err("Invalid length");
        }
        let low = u128::from_str_radix(&s[32..], radix).map_err(|_| "Invalid hex")?;
        let high = u128::from_str_radix(&s[..32], radix).map_err(|_| "Invalid hex")?;
        Ok(UInt256 { high, low })
    }

    pub fn from_le(bytes: &[u8]) -> Self {
        let mut low = 0;
        let mut high = 0;
        for (i, byte) in bytes.iter().enumerate() {
            if i < 16 {
                low |= (*byte as u128) << (i * 8);
            } else {
                high |= (*byte as u128) << ((i - 16) * 8);
            }
        }
        UInt256 { high, low }
    }

    pub fn from_be(bytes: &[u8]) -> Self {
        let mut low = 0;
        let mut high = 0;
        for (i, byte) in bytes.iter().enumerate() {
            if i < 16 {
                low |= (*byte as u128) << ((15 - i) * 8);
            } else {
                high |= (*byte as u128) << ((31 - i) * 8);
            }
        }
        UInt256 { high, low }
    }

    pub fn to_le(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(32);
        for i in 0..32 {
            if i < 16 {
                bytes.push(((self.low >> (i * 8)) & 0xff) as u8);
            } else {
                bytes.push(((self.high >> ((i - 16) * 8)) & 0xff) as u8);
            }
        }
        bytes
    }

    pub fn to_be(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(32);
        for i in 0..32 {
            if i < 16 {
                bytes.push(((self.low >> ((15 - i) * 8)) & 0xff) as u8);
            } else {
                bytes.push(((self.high >> ((31 - i) * 8)) & 0xff) as u8);
            }
        }
        bytes
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_uint256_from_str() {
        let mut u256_value = UInt256::from_str("0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef").unwrap();

        println!("High: {:x}, Low: {:x}", u256_value.high, u256_value.low);
        assert_eq!(u256_value.high, 0x1234567890abcdef1234567890abcdef);
        assert_eq!(u256_value.low, 0x1234567890abcdef1234567890abcdef);

        u256_value = UInt256::max();
        assert_eq!(u256_value.high, 0xffffffffffffffffffffffffffffffff);
        assert_eq!(u256_value.low, 0xffffffffffffffffffffffffffffffff);
    }

    #[test]
    fn test_uint256_add() {
        let u256_value1 = UInt256::max() - UInt256::max() / 2.into();
        let u256_value2 = UInt256::max() / 2.into();
        let u256_value3 = u256_value1 + u256_value2;
        assert_eq!(u256_value3, UInt256::max());
    }

    #[test]
    fn test_uint256_sub() {
        let u256_value1 = UInt256::from(1000_000_000);
        let u256_value2 = UInt256::from(999_999_999);
        let u256_value3 = u256_value1 - u256_value2;
        assert_eq!(u256_value3, UInt256::one());
        let u256_value4 = UInt256::from(801002);
        let u256_value5 = u256_value1 - u256_value4;
        assert_eq!(u256_value5, UInt256::from(999198998));
    }

    #[test]
    fn test_endian_conversion() {
        let bytes = vec![0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10];
        let u256_value = UInt256::from_le(&bytes);
        let le_bytes = u256_value.to_le();
        assert_eq!(bytes, le_bytes);

        let u256_value = UInt256::from_be(&bytes);
        let be_bytes = u256_value.to_be();
        assert_eq!(bytes, be_bytes);
    }
}


