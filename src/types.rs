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

impl std::fmt::Display for UInt256 {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "0x{:032x}{:032x}", self.high, self.low)
    }
}


impl Div for UInt256 {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        if other.high == 0 && other.low == 0 {
            panic!("Division by zero");
        }

        let mut quotient = UInt256 { high: 0, low: 0 };
        let mut remainder = UInt256 { high: self.high, low: self.low };

        // Start the division bit by bit from the most significant bit
        for i in (0..256).rev() {
            // Shift remainder left by 1 bit to make space for the next bit
            remainder = remainder << 1;

            // Set the current bit in the quotient if remainder >= other
            let shifted_other = other << i;
            if remainder >= shifted_other {
                remainder = remainder - shifted_other;
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

    fn add(self, rhs: Self) -> Self {
        let (low, carry_low) = self.low.overflowing_add(rhs.low);

        if carry_low {
            let (high, carry_high) = self.high.overflowing_add(rhs.high);
            if carry_high {
                panic!("addition overflow on most significant bits");
            }
            if high == u128::MAX {
                panic!("addition overflow on least significant bits");
            }
            let res = UInt256 {
                high: high + 1,
                low: self.low
            };
            return res;
        }
        let res = UInt256 {
            high: self.high,
            low,
        };
        return res;
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

// Helper implementation for left shift (<<) to handle shifting UInt256 by bit positions
impl std::ops::Shl<u32> for UInt256 {
    type Output = Self;

    fn shl(self, shift: u32) -> Self {
        if shift >= 128 {
            UInt256 {
                high: self.low << (shift - 128),
                low: 0,
            }
        } else {
            UInt256 {
                high: (self.high << shift) | (self.low >> (128 - shift)),
                low: self.low << shift,
            }
        }
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
    pub const ZERO: Self = Self { high: 0, low: 0 };
    pub const ONE: Self = Self { high: 0, low: 1 };
    pub const MAX: Self = Self {
        high: u128::MAX,
        low: u128::MAX,
    };

    pub fn new(high: u128, low: u128) -> Self {
        UInt256 { high, low }
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
        assert_eq!(u256_value.high, 0x1234567890abcdef1234567890abcdef);
        assert_eq!(u256_value.low, 0x1234567890abcdef1234567890abcdef);
        u256_value = UInt256::MAX;
        assert_eq!(u256_value.high, 0xffffffffffffffffffffffffffffffff);
        assert_eq!(u256_value.low, 0xffffffffffffffffffffffffffffffff);
    }

    #[cfg(test)]
    mod test_addition {
        use std::u128;
        use super::*;

        fn subtract_bitwise(lhs: u128, rhs: u128) -> u128{
            lhs.wrapping_add(!rhs).wrapping_add(1)
        }

        #[test]
        #[should_panic(expected = "addition overflow on least significant bits")]
        fn test_uint256_add_overflow() {
            let a = UInt256::MAX;
            let b = UInt256::ONE;
            let _ = a + b;
        }

        #[test]
        fn test_uint256_add_basic() {
            let a = UInt256::from(1000_000_000);
            let b = UInt256::from(999_999_999);
            let c = a + b;
            assert_eq!(c, UInt256::from(1999_999_999));
        }

        #[test]
        fn test_uint256_zero_property() {
            let c = UInt256::MAX + UInt256::ZERO;
            assert_eq!(c, UInt256::MAX);
        }

        #[test]
        fn test_uint256_add_big() {
            let a = UInt256::MAX - UInt256::ONE;
            let b = UInt256::ONE;
            let c = a + b;
            assert_eq!(c, UInt256::MAX);
        }
    }

    #[test]
    fn test_uint256_sub() {
        let u256_value1 = UInt256::from(1000_000_000);
        let u256_value2 = UInt256::from(999_999_999);
        let u256_value3 = u256_value1 - u256_value2;
        assert_eq!(u256_value3, UInt256::ONE);
        let u256_value4 = UInt256::from(801002);
        let u256_value5 = u256_value1 - u256_value4;
        assert_eq!(u256_value5, UInt256::from(999198998));
    }

    #[test]
    fn test_uint256_mul() {
        let u256_value1 = UInt256::from(1000_000_000);
        let u256_value2 = UInt256::from(999_999_999);
        let u256_value3 = u256_value1 * u256_value2;
        assert_eq!(u256_value3, UInt256::from(999_999_999_000_000_000));
    }

    #[test]
    fn test_uint256_div() {
        let u256_value1 = UInt256::from(10_000_000);
        let u256_value2 = UInt256::from(2);
        let u256_value3 = u256_value1 / u256_value2;
        let quotient = UInt256::from(5_000_000);
        assert_eq!(u256_value3, quotient);
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

    #[cfg(test)]
    mod div_tests {
        use super::*;
        #[test]
        fn test_div_basic() {
            // Test division of two simple numbers
            let a = UInt256 { high: 0, low: 10 };
            let b = UInt256 { high: 0, low: 2 };
            let result = a / b;
            let quotient = UInt256 { high: 0, low: 5 };
            assert_eq!(result, quotient);
        }

        #[test]
        fn test_div_by_one() {
            // Test division by one (should return the original number)
            let a = UInt256 { high: 12345, low: 67890 };
            let b = UInt256 { high: 0, low: 1 };
            let result = a / b;
            let quotient = a;
            assert_eq!(result, quotient);
        }

        #[test]
        fn test_div_large_divisor() {
            // Test division where the divisor is greater than the dividend (should return zero)
            let a = UInt256 { high: 0, low: 5 };
            let b = UInt256 { high: 0, low: 10 };
            let result = a / b;
            let quotient = UInt256 { high: 0, low: 0 };
            assert_eq!(result, quotient);
        }

        #[test]
        fn test_div_self() {
            // Test division of a number by itself (should return one)
            let a = UInt256 { high: 12345, low: 67890 };
            let result = a / a;
            let quotient = UInt256 { high: 0, low: 1 };
            assert_eq!(result, quotient);
        }

        #[test]
        #[should_panic(expected = "Division by zero")]
        fn test_div_by_zero() {
            // Test division by zero (should panic)
            let a = UInt256 { high: 1, low: 0 };
            let b = UInt256 { high: 0, low: 0 };
            let _ = a / b; // This should panic
        }

        #[test]
        fn test_div_large_numbers() {
            // Test division with large numbers
            let a = UInt256 {
                high: 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
                low: 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
            };
            let b = UInt256 { high: 0, low: 2 };
            let result = a / b;
            let quotient = UInt256 {
                high: 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
                low: 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
            };
            assert_eq!(result, quotient);
        }
    }
}


