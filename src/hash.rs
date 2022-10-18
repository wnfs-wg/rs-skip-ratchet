use sha3::{Digest, Sha3_256};
use std::{
    fmt::Debug,
    ops::{BitXor, Index, IndexMut, Not},
    slice::Iter,
};

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Hash(pub [u8; 32]);

impl Hash {
    /// Creates a new Hash from last hash of `n` consecutive hashes of an item.
    pub fn from_chain<T: AsRef<[u8]>>(value: &T, n: usize) -> Self {
        let mut hash = Self::from(value);
        for _ in 1..n {
            hash = Self::from(&hash);
        }

        hash
    }

    pub fn from<T: AsRef<[u8]>>(value: &T) -> Self {
        let mut hasher = Sha3_256::new();
        hasher.update(value.as_ref());
        Self(hasher.finalize().into())
    }

    /// Creates a new Hash from a raw byte array.
    pub fn from_raw(array: [u8; 32]) -> Self {
        Self(array)
    }

    pub fn zero() -> Self {
        Self([0; 32])
    }

    pub fn as_slice(&self) -> &[u8; 32] {
        &self.0
    }

    pub fn iter(&self) -> Iter<u8> {
        self.0.iter()
    }

    pub fn bytes(self) -> [u8; 32] {
        self.0
    }
}

impl BitXor for Hash {
    type Output = Self;

    fn bitxor(mut self, other: Self) -> Self {
        for (a, b) in self.0.iter_mut().zip(other.0.iter()) {
            *a ^= *b;
        }
        Self(self.0)
    }
}

impl Not for Hash {
    type Output = Self;

    fn not(mut self) -> Self {
        for b in self.0.iter_mut() {
            *b = !*b;
        }
        Self(self.0)
    }
}

impl Index<usize> for Hash {
    type Output = u8;

    fn index(&self, index: usize) -> &u8 {
        &self.0[index]
    }
}

impl IndexMut<usize> for Hash {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut u8 {
        &mut self.0[index]
    }
}

impl AsRef<[u8]> for Hash {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl From<Hash> for [u8; 32] {
    #[inline]
    fn from(hash: Hash) -> Self {
        hash.0
    }
}

impl Debug for Hash {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "0x")?;
        for (i, byte) in self.0.iter().enumerate() {
            if i > 6 {
                write!(f, "..")?;
                break;
            } else {
                write!(f, "{:02X}", byte)?;
            }
        }

        Ok(())
    }
}

//--------------------------------------------------------------------------------------------------
// Tests
//--------------------------------------------------------------------------------------------------

#[cfg(test)]
mod hash_tests {
    use super::*;

    #[test]
    fn can_hash_items() {
        let hash = Hash::from(&b"An example of a byte array");
        let expected = Hash::from_raw([
            0xa1, 0x6f, 0x2d, 0x12, 0x23, 0x21, 0x11, 0xb2, 0xb8, 0xca, 0x57, 0x02, 0xcf, 0x55,
            0x25, 0x57, 0xfb, 0xff, 0xc3, 0x40, 0x22, 0x72, 0x62, 0x8e, 0x9c, 0xc0, 0x08, 0x89,
            0x99, 0xd2, 0x4b, 0x2b,
        ]);

        assert_eq!(hash, expected);
    }

    #[test]
    fn xor_operator_xors_bits() {
        let a = Hash::from_raw([0xFF; 32]);
        let b = Hash::from_raw([0xFF; 32]);
        let c = Hash::zero();
        assert_eq!(c, a ^ b);

        let a = Hash::from_raw([0b1000_1110; 32]);
        let b = Hash::from_raw([0b0000_1111; 32]);
        let c = Hash::from_raw([0b1000_0001; 32]);
        assert_eq!(c, a ^ b);

        let a = Hash::from_raw([0b1010_1010; 32]);
        let b = Hash::from_raw([0b0101_0101; 32]);
        let c = Hash::from_raw([0xFF; 32]);
        assert_eq!(c, a ^ b);
    }

    #[test]
    fn complement_operator_applies_one_complements_to_bits() {
        let d = Hash::zero();
        let e = Hash::from_raw([0xFF; 32]);
        assert_eq!(e, !d);

        let d = Hash::from_raw([0b1010_1010; 32]);
        let e = Hash::from_raw([0b0101_0101; 32]);
        assert_eq!(e, !d);
    }

    #[test]
    fn from_n_hashes_n_times() {
        let hash_1 = {
            let h = Hash::from(b"James Cameron");
            let h = Hash::from(&h);
            let h = Hash::from(&h);
            let h = Hash::from(&h);

            Hash::from(&h)
        };

        let hash_2 = Hash::from_chain(b"James Cameron", 5);

        assert_eq!(hash_1, hash_2);
    }
}
