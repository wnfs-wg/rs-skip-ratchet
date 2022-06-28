use std::{
    ops::{BitXor, Index, IndexMut, Not},
    slice::Iter,
};

use sha3::{Digest, Sha3_256};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
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
}

impl BitXor for Hash {
    type Output = Self;

    fn bitxor(mut self, other: Self) -> Self {
        for (a, b) in self.0.iter_mut().zip(other.0.iter()) {
            *a = *a ^ *b;
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

//--------------------------------------------------------------------------------------------------
// Tests
//--------------------------------------------------------------------------------------------------

#[cfg(test)]
mod hash_tests {
    use super::*;

    #[test]
    fn from_item_hashes() {
        let seed = Hash::from_raw([0xFF; 32]);

        println!("seed = {:?}", seed);

        let hash = Hash::from(&!seed);

        println!("hash = {:?}", hash);

        let hash = Hash::from(&!seed);

        println!("hash = {:?}", hash);
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
            let h = Hash::from(b"James");
            let h = Hash::from(&h);
            let h = Hash::from(&h);
            let h = Hash::from(&h);
            let h = Hash::from(&h);
            h
        };

        let hash_2 = Hash::from_chain(b"James", 5);

        assert_eq!(hash_1, hash_2);
    }
}
