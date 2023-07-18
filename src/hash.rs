use std::fmt::Debug;

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Hash(
    #[cfg_attr(feature = "serde", serde(with = "crate::serde_byte_array"))] [u8; 32],
);

impl Hash {
    /// Creates a new Hash from last hash of `n` consecutive hashes of an item.
    /// Adds in the prefix bytes for each hash.
    pub(crate) fn from_chain(prefix: impl AsRef<[u8]>, value: impl AsRef<[u8]>, n: usize) -> Self {
        let mut hash = Self::from(&prefix, value);
        for _ in 1..n {
            hash = Self::from(&prefix, hash);
        }

        hash
    }

    /// Creates a keyed Hash by hashing the value with given prefix.
    pub(crate) fn from(prefix: impl AsRef<[u8]>, value: impl AsRef<[u8]>) -> Self {
        let mut hasher = blake3::Hasher::new();
        hasher.update(prefix.as_ref());
        hasher.update(value.as_ref());
        Self(hasher.finalize().into())
    }

    #[cfg(test)]
    /// Creates a new Hash from a raw byte array.
    pub fn from_raw(array: [u8; 32]) -> Self {
        Self(array)
    }

    pub(crate) fn as_slice(&self) -> &[u8; 32] {
        &self.0
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
                write!(f, "{byte:02X}")?;
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
        let hash = Hash::from([], b"An example of a byte array");
        let expected = Hash::from_raw([
            0xe2, 0xeb, 0x80, 0x2e, 0x0c, 0x70, 0xe6, 0x8d, 0xdc, 0xd5, 0x20, 0xfe, 0x34, 0x90,
            0x1c, 0x0d, 0xef, 0x38, 0x2d, 0x82, 0xc6, 0x02, 0xee, 0x12, 0x44, 0x03, 0x87, 0x9c,
            0xf3, 0x7b, 0xce, 0xe9,
        ]);

        assert_eq!(hash, expected);
    }

    #[test]
    fn from_n_hashes_n_times() {
        let prefix = "test Hash::from_chain";
        let hash_1 = {
            let h = Hash::from(prefix, b"James Cameron");
            let h = Hash::from(prefix, h);
            let h = Hash::from(prefix, h);
            let h = Hash::from(prefix, h);

            Hash::from(prefix, h)
        };

        let hash_2 = Hash::from_chain(prefix, b"James Cameron", 5);

        assert_eq!(hash_1, hash_2);
    }
}
