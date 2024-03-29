use crate::hash::Hash;
use std::fmt::Debug;

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Salt(
    #[cfg_attr(feature = "serde", serde(with = "crate::serde_byte_array"))] [u8; 32],
);

impl Salt {
    pub(crate) fn from_raw(raw: [u8; 32]) -> Self {
        Self(raw)
    }
}

impl From<Hash> for Salt {
    fn from(hash: Hash) -> Self {
        Self(*hash.as_slice())
    }
}

impl Debug for Salt {
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

impl AsRef<[u8]> for Salt {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl From<Salt> for [u8; 32] {
    #[inline]
    fn from(seed: Salt) -> Self {
        seed.0
    }
}
