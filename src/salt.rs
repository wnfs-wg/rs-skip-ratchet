use rand::{Rng, RngCore};
use std::fmt::Debug;

use crate::hash::Hash;

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Salt(
    #[cfg_attr(feature = "serde", serde(with = "crate::serde_byte_array"))] pub [u8; 32],
);
impl Salt {
    pub fn random(rng: &mut impl RngCore) -> Self {
        Self(rng.gen::<[u8; 32]>())
    }
}

impl From<Hash> for Salt {
    fn from(hash: Hash) -> Self {
        Self(hash.0)
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
