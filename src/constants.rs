/// 256² = 65536, the maximum number of times a skip ratchet can be
/// incremented within the same large epoch.
pub const LARGE_EPOCH_LENGTH: usize = 256 * 256;

/// 256, the maximum number of times a skip ratchet can be
/// incremented within the same medium epoch.
pub const MEDIUM_EPOCH_LENGTH: usize = 256;

/// A domain-separation string used when deriving the ratchet
/// salt from a seed secret.
///
/// Using these prevents accidentally deriving the same state inside the
/// ratchet if the seed passed in is used for other purposes.
pub(crate) const DOMAIN_SEP_STR_SALT: &str = "Skip Ratchet Slt";
/// A domain-separation string used when deriving the ratchet
/// large digit preimage from a seed secret.
///
/// Using these prevents accidentally deriving the same state inside the
/// ratchet if the seed passed in is used for other purposes.
pub(crate) const DOMAIN_SEP_STR_LARGE: &str = "Skip Ratchet Lrg";
