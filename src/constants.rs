/// Flag the encoding. The default encoding is:
/// * base64URL-unpadded (signified with u)
/// * SHA-256 (0x16: "F" in base64URL)
pub(crate) const RATCHET_SIGNIFIER: &str = "uF";

/// The number of iterations a previous search can use before ratchets are considered unrelated.
pub(crate) const DEFAULT_PREV_BUDGET: usize = 1_000_000;
