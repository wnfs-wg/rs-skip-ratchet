/// Flag the encoding. The default encoding is:
/// * base64URL-unpadded (signified with u)
/// * SHA-256 (0x16: "F" in base64URL)
pub(crate) const RATCHET_SIGNIFIER: &str = "uF";

pub const LARGE_EPOCH_LENGTH: usize = 256 * 256;

pub const MEDIUM_EPOCH_LENGTH: usize = 256;
