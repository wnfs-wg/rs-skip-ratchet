use crate::{hash::Hash, salt::Salt, seek::JumpSize, Ratchet};
use hex::FromHex;
use proptest::{prelude::any, strategy::Strategy};

pub(crate) fn hash_from_hex(s: &str) -> Hash {
    Hash::from_raw(<[u8; 32]>::from_hex(s).unwrap())
}

pub(crate) fn salt_from_hex(s: &str) -> Salt {
    Salt::from_raw(<[u8; 32]>::from_hex(s).unwrap())
}

pub(crate) fn salt() -> [u8; 32] {
    salt_from_hex("eafe7de965c8a149d6ad0e1a4bd28c79db7d408f6655b1570e9c16d4a96bfc5e").into()
}

pub(crate) fn seed() -> [u8; 32] {
    hash_from_hex("600b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33").into()
}

pub(crate) fn assert_ratchet_equal(expected: &Ratchet, got: &Ratchet) {
    assert_eq!(format!("{expected:#?}"), format!("{got:#?}"));
}

#[macro_export]
macro_rules! prop_assert_ratchet_eq {
    ($expected:expr, $actual:expr) => {
        prop_assert_eq!(format!("{:#?}", $expected), format!("{:#?}", $actual));
    };
}

pub(crate) fn any_jump_size() -> impl Strategy<Value = JumpSize> {
    (0..3).prop_map(|n| match n {
        0 => JumpSize::Zero,
        1 => JumpSize::Small,
        2 => JumpSize::Medium,
        3 => JumpSize::Large,
        _ => unreachable!(),
    })
}

pub(crate) fn any_ratchet() -> impl Strategy<Value = Ratchet> {
    (any::<[u8; 32]>().no_shrink(), 0..=255u8, 254..=255u8)
        .prop_map(|(seed, inc_small, inc_med)| Ratchet::from_seed(&seed, inc_small, inc_med))
}
