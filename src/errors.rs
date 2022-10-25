use crate::constants::RATCHET_SIGNIFIER;
use base64::DecodeError;
use std::{
    error::Error,
    fmt::{self, Display, Formatter},
};

/// This type is used to indicate errors that occur interpreting a `Ratchet`
#[derive(Debug)]
pub enum RatchetErr {
    BadLen(usize),
    BadEncoding(String),
    UnknownRelation,
    Decode(DecodeError),
}

/// This type is used to indicate errors that occur when getting a previous version of a `Ratchet`.
#[derive(Debug, PartialEq, Eq)]
pub enum PreviousErr {
    BudgetExceeded,
    EqualRatchets,
    OlderRatchet,
}

impl Display for RatchetErr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            RatchetErr::BadLen(i) => write!(f, "invalid ratchet length {i}"),
            RatchetErr::BadEncoding(s) => write!(
                f,
                "unsupported ratched encoding: '{}'. only '{}' is supported",
                s, RATCHET_SIGNIFIER
            ),
            RatchetErr::UnknownRelation => write!(f, "cannot relate ratchets"),
            RatchetErr::Decode(e) => write!(f, "{e:?}"),
        }
    }
}

impl Error for RatchetErr {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match *self {
            RatchetErr::Decode(ref e) => Some(e),
            _ => None,
        }
    }
}

impl From<DecodeError> for RatchetErr {
    fn from(err: DecodeError) -> RatchetErr {
        RatchetErr::Decode(err)
    }
}

impl Display for PreviousErr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match *self {
            PreviousErr::BudgetExceeded => write!(f, "ratchet discrepancy budget exceeded"),
            PreviousErr::EqualRatchets => write!(f, "ratchets are equal"),
            PreviousErr::OlderRatchet => write!(f, "current ratchet is older than given ratchet"),
        }
    }
}
