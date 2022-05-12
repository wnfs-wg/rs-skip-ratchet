use std::{
    error::Error,
    fmt::{self, Display, Formatter},
};

use base64::DecodeError;

use crate::constants::RATCHET_SIGNIFIER;

#[derive(Debug)]
pub enum RatchetErr {
    BadLen(usize),
    BadEncoding(String),
    UnknownRelation,
    Decode(DecodeError),
}

#[derive(Debug)]
pub enum PreviousErr {
    ExhaustedBudget,
    EqualRatchets,
    OlderRatchet,
}

impl Display for RatchetErr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match &*self {
            RatchetErr::BadLen(i) => write!(f, "invalid ratchet length {}", i),
            RatchetErr::BadEncoding(s) => write!(
                f,
                "unsupported ratched encoding: '{}'. only '{}' is supported",
                s, RATCHET_SIGNIFIER
            ),
            RatchetErr::UnknownRelation => write!(f, "cannot relate ratchets"),
            RatchetErr::Decode(e) => write!(f, "{:?}", e),
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
            PreviousErr::ExhaustedBudget => write!(f, "exhausted ratchet discrepency budget"),
            PreviousErr::EqualRatchets => write!(f, "ratchets are equal"),
            PreviousErr::OlderRatchet => write!(f, "self ratchet is older than given ratchet"),
        }
    }
}
