use std::{
    error::Error,
    fmt::{self, Display, Formatter},
};

/// This type is used to indicate errors that occur interpreting a `Ratchet`
#[derive(Debug)]
pub enum RatchetErr {
    UnknownRelation,
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
            RatchetErr::UnknownRelation => write!(f, "cannot relate ratchets"),
        }
    }
}

impl Error for RatchetErr {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
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
