use std::cmp::{self, Ordering};

use crate::Ratchet;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Epoch {
    Small,
    Medium,
    Large,
}

impl Epoch {
    fn inc(&self) -> Self {
        match self {
            Self::Small => Self::Medium,
            Self::Medium => Self::Large,
            Self::Large => Self::Large,
        }
    }

    fn dec(&self) -> Self {
        match self {
            Self::Small => Self::Small,
            Self::Medium => Self::Small,
            Self::Large => Self::Medium,
        }
    }

    fn inc_ratchet(&self, ratchet: &Ratchet) -> Ratchet {
        match self {
            Self::Small => ratchet.next_small_epoch(),
            Self::Medium => ratchet.next_medium_epoch().0,
            Self::Large => ratchet.next_large_epoch().0,
        }
    }
}

/// The ratchet seeker looks for a specific ratchet
/// by efficiently jumping multiple steps ahead similar to an
/// exponential search.
pub struct RatchetSeeker {
    /// Invariant: minimum is always smaller than and never equal to the seeked ratchet
    minimum: Ratchet,
    /// Invariant: current is the next jump_size-ed jump bigger than minimum
    current: Ratchet,
    /// Will increase as long as seeked elements are smaller than the target,
    /// with a maximum of max_jump_size
    /// and decrease when current is bigger than the target.
    jump_size: Epoch,
    /// Will start out at Large and decreases everytime current ends up overshooting.
    max_jump_size: Epoch,
}

impl From<Ratchet> for RatchetSeeker {
    /// Construct a ratchet seeker.
    ///
    /// The given ratchet *must* be smaller than the value seeked for.
    ///
    /// The ratchet seeker's `current()` value will never be the ratchet passed in.
    fn from(ratchet: Ratchet) -> Self {
        let next = ratchet.next_small_epoch();
        Self {
            minimum: ratchet,
            current: next,
            jump_size: Epoch::Small,
            max_jump_size: Epoch::Large,
        }
    }
}

impl RatchetSeeker {
    /// The current ratchet value to evaluate.
    pub fn current(&self) -> &Ratchet {
        &self.current
    }

    /// Do a seeking step by providing it whether `self.current()` is
    /// less than or greater/equal to the step you're looking for.
    ///
    /// Returns a boolean indicating whether to continue.
    pub fn seek(&mut self, current_vs_goal: Ordering) -> bool {
        match current_vs_goal {
            Ordering::Less => {
                // We didn't find the end yet, try bigger jumps.
                self.jump_size = cmp::max(self.jump_size.inc(), self.max_jump_size);
                let increased = self.jump_size.inc_ratchet(&self.current);
                std::mem::swap(&mut self.current, &mut self.minimum);
                self.current = increased;
                true
            }
            Ordering::Equal => {
                // you found it, just stop searching
                false
            }
            Ordering::Greater => {
                if matches!(self.jump_size, Epoch::Small) {
                    // the invariant is that `minimum` is smaller,
                    // but `current` is bigger,
                    // while they both are only a single step apart.
                    // We can't continue searching: there's no in-between ratchets anymore.
                    return false;
                }
                self.jump_size = self.jump_size.dec();
                self.max_jump_size = self.max_jump_size.dec();
                let increased_less = self.jump_size.inc_ratchet(&self.minimum);
                self.current = increased_less;
                true
            }
        }
    }
}
