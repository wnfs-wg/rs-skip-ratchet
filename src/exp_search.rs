use std::cmp::{self, Ordering};

use crate::Ratchet;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Epoch {
    Zero,
    Small,
    Medium,
    Large,
}

impl Epoch {
    fn inc(&self) -> Self {
        match self {
            Self::Zero => Self::Small,
            Self::Small => Self::Medium,
            Self::Medium => Self::Large,
            Self::Large => Self::Large,
        }
    }

    fn dec(&self) -> Self {
        match self {
            Self::Zero => Self::Zero,
            Self::Small => Self::Zero,
            Self::Medium => Self::Small,
            Self::Large => Self::Medium,
        }
    }

    fn inc_ratchet(&self, ratchet: &Ratchet) -> Ratchet {
        match self {
            Self::Zero => ratchet.clone(),
            Self::Small => ratchet.next_small_epoch(),
            Self::Medium => ratchet.next_medium_epoch().0,
            Self::Large => ratchet.next_large_epoch().0,
        }
    }
}

/// The ratchet exponential searcher looks for a specific ratchet
/// by efficiently jumping multiple steps ahead.
pub struct RatchetExpSearcher {
    /// Invariant: minimum is always smaller than or equal to the seeked ratchet
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

impl From<Ratchet> for RatchetExpSearcher {
    /// Construct a ratchet seeker.
    fn from(ratchet: Ratchet) -> Self {
        Self {
            minimum: ratchet.clone(),
            current: ratchet,
            jump_size: Epoch::Zero,
            max_jump_size: Epoch::Large,
        }
    }
}

impl RatchetExpSearcher {
    /// The current ratchet value to evaluate.
    pub fn current(&self) -> &Ratchet {
        &self.current
    }

    /// Do a search step by providing it whether `self.current()` is
    /// less than or greater/equal to the step you're looking for.
    ///
    /// Returns a boolean indicating whether to continue.
    pub fn step(&mut self, current_vs_goal: Ordering) -> bool {
        match current_vs_goal {
            Ordering::Less => {
                // We didn't find the end yet, try bigger jumps.
                self.jump_size = cmp::max(self.jump_size.inc(), self.max_jump_size);
                let increased = self.jump_size.inc_ratchet(&self.current);
                // self.minimum = self.current;
                // self.current = increased;
                std::mem::swap(&mut self.current, &mut self.minimum);
                self.current = increased;
                true
            }
            Ordering::Equal => {
                // you found it, just stop searching
                false
            }
            Ordering::Greater => {
                if matches!(self.jump_size, Epoch::Zero) {
                    // We can't jump "less" than zero from `minimum`, so we're there.
                    return false;
                }
                self.jump_size = self.jump_size.dec();
                self.max_jump_size = self.max_jump_size.dec();
                self.current = self.jump_size.inc_ratchet(&self.minimum);
                true
            }
        }
    }
}
