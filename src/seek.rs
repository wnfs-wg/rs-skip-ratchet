use std::cmp::Ordering;

use crate::Ratchet;

#[derive(Debug, Clone, Copy)]
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

pub struct RatchetSeeker {
    /// Invariant: minimum is always smaller than the seeked value (and not equal to it)
    minimum: Ratchet,
    /// Invariant: current is the next jump_size-ed jump bigger than minimum
    current: Ratchet,
    /// Will increase as long as seeked elements are smaller than the target,
    /// and decrease when current is bigger than the target
    jump_size: Epoch,
}

impl From<Ratchet> for RatchetSeeker {
    fn from(ratchet: Ratchet) -> Self {
        let next = ratchet.next_small_epoch();
        Self {
            minimum: ratchet,
            current: next,
            jump_size: Epoch::Small,
        }
    }
}

impl RatchetSeeker {
    pub fn current(&self) -> &Ratchet {
        &self.current
    }

    pub fn seek(&mut self, current_vs_goal: Ordering) -> bool {
        match current_vs_goal {
            Ordering::Less => {
                self.jump_size = self.jump_size.inc();
                let increased = self.jump_size.inc_ratchet(&self.current);
                std::mem::swap(&mut self.current, &mut self.minimum);
                self.current = increased;
                true
            }
            Ordering::Equal => {
                // uh, you found it. Do nothing
                // TODO: Consider using another type that only has Less and Greater
                false
            }
            Ordering::Greater => {
                if matches!(self.jump_size, Epoch::Small) {
                    return false;
                }
                self.jump_size = self.jump_size.dec();
                let increased_less = self.jump_size.inc_ratchet(&self.minimum);
                self.current = increased_less;
                true
            }
        }
    }
}
