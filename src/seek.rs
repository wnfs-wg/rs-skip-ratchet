use std::cmp::{self, Ordering};

use crate::Ratchet;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
/// The different possible ratchet jumps
pub enum JumpSize {
    /// A jump size that doesn't change the ratchet at all
    Zero,
    /// Stepping the ratchet forward exactly once
    Small,
    /// Jumping to the next medium epoch
    Medium,
    /// Jumping to the next large epoch
    Large,
}

impl JumpSize {
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

/// The ratchet seeker looks for a target ratchet
/// by efficiently exploring the ratchet space and
/// figuring out whether it's smaller or greater than
/// the target until it finds the target.
pub struct RatchetSeeker {
    /// Invariant: minimum is always smaller than or equal to the seeked ratchet
    minimum: Ratchet,
    /// Invariant: current is the next jump_size-ed jump bigger than minimum
    current: Ratchet,
    /// Will increase as long as seeked elements are smaller than the target,
    /// with a maximum of max_jump_size
    /// and decrease when current is bigger than the target.
    jump_size: JumpSize,
    /// Will start out at Large and decreases everytime current ends up overshooting.
    max_jump_size: JumpSize,
}

impl RatchetSeeker {
    /// Start a new ratchet search.
    ///
    /// The assumption is that given ratchet is less or equal to the target
    /// you're looking for.
    ///
    /// Then it proceeds doing an exponential search forwards looking for a
    /// ratchet that is bigger than the target.
    /// Then it does something similar to a binary search trying to find
    /// the target between the ratchet that was bigger than the target
    /// and the last known ratchet to be smaller than the target.
    ///
    /// This search is kicked off with an initial jump of `initial_jump_size`.
    pub fn new(ratchet: Ratchet, initial_jump_size: JumpSize) -> Self {
        Self {
            current: initial_jump_size.inc_ratchet(&ratchet),
            minimum: ratchet,
            jump_size: initial_jump_size,
            max_jump_size: JumpSize::Large,
        }
    }

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
                if matches!(self.jump_size, JumpSize::Zero) {
                    // We can't jump "less" than zero from `minimum`, so we're there.
                    return false;
                }
                if matches!(self.jump_size, JumpSize::Small) {
                    // If jump_size was small, then `current` is `minimum + 1`.
                    // The smallest we can do is `minimum`, so stop after that.
                    self.current = self.minimum.clone();
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
