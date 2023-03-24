use crate::Ratchet;
use std::cmp::{self, Ordering};

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
        let mut cloned = ratchet.clone();
        match self {
            Self::Zero => {}
            Self::Small => cloned.inc(),
            Self::Medium => {
                cloned.next_medium_epoch();
            }
            Self::Large => {
                cloned.next_large_epoch();
            }
        };
        cloned
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

#[cfg(test)]
mod proptests {
    use crate::{
        prop_assert_ratchet_eq,
        seek::JumpSize,
        test_utils::{any_jump_size, any_ratchet},
        Ratchet, RatchetSeeker,
    };
    use proptest::prelude::*;
    use test_strategy::proptest;

    #[proptest]
    fn prop_ratchet_seek_finds(
        #[strategy(any_ratchet())] initial: Ratchet,
        #[strategy(0..10_000_000usize)] jump: usize,
        #[strategy(any_jump_size())] initial_jump_size: JumpSize,
    ) {
        let goal = {
            let mut goal = initial.clone();
            goal.inc_by(jump);
            goal
        };

        let mut seeker = RatchetSeeker::new(initial, initial_jump_size);
        let mut iterations = 0;
        loop {
            let ord = seeker.current().compare(&goal, jump).unwrap().cmp(&0);
            if !seeker.step(ord) {
                break;
            }
            iterations += 1;
            // Seeking should never take much more than the ratchet is from it's goal.
            if iterations > jump {
                panic!("Infinite loop detected.")
            }
        }
        prop_assert_ratchet_eq!(&goal, seeker.current());
    }

    #[proptest]
    fn prop_ratchet_seek_finds_zero(
        #[strategy(any_ratchet())] ratchet: Ratchet,
        #[strategy(any_jump_size())] initial_jump_size: JumpSize,
    ) {
        let mut seeker = RatchetSeeker::new(ratchet.clone(), initial_jump_size);

        loop {
            if !seeker.step(std::cmp::Ordering::Greater) {
                break;
            }
        }

        prop_assert_ratchet_eq!(&ratchet, seeker.current());
    }

    #[proptest]
    fn prop_ratchet_seek_finds_only_greater_and_less(
        #[strategy(any_ratchet())] initial: Ratchet,
        #[strategy(0..10_000_000usize)] jump: usize,
        #[strategy(any_jump_size())] initial_jump_size: JumpSize,
    ) {
        let goal = {
            let mut goal = initial.clone();
            goal.inc_by(jump);
            goal
        };

        let mut seeker = RatchetSeeker::new(initial, initial_jump_size);
        let mut iterations = 0;
        loop {
            // should give the same result
            let ord = match seeker.current().compare(&goal, jump).unwrap().cmp(&0) {
                std::cmp::Ordering::Equal => std::cmp::Ordering::Less,
                o => o,
            };
            if !seeker.step(ord) {
                break;
            }
            iterations += 1;
            // Seeking should never take much more than the ratchet is from it's goal.
            if iterations > jump {
                panic!("Infinite loop detected.")
            }
        }
        prop_assert_ratchet_eq!(&goal, seeker.current());
    }
}
