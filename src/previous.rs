//! Implements an iterator which gives intermediate states between two ratchets
//! yielding states from recent to old.
use crate::{constants::LARGE_EPOCH_LENGTH, PreviousErr, Ratchet};

/// An iterator over `Ratchet`'s between two `Ratchet`'s.
///
/// # Examples
///
/// ```
/// use skip_ratchet::Ratchet;
///
/// let mut old_ratchet = Ratchet::from_rng(&mut rand::thread_rng());
/// old_ratchet.inc_by(10);
///
/// let mut recent_ratchet = old_ratchet.clone();
/// recent_ratchet.inc_by(10);
///
/// for r in recent_ratchet.previous(&old_ratchet, 10).unwrap() {
///   println!("{:?}", r);
/// }
/// ```
#[derive(Clone, Debug)]
pub struct PreviousIterator {
    pub(crate) large_skips: Vec<Ratchet>,
    pub(crate) medium_skips: Vec<Ratchet>,
    pub(crate) small_skips: Vec<Ratchet>,
    pub(crate) recent: Ratchet,
}

impl PreviousIterator {
    /// If possible, this constructs an iterator for enumerating all ratchets
    /// from most recent to oldest between `old` and `recent`.
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::{Ratchet, PreviousIterator};
    ///
    /// let old_ratchet = Ratchet::from_rng(&mut rand::thread_rng());
    ///
    /// let mut new_ratchet = old_ratchet.clone();
    /// new_ratchet.inc_by(100_000);
    ///
    /// let mut new_ratchet_previous = old_ratchet.clone();
    /// new_ratchet_previous.inc_by(99_999);
    ///
    /// let mut iterator = PreviousIterator::new(&old_ratchet, &new_ratchet, 1_000_000_000).unwrap();
    ///
    /// assert_eq!(iterator.next(), Some(new_ratchet_previous));
    /// ```
    pub(crate) fn new(
        old: &Ratchet,
        recent: &Ratchet,
        discrepancy_budget: usize,
    ) -> Result<Self, PreviousErr> {
        let mut iter = Self {
            large_skips: vec![old.clone()],
            medium_skips: vec![],
            small_skips: vec![],
            recent: recent.clone(),
        };
        let mut old_ratchet_large = old.clone();

        // The budget is rounded up to the nearest large epoch. We only care about the large epochs.
        let rounded_budget = (discrepancy_budget / LARGE_EPOCH_LENGTH
            + usize::from(discrepancy_budget % LARGE_EPOCH_LENGTH != 0))
            * LARGE_EPOCH_LENGTH;
        let mut total_jumps = LARGE_EPOCH_LENGTH;

        while old_ratchet_large.large != recent.large {
            let jump_count = old_ratchet_large.next_large_epoch();
            total_jumps += jump_count;
            if total_jumps > rounded_budget {
                return Err(PreviousErr::BudgetExceeded);
            }
            iter.large_skips.push(old_ratchet_large.clone());
        }

        Ok(iter)
    }

    /// Returns the exact amount of ratchets between the old and recent ratchet.
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::{Ratchet, PreviousIterator};
    ///
    /// let old_ratchet = Ratchet::from_rng(&mut rand::thread_rng());
    /// let mut new_ratchet = old_ratchet.clone();
    /// new_ratchet.inc_by(100_000);
    ///
    /// let iterator = PreviousIterator::new(&old_ratchet, &new_ratchet, 1_000_000_000).unwrap();
    ///
    /// assert_eq!(iterator.step_count(), 100_000);
    /// ```
    pub fn step_count(&self) -> usize {
        let mut count = 0;

        // The oldest ratchet in this iterator with the same large epoch as recent:
        let (oldest_in_recent_epoch, from_large) = match self.large_skips.last() {
            // the last large skip may or may not have the same large epoch
            Some(last_large) if last_large.large == self.recent.large => (last_large, true),
            // if not, we take the first in any of the other skip lists
            _ => (
                self.medium_skips
                    .first()
                    .or_else(|| self.small_skips.first())
                    .unwrap_or(&self.recent),
                false,
            ),
        };

        // It's safe to compare combined counters, since they both are in the same large epoch
        count += self.recent.combined_counter() - oldest_in_recent_epoch.combined_counter();

        // Other than that we need to add all large skips
        if let Some(first_large) = self.large_skips.first() {
            count += (self.large_skips.len() - 1) * LARGE_EPOCH_LENGTH;
            // If we didn't take the large from the large epoch, we need to add it back in here
            if !from_large {
                count += LARGE_EPOCH_LENGTH;
            }
            count += oldest_in_recent_epoch.combined_counter() - first_large.combined_counter();
        }

        count
    }
}

impl Iterator for PreviousIterator {
    type Item = Ratchet;

    fn next(&mut self) -> Option<Self::Item> {
        while !(self.large_skips.is_empty()
            && self.medium_skips.is_empty()
            && self.small_skips.is_empty())
        {
            if self.medium_skips.is_empty() && self.small_skips.is_empty() {
                let old_ratchet_large = self.large_skips.pop().unwrap();
                self.medium_skips.push(old_ratchet_large.clone());
                let mut old_ratchet_medium = old_ratchet_large;

                while !(old_ratchet_medium.medium == self.recent.medium
                    && old_ratchet_medium.large == self.recent.large)
                {
                    old_ratchet_medium.next_medium_epoch();
                    self.medium_skips.push(old_ratchet_medium.clone());
                }

                continue;
            } else if self.small_skips.is_empty() {
                let old_ratchet_medium = self.medium_skips.pop().unwrap();
                let mut old_ratchet_small = old_ratchet_medium;

                while !(old_ratchet_small.small == self.recent.small
                    && old_ratchet_small.medium == self.recent.medium)
                {
                    self.small_skips.push(old_ratchet_small.clone());
                    old_ratchet_small.inc();
                }

                continue;
            }

            let old_ratchet_small = self.small_skips.pop().unwrap();
            self.recent = old_ratchet_small.clone();
            return Some(old_ratchet_small);
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let count = self.step_count();
        (count, Some(count))
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        constants::LARGE_EPOCH_LENGTH,
        test_utils::{assert_ratchet_equal, salt, seed},
        PreviousErr, PreviousIterator, Ratchet,
    };
    use std::vec;

    #[test]
    fn test_step_count_regression() {
        let old_ratchet = Ratchet::from_rng(&mut rand::thread_rng());
        let mut new_ratchet = old_ratchet.clone();
        new_ratchet.inc_by(LARGE_EPOCH_LENGTH + 10);

        let mut iterator =
            PreviousIterator::new(&old_ratchet, &new_ratchet, 1_000_000_000).unwrap();

        for _ in 0..LARGE_EPOCH_LENGTH {
            assert!(iterator.next().is_some());
        }

        assert_ne!(iterator.step_count(), 0);

        for _ in 0..10 {
            assert!(iterator.next().is_some());
        }

        assert!(iterator.next().is_none());
    }

    #[test]
    fn test_ratchet_previous_equal_error() {
        let old = Ratchet::zero(salt(), &seed());
        match old.previous(&old, 10) {
            Ok(_) => panic!("expected PreviousErr::EqualRatchets, got an iterator instead"),
            Err(e) => match e {
                PreviousErr::EqualRatchets => (),
                _ => panic!("expected PreviousErr::EqualRatchets, got {e:?}"),
            },
        }
    }

    #[test]
    fn test_ratchet_previous_older_error() {
        let old = Ratchet::zero(salt(), &seed());
        let mut recent = old.clone();
        recent.inc();
        match old.previous(&recent, 10) {
            Ok(_) => panic!("expected PreviousErr::EqualRatchets, got an iterator instead"),
            Err(e) => match e {
                PreviousErr::OlderRatchet => (),
                _ => panic!("expected PreviousErr::EqualRatchets, got {e:?}"),
            },
        }
    }

    #[test]
    fn test_ratchet_previous_increments() {
        let discrepancy_budget = 1_000_000;
        let old = Ratchet::zero(salt(), &seed());
        let increments = [1, 260, 65_600, 131_100];

        for inc in increments.into_iter() {
            let mut expected_ratchets = vec![old.clone()];
            let mut ratchet = old.clone();
            for _ in 1..inc {
                ratchet.inc();
                expected_ratchets.push(ratchet.clone());
            }

            let mut recent_ratchet = old.clone();
            recent_ratchet.inc_by(inc);
            let got_ratchets = match recent_ratchet.previous(&old, discrepancy_budget) {
                Ok(iter) => iter.collect::<Vec<_>>(),
                Err(e) => panic!("error for previous with inc {inc}: {e:?}"),
            };

            assert_eq!(expected_ratchets.len(), got_ratchets.len());
            for (expected, got) in expected_ratchets.iter().rev().zip(got_ratchets.iter()) {
                assert_ratchet_equal(expected, got);
            }
        }
    }

    #[test]
    fn test_ratchet_previous_budget() {
        let old_ratchet = Ratchet::zero(salt(), &seed());
        let increments = [(65_600, 65_500), (131_100, 131_000)];

        for (inc, budget) in increments.into_iter() {
            let mut recent_ratchet = old_ratchet.clone();
            recent_ratchet.inc_by(inc);
            let result = recent_ratchet.previous(&old_ratchet, budget);
            assert_eq!(result.unwrap_err(), PreviousErr::BudgetExceeded);
        }

        let increments = [(65_535, 10), (65_600, 65_600)];

        for (inc, budget) in increments.into_iter() {
            let mut recent_ratchet = old_ratchet.clone();
            recent_ratchet.inc_by(inc);
            let result = recent_ratchet.previous(&old_ratchet, budget);
            assert!(result.is_ok());
        }
    }
}

#[cfg(test)]
mod proptests {
    use crate::{
        constants::LARGE_EPOCH_LENGTH, test_utils::any_ratchet, PreviousIterator, Ratchet,
    };
    use proptest::prelude::*;
    use test_strategy::proptest;

    #[proptest]
    fn prop_ratchet_step_count_is_inc_by(
        #[strategy(any_ratchet())] initial: Ratchet,
        #[strategy(0..10_000_000usize)] jump: usize,
    ) {
        let goal = {
            let mut goal = initial.clone();
            goal.inc_by(jump);
            goal
        };

        let iterator = PreviousIterator::new(&initial, &goal, 1_000_000_000).unwrap();

        prop_assert_eq!(iterator.step_count(), jump);
    }

    #[proptest]
    fn prop_ratchet_step_count_is_inc_by_minus_steps(
        #[strategy(any_ratchet())] initial: Ratchet,
        #[strategy(0..100usize)] previous_steps: usize,
        #[strategy(0..100_000usize)] additional_jumps: usize,
    ) {
        let jumps = previous_steps + additional_jumps;
        let goal = {
            let mut goal = initial.clone();
            goal.inc_by(jumps);
            goal
        };

        let mut iterator = PreviousIterator::new(&initial, &goal, 1_000_000_000).unwrap();

        for _ in 0..previous_steps {
            assert!(iterator.next().is_some());
        }

        prop_assert_eq!(iterator.step_count(), jumps - previous_steps);
    }

    #[proptest]
    fn prop_ratchet_previous_of_equal_is_none(
        #[strategy(any_ratchet())] mut initial: Ratchet,
        #[strategy(1..LARGE_EPOCH_LENGTH)] jump: usize,
    ) {
        initial.inc_by(jump);

        let mut iterator = PreviousIterator::new(&initial.clone(), &initial, 1_000).unwrap();

        prop_assert_eq!(iterator.next(), None);
    }

    #[proptest]
    fn prop_ratchet_previous_is_inc_reverse(
        #[strategy(any_ratchet())] initial: Ratchet,
        #[strategy(1..10_000usize)] jump: usize,
    ) {
        let goal = {
            let mut goal = initial.clone();
            goal.inc_by(jump);
            goal
        };

        let previous_iterator = PreviousIterator::new(&initial, &goal, 1_000_000_000).unwrap();

        let forward_iterator = initial.clone().take(jump - 1);

        let mut forward_collected_reversed = forward_iterator.collect::<Vec<Ratchet>>();
        forward_collected_reversed.reverse();
        forward_collected_reversed.push(initial);

        prop_assert_eq!(
            previous_iterator.collect::<Vec<Ratchet>>(),
            forward_collected_reversed
        );
    }
}
