use crate::{
    constants::{LARGE_EPOCH_LENGTH, MEDIUM_EPOCH_LENGTH},
    hash::Hash,
    salt::Salt,
    PreviousErr, RatchetErr,
};
use rand::{Rng, RngCore};
use sha3::{Digest, Sha3_256};
use std::fmt::{self, Display, Formatter};

/// A (Skip) `Ratchet` is a data structure for deriving keys that maintain backward secrecy.
/// Unlike hash chains, this data structure is capable of efficiently making large leaps in hash count.
///
/// The implementation is based on the [Skip Ratchet paper][1].
///
/// # Examples
///
/// ```
/// use skip_ratchet::Ratchet;
///
/// let ratchet = Ratchet::new(&mut rand::thread_rng());
/// let key = ratchet.derive_key("awesome.ly key derivation");
/// ```
///
/// [1]: https://github.com/fission-suite/skip-ratchet-paper/blob/main/spiral-ratchet.pdf
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
#[derive(Clone, PartialEq, Debug, Eq)]
pub struct Ratchet {
    pub(crate) salt: Salt,
    pub(crate) large: Hash,
    pub(crate) medium: Hash,
    pub(crate) small: Hash,
    pub(crate) medium_counter: u8,
    pub(crate) small_counter: u8,
}

/// An iterator over `Ratchet`'s between two `Ratchet`'s.
///
/// # Examples
///
/// ```
/// use skip_ratchet::Ratchet;
///
/// let mut old_ratchet = Ratchet::new(&mut rand::thread_rng());
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

impl Ratchet {
    /// Creates a new ratchet with a randomly generated seed.
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::Ratchet;
    ///
    /// let ratchet = Ratchet::new(&mut rand::thread_rng());
    /// ```
    pub fn new(rng: &mut impl RngCore) -> Self {
        // 32 bytes for the seed, plus two extra bytes to randomize small & medium starts
        let seed = rng.gen::<[u8; 32]>();
        let inc_small = rng.gen::<u8>();
        let inc_med = rng.gen::<u8>();

        Self::from_seed(&seed, inc_small, inc_med)
    }

    /// Creates a new ratchet from a seed with zero counters.
    pub fn zero(seed: &[u8; 32]) -> Self {
        Self::from_seed(&seed, 0, 0)
    }

    /// Creates a new ratchet with given seed with given counters.
    pub fn from_seed(seed: &[u8; 32], inc_small: u8, inc_med: u8) -> Self {
        let salt = Salt::from(Hash::from("Skip Ratchet Slt", seed));
        let large = Hash::from("Skip Ratchet Lrg", seed);
        let medium = Hash::from("Skip Ratchet Med", seed);
        let small = Hash::from("Skip Ratchet Sml", seed);

        Ratchet {
            salt,
            large,
            medium: Hash::from_chain(&[], medium, inc_med.into()),
            small: Hash::from_chain(&[], small, inc_small.into()),
            medium_counter: inc_med,
            small_counter: inc_small,
        }
    }

    /// Derives a new key from the ratchet.
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::Ratchet;
    ///
    /// let ratchet = Ratchet::new(&mut rand::thread_rng());
    /// let key = ratchet.derive_key("awesome.ly temporal key derivation");
    /// ```
    pub fn derive_key(&self, purpose: impl AsRef<[u8]>) -> [u8; 32] {
        let mut hasher = Sha3_256::new();
        hasher.update(purpose);
        hasher.update(self.large);
        hasher.update(self.medium);
        hasher.update(self.small);
        hasher.finalize().into()
    }

    /// Moves the ratchet forward by one step.
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::Ratchet;
    ///
    /// let mut ratchet = Ratchet::new(&mut rand::thread_rng());
    /// ratchet.inc();
    /// ```
    pub fn inc(&mut self) {
        if self.small_counter == 255 {
            let (r, j) = self.next_medium_epoch();
            debug_assert_eq!(j, 1);
            *self = r;
            return;
        }

        self.small = Hash::from(&[], self.small);
        self.small_counter += 1;
    }

    /// Moves the ratchet forward by `n` steps.
    ///
    /// # Examples
    /// ```
    /// use skip_ratchet::Ratchet;
    ///
    /// let mut ratchet = Ratchet::new(&mut rand::thread_rng());
    /// ratchet.inc_by(3);
    ///
    /// println!("{:?}", ratchet);
    /// ```
    pub fn inc_by(&mut self, n: usize) {
        let jumped = inc_by(self, n);
        *self = jumped;
    }

    pub fn compare(&self, other: &Ratchet, max_steps: usize) -> Result<isize, RatchetErr> {
        if self.salt != other.salt {
            return Err(RatchetErr::UnknownRelation);
        }

        let self_counter = self.combined_counter() as isize;
        let other_counter = other.combined_counter() as isize;
        if self.large == other.large {
            if self_counter == other_counter {
                return Ok(0);
            }
            return Ok(self_counter - other_counter);
        }

        // Here, the large digit always differs, so one of the ratchets will always be bigger, they cannot be equal.
        // We can find out which one is bigger by hashing both at the same time and looking at  when one created the same digit as the other,
        // essentially racing the large digit's recursive hashes.
        let mut self_large = self.large;
        let mut other_large = other.large;
        let mut steps = 0;
        let mut steps_left = max_steps;

        // Since the two ratches might just be generated from a totally different setup, we can never _really_ know which one is the bigger one.
        // They might be unrelated.
        while steps_left > 0 {
            self_large = Hash::from(&[], self_large);
            other_large = Hash::from(&[], other_large);
            steps += 1;

            if other_large == self.large {
                // Other_large_counter * LARGE_EPOCH_LENGTH is the count of increments applied via advancing the large digit continually.
                // -other_large_counter is the difference between 'other' and its next large epoch.
                // self_counter is just what's self to add because of the count at which 'self' is
                return Ok((steps * LARGE_EPOCH_LENGTH as isize) - (other_counter + self_counter));
            }

            if self_large == other.large {
                // In this case, we compute the same difference, but return the negative to indicate that 'other' is bigger that
                // 'self' rather than the other way around.
                return Ok(-(steps * LARGE_EPOCH_LENGTH as isize) - (self_counter + other_counter));
            }
            steps_left -= 1;
        }
        Err(RatchetErr::UnknownRelation)
    }

    /// This function is probabilistic. Returns true if self is known to be after b, and false if large
    /// counters are inequal (meaning r is before, equal, unrelated, or after)
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::Ratchet;
    ///
    /// let mut ratchet1 = Ratchet::new(&mut rand::thread_rng());
    /// ratchet1.inc();
    ///
    /// let mut ratchet2 = ratchet1.clone();
    /// ratchet2.inc();
    ///
    /// assert!(ratchet2.known_after(&ratchet1));
    /// ```
    pub fn known_after(&self, other: &Ratchet) -> bool {
        self.large == other.large
            && self.medium_counter >= other.medium_counter
            && self.small_counter > other.small_counter
    }

    /// Gets an iterator over the ratchet's previous hashes.
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::Ratchet;
    ///
    /// let mut old_ratchet = Ratchet::new(&mut rand::thread_rng());
    /// old_ratchet.inc_by(10);
    ///
    /// let mut recent_ratchet = old_ratchet.clone();
    /// recent_ratchet.inc_by(10);
    ///
    /// for r in recent_ratchet.previous(&old_ratchet, 10).unwrap() {
    ///   println!("{:?}", r);
    /// }
    /// ```
    pub fn previous(
        &self,
        old: &Ratchet,
        discrepancy_budget: usize,
    ) -> Result<PreviousIterator, PreviousErr> {
        if self == old {
            return Err(PreviousErr::EqualRatchets);
        } else if old.known_after(self) {
            return Err(PreviousErr::OlderRatchet);
        }

        PreviousIterator::new(old, self, discrepancy_budget)
    }

    /// Get the entire hash count of the ratchet.
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::Ratchet;
    ///
    /// let mut ratchet = Ratchet::new(&mut rand::thread_rng());
    /// ratchet.inc_by(10);
    ///
    /// println!("{:?}", ratchet.combined_counter());
    /// ```
    pub fn combined_counter(&self) -> usize {
        (MEDIUM_EPOCH_LENGTH * self.medium_counter as usize) + self.small_counter as usize
    }

    /// Returns the next large epoch of the ratchet.
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::Ratchet;
    ///
    /// let mut ratchet = Ratchet::new(&mut rand::thread_rng());
    /// let (r, s) = ratchet.next_large_epoch();
    /// ```
    pub fn next_large_epoch(&self) -> (Ratchet, usize) {
        let jump_count = LARGE_EPOCH_LENGTH - self.combined_counter();

        let large = Hash::from(&[], self.large);
        let medium = Hash::from(self.salt, self.large);
        let small = Hash::from(self.salt, medium);

        let jumped = Ratchet {
            salt: self.salt,
            large,
            medium,
            medium_counter: 0,
            small,
            small_counter: 0,
        };

        (jumped, jump_count)
    }

    /// Returns the next medium epoch of the ratchet.
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::Ratchet;
    ///
    /// let mut ratchet = Ratchet::new(&mut rand::thread_rng());
    /// let (r, s) = ratchet.next_medium_epoch();
    /// ```
    pub fn next_medium_epoch(&self) -> (Ratchet, usize) {
        if self.medium_counter == 255 {
            return self.next_large_epoch();
        }

        let medium = Hash::from(&[], self.medium);
        let small = Hash::from(self.salt, medium);

        let jumped = Ratchet {
            salt: self.salt,
            large: self.large,
            medium,
            medium_counter: self.medium_counter + 1,
            small,
            small_counter: 0,
        };

        let jump_count = jumped.combined_counter() - self.combined_counter();
        (jumped, jump_count)
    }

    /// Returns the next small epoch of the ratchet.
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::Ratchet;
    ///
    /// let mut ratchet = Ratchet::new(&mut rand::thread_rng());
    /// let r = ratchet.next_small_epoch();
    /// ```
    pub fn next_small_epoch(&self) -> Ratchet {
        let mut ratchet = self.clone();
        ratchet.inc();
        ratchet
    }
}

impl PreviousIterator {
    /// If possible, this constructs an iterator for enumerating all ratchets
    /// from most recent to oldest between `old` and `recent`.
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::{Ratchet, ratchet::PreviousIterator};
    ///
    /// let old_ratchet = Ratchet::new(&mut rand::thread_rng());
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
    pub fn new(
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
            let (ratchet, jump_count) = old_ratchet_large.next_large_epoch();
            old_ratchet_large = ratchet;
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
    /// use skip_ratchet::{Ratchet, ratchet::PreviousIterator};
    ///
    /// let old_ratchet = Ratchet::new(&mut rand::thread_rng());
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
                    (old_ratchet_medium, _) = old_ratchet_medium.next_medium_epoch();
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
                    old_ratchet_small = old_ratchet_small.next_small_epoch();
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

impl Iterator for Ratchet {
    type Item = Ratchet;

    fn next(&mut self) -> Option<Self::Item> {
        self.inc();
        Some(self.clone())
    }
}

impl Display for Ratchet {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("Ratchet")
            .field("small", &self.small.as_slice()[0..3].to_vec())
            .field("medium", &self.medium.as_slice()[0..3].to_vec())
            .field("large", &self.large.as_slice()[0..3].to_vec())
            .field("small_counter", &self.small_counter)
            .field("medium_counter", &self.medium_counter)
            .finish()
    }
}

pub(crate) fn inc_by(ratchet: &Ratchet, n: usize) -> Ratchet {
    if n == 0 {
        return ratchet.clone();
    } else if n >= LARGE_EPOCH_LENGTH - ratchet.combined_counter() {
        // `n` is larger than at least one large epoch jump
        let (jumped, jump_count) = ratchet.next_large_epoch();
        return inc_by(&jumped, n - jump_count);
    } else if n >= MEDIUM_EPOCH_LENGTH - ratchet.small_counter as usize {
        // `n` is larger than at least one medium epoch jump
        let (jumped, jump_count) = ratchet.next_medium_epoch();
        return inc_by(&jumped, n - jump_count);
    }

    let mut ratchet = ratchet.clone();

    ratchet.small = Hash::from_chain(&[], ratchet.small, n);
    ratchet.small_counter += n as u8;

    ratchet
}
