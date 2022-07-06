use std::fmt::{self, Display, Formatter};

use crate::{
    constants::{LARGE_EPOCH_LENGTH, MEDIUM_EPOCH_LENGTH, RATCHET_SIGNIFIER},
    hash::Hash,
    PreviousErr, RatchetErr,
};
use rand::Rng;

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
/// let ratchet = Ratchet::new();
/// let key = ratchet.key();
/// ```
///
/// [1]: https://github.com/fission-suite/skip-ratchet-paper/blob/main/spiral-ratchet.pdf
#[derive(Clone, PartialEq, Debug, Eq)]
pub struct Ratchet {
    pub(crate) large: Hash,
    pub(crate) medium: Hash,
    pub(crate) small: Hash,
    pub(crate) medium_counter: u8,
    pub(crate) small_counter: u8,
}

// TODO: this won't work for histories that span the small ratchet.
/// An iterator over `Ratchet`'s between two `Ratchet`'s.
///
/// # Examples
///
/// ```
/// use skip_ratchet::Ratchet;
///
/// let mut old_ratchet = Ratchet::new();
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
    large_skips: Vec<Ratchet>,
    medium_skips: Vec<Ratchet>,
    small_skips: Vec<Ratchet>,
    recent: Ratchet,
}

impl Ratchet {
    /// Creates a new ratchet with a randomly generated seed.
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::Ratchet;
    ///
    /// let ratchet = Ratchet::new();
    /// ```
    pub fn new() -> Self {
        // 32 bytes for the seed, plus two extra bytes to randomize small & medium starts
        let seed = Hash::from_raw(rand::thread_rng().gen::<[u8; 32]>());
        let medium = Hash::from(&!seed);
        let small = Hash::from(&!medium);

        let inc_med = rand::thread_rng().gen::<u8>();
        let inc_small = rand::thread_rng().gen::<u8>();

        Ratchet {
            large: Hash::from(&seed),
            medium: Hash::from_chain(&medium, inc_med.into()),
            small: Hash::from_chain(&small, inc_small.into()),
            medium_counter: inc_med,
            small_counter: inc_small,
        }
    }

    /// Creates a new ratchet from a seed with zero counters.
    pub(crate) fn zero(seed: [u8; 32]) -> Self {
        let seed = Hash::from_raw(seed);

        let medium = Hash::from(&!seed);
        let small = Hash::from(&!medium);

        Ratchet {
            large: Hash::from(&seed),
            medium,
            small,
            medium_counter: 0,
            small_counter: 0,
        }
    }

    /// Derives a new key from the ratchet.
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::Ratchet;
    ///
    /// let ratchet = Ratchet::new();
    /// let key = ratchet.key();
    /// ```
    pub fn key(&self) -> Hash {
        Hash::from(&(self.large ^ self.medium ^ self.small))
    }

    /// Moves the ratchet forward by one step.
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::Ratchet;
    ///
    /// let mut ratchet = Ratchet::new();
    /// ratchet.inc();
    /// ```
    pub fn inc(&mut self) {
        if self.small_counter == 255 {
            let (r, _) = self.next_medium_epoch();
            *self = r;
            return;
        }

        self.small = Hash::from(&self.small);
        self.small_counter += 1;
    }

    /// Moves the ratchet forward by `n` steps.
    ///
    /// # Examples
    /// ```
    /// use skip_ratchet::Ratchet;
    ///
    /// let mut ratchet = Ratchet::new();
    /// ratchet.inc_by(3);
    ///
    /// println!("{:?}", String::from(&ratchet));
    /// ```
    pub fn inc_by(&mut self, n: usize) {
        let (jumped, _) = inc_by(self, n);
        *self = jumped;
    }

    pub fn compare(&self, other: &Ratchet, max_steps: usize) -> Result<isize, RatchetErr> {
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
            self_large = Hash::from(&self_large);
            other_large = Hash::from(&other_large);
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
    /// let mut ratchet1 = Ratchet::new();
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
    /// let mut old_ratchet = Ratchet::new();
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
    /// let mut ratchet = Ratchet::new();
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
    /// let mut ratchet = Ratchet::new();
    /// let (r, s) = ratchet.next_large_epoch();
    /// ```
    pub fn next_large_epoch(&self) -> (Ratchet, usize) {
        (
            Ratchet::zero(self.large.as_slice().clone()),
            LARGE_EPOCH_LENGTH - self.combined_counter(),
        )
    }

    /// Returns the next medium epoch of the ratchet.
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::Ratchet;
    ///
    /// let mut ratchet = Ratchet::new();
    /// let (r, s) = ratchet.next_medium_epoch();
    /// ```
    pub fn next_medium_epoch(&self) -> (Ratchet, usize) {
        if self.medium_counter == 255 {
            return self.next_large_epoch();
        }

        let jumped = Ratchet {
            large: self.large,
            medium: Hash::from(&self.medium),
            medium_counter: self.medium_counter + 1,
            small: Hash::from(&!self.medium),
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
    /// let mut ratchet = Ratchet::new();
    /// let r = ratchet.next_small_epoch();
    /// ```
    pub fn next_small_epoch(&self) -> Ratchet {
        let mut ratchet = self.clone();
        ratchet.inc();
        ratchet
    }
}

impl Default for Ratchet {
    fn default() -> Self {
        Self::new()
    }
}

impl TryFrom<String> for Ratchet {
    type Error = RatchetErr;

    fn try_from(string: String) -> Result<Self, Self::Error> {
        if string.len() != 133 {
            return Err(RatchetErr::BadLen(string.len()));
        }

        if &string[0..2] != RATCHET_SIGNIFIER {
            return Err(RatchetErr::BadEncoding(string[0..2].to_string()));
        }

        let d = base64::decode_config(&string[2..], base64::URL_SAFE_NO_PAD)?;

        let mut ratchet = Ratchet {
            large: Hash::zero(),
            medium: Hash::zero(),
            small: Hash::zero(),
            small_counter: 0,
            medium_counter: 0,
        };

        for (i, byte) in d.iter().enumerate() {
            match i {
                0..=31 => ratchet.small[i] = *byte,
                32 => ratchet.small_counter = *byte,
                33..=64 => ratchet.medium[i - 33] = *byte,
                65 => ratchet.medium_counter = *byte,
                66..=97 => ratchet.large[i - 66] = *byte,
                _ => (),
            }
        }

        Ok(ratchet)
    }
}

impl From<&Ratchet> for String {
    fn from(ratchet: &Ratchet) -> Self {
        let mut b: [u8; 98] = [0; 98];

        for (i, byte) in ratchet.small.iter().enumerate() {
            b[i] = *byte;
        }

        b[32] = ratchet.small_counter;

        for (i, byte) in ratchet.medium.iter().enumerate() {
            b[i + 33] = *byte;
        }

        b[65] = ratchet.medium_counter;

        for (i, byte) in ratchet.large.iter().enumerate() {
            b[i + 66] = *byte;
        }

        RATCHET_SIGNIFIER.to_owned() + &base64::encode_config(b, base64::URL_SAFE_NO_PAD)
    }
}

impl PreviousIterator {
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

        return None;
    }
}

impl Iterator for Ratchet {
    type Item = Ratchet;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.next_small_epoch())
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

pub(crate) fn inc_by(ratchet: &mut Ratchet, n: usize) -> (Ratchet, usize) {
    if n == 0 {
        return (ratchet.clone(), 0);
    } else if n >= LARGE_EPOCH_LENGTH - ratchet.combined_counter() {
        // `n` is larger than at least one large epoch jump
        let (mut jumped, jump_count) = ratchet.next_large_epoch();
        return inc_by(&mut jumped, n - jump_count);
    } else if n >= MEDIUM_EPOCH_LENGTH - ratchet.small_counter as usize {
        // `n` is larger than at lest one medium epoch jump
        let (mut jumped, jump_count) = ratchet.next_medium_epoch();
        return inc_by(&mut jumped, n - jump_count);
    }

    ratchet.small = Hash::from_chain(&ratchet.small, n);
    ratchet.small_counter += n as u8;

    (ratchet.clone(), n)
}
