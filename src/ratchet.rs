use std::{
    cmp,
    fmt::{self, Display, Formatter},
};

use crate::{
    constants::{DEFAULT_PREV_BUDGET, RATCHET_SIGNIFIER},
    utils, PreviousErr, RatchetErr,
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
/// [1]: https://github.com/fission-suite/skip-ratchet-paper/blob/initial-draft/spiral-ratchet.pdf
#[derive(Clone, PartialEq, Debug, Eq)]
pub struct Ratchet {
    pub(crate) large: [u8; 32],
    pub(crate) medium: [u8; 32],
    pub(crate) medium_counter: u8,
    pub(crate) small: [u8; 32],
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
/// let mut ratchet1 = Ratchet::new();
/// ratchet1.inc_by(10);
///
/// let mut ratchet2 = ratchet1.clone();
/// ratchet2.inc_by(10);
///
/// for r in ratchet2.previous(&ratchet1, 10) {
///   println!("{:?}", r);
/// }
/// ```
#[derive(Clone, Debug)]
pub struct PreviousIterator {
    revisions: Vec<Ratchet>,
}

impl PreviousIterator {
    /// Create a new `PreviousIterator`
    pub fn new(
        recent: &Ratchet,
        old: &Ratchet,
        discrepancy_budget: usize,
        limit: usize,
    ) -> Result<Self, PreviousErr> {
        let mut discrepancy_budget = discrepancy_budget as isize;
        let mut old = old.clone();

        while discrepancy_budget != 0 {
            // We gotta check if we can skip large epochs.
            let (old_next_large, old_next_large_steps_done) = old.next_large_epoch();
            if recent.large != old.large && recent.large != old_next_large.large {
                discrepancy_budget -= old_next_large_steps_done as isize;
                old = old_next_large;
                continue;
            }

            // We also gotta check if we can skip medium epochs.
            let (old_next_medium, old_next_medium_steps_done) = old.next_medium_epoch();
            if recent.medium != old.medium && recent.medium != old_next_medium.medium {
                discrepancy_budget -= old_next_medium_steps_done as isize;
                old = old_next_medium;
                continue;
            }

            let revisions = Self::get_revisions(recent, &old, limit);

            return Ok(Self { revisions });
        }

        Err(PreviousErr::ExhaustedBudget)
    }

    fn get_revisions(recent: &Ratchet, old: &Ratchet, limit: usize) -> Vec<Ratchet> {
        let mut revision = old.clone();
        let mut revisions = vec![old.clone()];
        let mut next = old.clone();
        next.inc();

        while &next != recent {
            revision.inc();
            next.inc();
            revisions.push(revision.clone());
        }

        let limit = cmp::min(limit, revisions.len());

        revisions[revisions.len() - limit..].to_vec()
    }
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
        let seed: [u8; 32] = rand::thread_rng().gen::<[u8; 32]>();
        let inc_med = rand::thread_rng().gen::<u8>();
        let inc_small = rand::thread_rng().gen::<u8>();
        let med_seed = utils::hash_32(&utils::compliment(&seed));
        let small_seed = utils::hash_32(&utils::compliment(&med_seed));

        Ratchet {
            large: utils::hash_32(&seed),
            medium: utils::hash_32_n(med_seed, inc_med),
            medium_counter: inc_med,
            small: utils::hash_32_n(small_seed, inc_small),
            small_counter: inc_small,
        }
    }

    /// Creates a new ratchet from a seed with zero counters.
    pub(crate) fn zero(seed: [u8; 32]) -> Self {
        let med = utils::hash_32(&utils::compliment(&seed));
        Ratchet {
            large: utils::hash_32(&seed),
            medium: med,
            medium_counter: 0,
            small: utils::hash_32(&utils::compliment(&med)),
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
    pub fn key(&self) -> [u8; 32] {
        let v = utils::xor(&self.large, &utils::xor(&self.medium, &self.small));
        utils::hash_32(&v)
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

        self.small = utils::hash_32(&self.small);
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
            self_large = utils::hash_32(&self_large);
            other_large = utils::hash_32(&other_large);
            steps += 1;

            if other_large == self.large {
                // Other_large_counter * 256 * 256 is the count of increments applied via advancing the large digit continually.
                // -other_large_counter is the difference between 'other' and its next large epoch.
                // self_counter is just what's self to add because of the count at which 'self' is
                return Ok((steps * 256 * 256) - (other_counter + self_counter));
            }

            if self_large == other.large {
                // In this case, we compute the same difference, but return the negative to indicate that 'other' is bigger that
                // 'self' rather than the other way around.
                return Ok(-(steps * 256 * 256) - (self_counter + other_counter));
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
    /// let mut ratchet1 = Ratchet::new();
    /// ratchet1.inc_by(10);
    ///
    /// let mut ratchet2 = ratchet1.clone();
    /// ratchet2.inc_by(10);
    ///
    /// for r in ratchet2.previous(&ratchet1, 10) {
    ///   println!("{:?}", r);
    /// }
    /// ```
    pub fn previous(&self, old: &Ratchet, limit: usize) -> Result<PreviousIterator, PreviousErr> {
        if self == old {
            return Err(PreviousErr::EqualRatchets);
        } else if old.known_after(self) {
            return Err(PreviousErr::OlderRatchet);
        }

        PreviousIterator::new(self, old, DEFAULT_PREV_BUDGET, limit)
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
        (256 * self.medium_counter as usize) + self.small_counter as usize
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
            Ratchet::zero(self.large),
            256 * 256 - self.combined_counter(),
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
            medium: utils::hash_32(&self.medium),
            medium_counter: self.medium_counter + 1,
            small: utils::hash_32(&utils::compliment(&self.medium)),
            small_counter: 0,
        };

        let jump_count = jumped.combined_counter() - self.combined_counter();
        (jumped, jump_count)
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
            small: [0; 32],
            small_counter: 0,
            medium: [0; 32],
            medium_counter: 0,
            large: [0; 32],
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

impl Iterator for PreviousIterator {
    type Item = Ratchet;

    fn next(&mut self) -> Option<Self::Item> {
        self.revisions.pop()
    }
}

impl Display for Ratchet {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("Ratchet")
            .field("small", &self.small[0..3].to_vec())
            .field("medium", &self.medium[0..3].to_vec())
            .field("large", &self.large[0..3].to_vec())
            .field("small_counter", &self.small_counter)
            .field("medium_counter", &self.medium_counter)
            .finish()
    }
}

pub(crate) fn inc_by(ratchet: &mut Ratchet, n: usize) -> (Ratchet, usize) {
    if n == 0 {
        return (ratchet.clone(), 0);
    } else if n >= 256 * 256 - ratchet.combined_counter() {
        // `n` is larger than at least one large epoch jump
        let (mut jumped, jump_count) = ratchet.next_large_epoch();
        return inc_by(&mut jumped, n - jump_count);
    } else if n >= 256 - ratchet.small_counter as usize {
        // `n` is larger than at lest one medium epoch jump
        let (mut jumped, jump_count) = ratchet.next_medium_epoch();
        return inc_by(&mut jumped, n - jump_count);
    }

    ratchet.small = utils::hash_32_n(ratchet.small, n as u8);
    ratchet.small_counter += n as u8;

    (ratchet.clone(), n)
}
