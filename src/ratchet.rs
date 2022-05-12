use crate::{
    constants::{DEFAULT_PREV_BUDGET, RATCHET_SIGNIFIER},
    utils, PreviousErr, RatchetErr,
};
use rand::Rng;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ratchet {
    pub(crate) large: [u8; 32],
    pub(crate) medium: [u8; 32],
    pub(crate) medium_counter: u8,
    pub(crate) small: [u8; 32],
    pub(crate) small_counter: u8,
}

impl Ratchet {
    pub fn new() -> Self {
        // 32 bytes for the seed, plus two extra bytes to randomize small & medium starts
        let seed: [u8; 32] = rand::thread_rng().gen::<[u8; 32]>();
        let inc_med = rand::thread_rng().gen::<u8>();
        let inc_small = rand::thread_rng().gen::<u8>();
        let med_seed = utils::hash_32(utils::compliment(seed));
        let small_seed = utils::hash_32(utils::compliment(med_seed));

        Ratchet {
            large: utils::hash_32(seed),
            medium: utils::hash_32_n(med_seed, inc_med),
            medium_counter: inc_med,
            small: utils::hash_32_n(small_seed, inc_small),
            small_counter: inc_small,
        }
    }

    pub(crate) fn zero(seed: [u8; 32]) -> Self {
        let med = utils::hash_32(utils::compliment(seed));
        Ratchet {
            large: utils::hash_32(seed),
            medium: med,
            medium_counter: 0,
            small: utils::hash_32(utils::compliment(med)),
            small_counter: 0,
        }
    }

    pub fn key(&self) -> [u8; 32] {
        let v = utils::xor(self.large, utils::xor(self.medium, self.small));
        utils::hash_32(v)
    }

    pub fn summary(&self) -> String {
        format!(
            "{:?}-{:?}:{:?}-{:?}:{:?}",
            &self.large[0..3],
            self.medium_counter,
            &self.medium[0..3],
            self.small_counter,
            &self.small[0..3]
        )
    }

    pub fn inc(&mut self) {
        if self.small_counter == 255 {
            let (r, _) = self.next_medium_epoch();
            *self = r;
            return;
        }
        self.small = utils::hash_32(self.small);
        self.small_counter += 1;
    }

    pub fn inc_by(&mut self, n: usize) {
        let (jumped, _) = inc_by(self, n as isize);
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

        // here, the large digit always differs, so one of the ratchets will always be bigger,
        // they cannot be equal.
        // We can find out which one is bigger by hashing both at the same time and looking at
        // when one created the same digit as the other, essentially racing the large digit's
        // recursive hashes.
        let mut self_large = self.large;
        let mut other_large = other.large;
        let mut steps = 0;
        let mut steps_left = max_steps;

        // Since the two ratches might just be generated from a totally different setup, we
        // can never _really_ know which one is the bigger one. They might be unrelated.
        while steps_left > 0 {
            self_large = utils::hash_32(self_large);
            other_large = utils::hash_32(other_large);
            steps += 1;

            if other_large == self.large {
                // other_large_counter * 256 * 256 is the count of increments applied via
                // advancing the large digit continually
                // -other_large_counter is the difference between 'other' and its next large epoch.
                // self_counter is just what's self to add because of the count at which 'self' is
                return Ok((steps * 256 * 256) - (other_counter + self_counter));
            }

            if self_large == other.large {
                // in this case, we compute the same difference, but return the negative to
                // indicate that 'other' is bigger that 'self' rather than the other way
                // around.
                return Ok(-(steps * 256 * 256) - (self_counter + other_counter));
            }
            steps_left -= 1;
        }
        Err(RatchetErr::UnknownRelation)
    }

    // known_after is probabilistic. Returns true if self is known to be after b, and false
    // if large counters are inequal (meaning r is before, equal, unrelated, or after)
    pub fn known_after(&self, other: &Ratchet) -> bool {
        self.large == other.large
            && self.medium_counter >= other.medium_counter
            && self.small_counter > other.small_counter
    }

    // webnative version is a generator
    // go version returns slice of ratchets
    // create PreviousIterator, that satisfies the Iterator trait
    // so calling "next" or "iter" will allow you to iterate over
    // the previous ratchets
    pub fn previous(&self, old: &Ratchet, limit: usize) -> Result<Vec<Ratchet>, PreviousErr> {
        self.previous_budget(old, DEFAULT_PREV_BUDGET, limit)
    }

    fn previous_budget(
        &self,
        old: &Ratchet,
        discrepency_budget: isize,
        limit: usize,
    ) -> Result<Vec<Ratchet>, PreviousErr> {
        if self == old {
            return Err(PreviousErr::EqualRatchets);
        } else if old.known_after(self) {
            return Err(PreviousErr::OlderRatchet);
        }

        previous_helper(&self.clone(), old, discrepency_budget, limit)
    }

    fn combined_counter(&self) -> usize {
        (256 * self.medium_counter as usize) + self.small_counter as usize
    }

    pub(crate) fn next_large_epoch(&self) -> (Ratchet, isize) {
        (
            Ratchet::zero(self.large),
            256 * 256 - self.combined_counter() as isize,
        )
    }

    pub(crate) fn next_medium_epoch(&self) -> (Ratchet, isize) {
        if self.medium_counter == 255 {
            return self.next_large_epoch();
        }

        let jumped = Ratchet {
            large: self.large,
            medium: utils::hash_32(self.medium),
            medium_counter: self.medium_counter + 1,
            small: utils::hash_32(utils::compliment(self.medium)),
            small_counter: 0,
        };

        let jump_count = jumped.combined_counter() - self.combined_counter();
        (jumped, jump_count as isize)
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

// TODO: this won't work for histories that span the small ratchet
pub fn previous_helper(
    recent: &Ratchet,
    old: &Ratchet,
    discrepency_budget: isize,
    limit: usize,
) -> Result<Vec<Ratchet>, PreviousErr> {
    if discrepency_budget < 0 {
        return Err(PreviousErr::ExhaustedBudget);
    }

    let (old_next_large, old_next_large_steps_done) = old.next_large_epoch();

    if recent.large == old.large || recent.large == old_next_large.large {
        let (old_next_medium, old_next_medium_steps_done) = old.next_medium_epoch();

        if recent.medium == old.medium || recent.medium == old_next_medium.medium {
            // break out of the recursive pattern at this point because discrepency is
            // within the small ratchet. working sequentially if faster
            let mut revision = old.clone();
            let mut next = old.clone();
            let mut revisions = vec![old.clone()];

            next.inc();

            while next != *recent {
                revision.inc();
                next.inc();
                revisions.push(revision.clone());
            }
            let mut lim = limit;
            if revisions.len() < limit {
                lim = revisions.len();
            }
            // only return the limited number of previous ratchets
            revisions = revisions[revisions.len() - lim..].to_vec();
            revisions.reverse();

            return Ok(revisions);
        }

        return previous_helper(
            recent,
            &old_next_medium,
            discrepency_budget - old_next_medium_steps_done as isize,
            limit,
        );
    }

    previous_helper(
        recent,
        &old_next_large,
        discrepency_budget - old_next_large_steps_done as isize,
        limit,
    )
}

pub(crate) fn inc_by(ratchet: &mut Ratchet, n: isize) -> (Ratchet, isize) {
    if n <= 0 {
        return (ratchet.clone(), 0);
    } else if n >= 256 * 256 - ratchet.combined_counter() as isize {
        // n is larger than at least one large epoch jump
        let (mut jumped, jump_count) = ratchet.next_large_epoch();
        return inc_by(&mut jumped, n - jump_count);
    } else if n >= 256 - ratchet.small_counter as isize {
        // n is larger than at lest one medium epoch jump
        let (mut jumped, jump_count) = ratchet.next_medium_epoch();
        return inc_by(&mut jumped, n - jump_count);
    }

    ratchet.small = utils::hash_32_n(ratchet.small, n as u8);
    ratchet.small_counter += n as u8;

    (ratchet.clone(), n)
}
