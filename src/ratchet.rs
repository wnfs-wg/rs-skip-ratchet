use crate::{
    constants::{
        DOMAIN_SEP_STR_LARGE, DOMAIN_SEP_STR_SALT, LARGE_EPOCH_LENGTH, MEDIUM_EPOCH_LENGTH,
    },
    hash::Hash,
    salt::Salt,
    PreviousErr, PreviousIterator, RatchetErr,
};
use rand_core::CryptoRngCore;
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
/// use sha3::Digest;
///
/// let ratchet = Ratchet::from_rng(&mut rand::thread_rng());
/// let key: [u8; 32] = ratchet.derive_key("awesome.ly key derivation").finalize().into();
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

impl Ratchet {
    /// Creates a randomly-generated Skip Ratchet.
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::Ratchet;
    ///
    /// let ratchet = Ratchet::from_rng(&mut rand::thread_rng());
    /// ```
    pub fn from_rng(rng: &mut impl CryptoRngCore) -> Self {
        // 32 bytes for the seed, plus two extra bytes to randomize small & medium starts
        let mut seed = [0u8; 32];
        let mut incs = [0u8; 2];
        rng.fill_bytes(&mut seed);
        rng.fill_bytes(&mut incs);
        let [inc_med, inc_small] = incs;

        Self::from_seed(&seed, inc_small, inc_med)
    }

    /// Creates a new ratchet from a seed with zero counters.
    pub fn zero(salt: [u8; 32], large_pre: &[u8; 32]) -> Self {
        let large = Hash::from([], large_pre);
        let medium_pre = Hash::from(salt, large_pre);
        let medium = Hash::from([], medium_pre);
        let small = Hash::from(salt, medium_pre);

        Ratchet {
            salt: Salt::from_raw(salt),
            large,
            medium,
            medium_counter: 0,
            small,
            small_counter: 0,
        }
    }

    /// Creates a new ratchet with given seed with given counters.
    pub fn from_seed(seed: &[u8; 32], inc_small: u8, inc_med: u8) -> Self {
        let salt = Hash::from(DOMAIN_SEP_STR_SALT, seed).into();
        let large_pre = Hash::from(DOMAIN_SEP_STR_LARGE, seed);
        let mut ratchet = Self::zero(salt, large_pre.as_slice());

        for _ in 0..inc_med {
            ratchet.next_medium_epoch();
        }

        for _ in 0..inc_small {
            ratchet.inc();
        }

        ratchet
    }

    /// Derives a new key from the ratchet.
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::Ratchet;
    /// use sha3::Digest;
    ///
    /// let ratchet = Ratchet::from_rng(&mut rand::thread_rng());
    /// let key: [u8; 32] = ratchet.derive_key("awesome.ly temporal key derivation").finalize().into();
    /// ```
    pub fn derive_key(&self, domain_separation_info: impl AsRef<[u8]>) -> Sha3_256 {
        Sha3_256::new()
            .chain_update(domain_separation_info)
            .chain_update(self.large)
            .chain_update(self.medium)
            .chain_update(self.small)
    }

    /// Returns the bytes that get hashed during key derivation.
    ///
    /// Can be useful for hashing using algorithms other than SHA3.
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::Ratchet;
    /// use sha3::{Sha3_256, Digest};
    ///
    /// let dsi = "awesome.ly key derivation 2023";
    /// let ratchet = Ratchet::from_rng(&mut rand::thread_rng());
    ///
    /// let key: [u8; 32] = ratchet.derive_key(dsi).finalize().into();
    /// let key2: [u8; 32] = Sha3_256::new().chain_update(ratchet.key_derivation_data(dsi)).finalize().into();
    ///
    /// assert_eq!(key, key2);
    /// ```
    pub fn key_derivation_data(&self, domain_separation_info: impl AsRef<[u8]>) -> Vec<u8> {
        let mut vec = Vec::new();
        vec.extend(domain_separation_info.as_ref());
        vec.extend(self.large.as_ref());
        vec.extend(self.medium.as_ref());
        vec.extend(self.small.as_ref());
        vec
    }

    /// Moves the ratchet forward by one step.
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::Ratchet;
    ///
    /// let mut ratchet = Ratchet::from_rng(&mut rand::thread_rng());
    /// ratchet.inc();
    /// ```
    pub fn inc(&mut self) {
        if self.small_counter == 255 {
            self.next_medium_epoch();
            return;
        }

        self.small = Hash::from([], self.small);
        self.small_counter += 1;
    }

    /// Moves the ratchet forward by `n` steps.
    ///
    /// # Examples
    /// ```
    /// use skip_ratchet::Ratchet;
    ///
    /// let mut ratchet = Ratchet::from_rng(&mut rand::thread_rng());
    /// ratchet.inc_by(3);
    ///
    /// println!("{:?}", ratchet);
    /// ```
    pub fn inc_by(&mut self, n: usize) {
        if n == 0 {
            return;
        } else if n >= LARGE_EPOCH_LENGTH - self.combined_counter() {
            // `n` is larger than at least one large epoch jump
            let jump_count = self.next_large_epoch();
            self.inc_by(n - jump_count);
            return;
        } else if n >= MEDIUM_EPOCH_LENGTH - self.small_counter as usize {
            // `n` is larger than at least one medium epoch jump
            let jump_count = self.next_medium_epoch();
            self.inc_by(n - jump_count);
            return;
        }

        self.small = Hash::from_chain([], self.small, n);
        self.small_counter += n as u8;
    }

    pub fn compare(&self, other: &Ratchet, max_steps: usize) -> Result<isize, RatchetErr> {
        if self.salt != other.salt {
            return Err(RatchetErr::UnknownRelation);
        }

        let self_counter = self.combined_counter() as isize;
        let other_counter = other.combined_counter() as isize;
        if self.large == other.large {
            return Ok(self_counter - other_counter);
        }

        // Here, the large digit always differs, so one of the ratchets will always be bigger, they cannot be equal.
        // We can find out which one is bigger by hashing both at the same time and looking at  when one created the same digit as the other,
        // essentially racing the large digit's recursive hashes.
        let mut self_large = self.large;
        let mut other_large = other.large;
        let mut steps = 0;

        // Since the two ratches might just be generated from a totally different setup, we can never _really_ know which one is the bigger one.
        // They might be unrelated.
        while steps <= max_steps {
            self_large = Hash::from([], self_large);
            other_large = Hash::from([], other_large);
            steps += 1;

            if other_large == self.large {
                // steps * LARGE_EPOCH_LENGTH is the count of `inc`s applied via advancing the large digit so far
                // -self_counter is the difference between `right` and its next large epoch.
                // other_counter is just what's left to add because of the count at which `self` is.
                let larger_count_ahead =
                    (steps * LARGE_EPOCH_LENGTH) as isize - other_counter + self_counter;

                return Ok(larger_count_ahead);
            }

            if self_large == other.large {
                // In this case, we compute the same difference, but return the negative to indicate that 'other' is bigger that
                // 'self' rather than the other way around.
                let larger_count_ahead =
                    (steps * LARGE_EPOCH_LENGTH) as isize - self_counter + other_counter;

                return Ok(-larger_count_ahead);
            }
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
    /// let mut ratchet1 = Ratchet::from_rng(&mut rand::thread_rng());
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
    pub fn previous(
        &self,
        old: &Ratchet,
        discrepancy_budget: usize,
    ) -> Result<PreviousIterator, PreviousErr> {
        if old.known_after(self) {
            return Err(PreviousErr::OlderRatchet);
        }

        PreviousIterator::new(old, self, discrepancy_budget)
    }

    /// Returns the number of steps away from "zero" this ratchet is.
    /// This is a number between 0 and 65535. If stepping the ratchet
    /// forwards results in the next large epoch to be loaded, this
    /// counter resets back to 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::Ratchet;
    ///
    /// let mut ratchet = Ratchet::from_rng(&mut rand::thread_rng());
    /// println!("{}", ratchet.combined_counter());
    /// ratchet.inc_by(10);
    /// println!("{}", ratchet.combined_counter());
    /// ```
    pub fn combined_counter(&self) -> usize {
        (MEDIUM_EPOCH_LENGTH * self.medium_counter as usize) + self.small_counter as usize
    }

    /// Skips the ratchet to the next large epoch.
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::Ratchet;
    ///
    /// let mut ratchet = Ratchet::from_rng(&mut rand::thread_rng());
    /// ratchet.next_large_epoch();
    /// ```
    pub fn next_large_epoch(&mut self) -> usize {
        let jump_count = LARGE_EPOCH_LENGTH - self.combined_counter();

        *self = Ratchet::zero(self.salt.into(), self.large.as_slice());

        jump_count
    }

    /// Skips the ratchet to the next medium epoch.
    ///
    /// # Examples
    ///
    /// ```
    /// use skip_ratchet::Ratchet;
    ///
    /// let mut ratchet = Ratchet::from_rng(&mut rand::thread_rng());
    /// ratchet.next_medium_epoch();
    /// ```
    pub fn next_medium_epoch(&mut self) -> usize {
        if self.medium_counter == 255 {
            return self.next_large_epoch();
        }

        let count_before = self.combined_counter();

        let medium_pre = Hash::from([], self.medium);
        self.medium = Hash::from([], medium_pre);
        self.small = Hash::from(self.salt, medium_pre);

        self.medium_counter += 1;
        self.small_counter = 0;

        self.combined_counter() - count_before
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

#[cfg(test)]
mod tests {
    use crate::{
        test_utils::{assert_ratchet_equal, hash_from_hex, salt, seed},
        Ratchet,
    };
    use std::vec;

    #[test]
    fn test_ratchet_add_256() {
        // manually advance ratchet 256 (2 ^ 8) times
        let slow = &mut Ratchet::zero(salt(), &seed());
        for _ in 0..256 {
            slow.inc();
        }

        // fast jump 256 values in one shot
        let fast = &mut Ratchet::zero(salt(), &seed());
        fast.next_medium_epoch();
        assert_ratchet_equal(slow, fast);
    }

    #[test]
    fn test_ratchet_compare() {
        let one = &mut Ratchet::zero(salt(), &seed());

        let two = &mut one.clone();
        two.inc();

        let twenty_five_thousand = &mut one.clone();
        twenty_five_thousand.inc_by(25000);

        let one_hundred_thousand = &mut one.clone();
        one_hundred_thousand.inc_by(100_000);

        let temp = &mut one.clone();
        temp.inc_by(65_536);

        struct Cases<'a> {
            description: &'a str,
            a: &'a Ratchet,
            b: &'a Ratchet,
            max_steps: usize,
            expect: isize,
        }

        let mut cases = vec![
            Cases {
                description: "comparing same ratchet",
                a: one,
                b: one,
                max_steps: 0,
                expect: 0,
            },
            Cases {
                description: "ratchet a is one step behind",
                a: one,
                b: two,
                max_steps: 1,
                expect: -1,
            },
            Cases {
                description: "ratchet a is one step ahead",
                a: two,
                b: one,
                max_steps: 1,
                expect: 1,
            },
            Cases {
                description: "ratchet a is 25000 steps ahead",
                a: twenty_five_thousand,
                b: one,
                max_steps: 10,
                expect: 25000,
            },
            Cases {
                description: "ratchet a is 65_536 steps behind",
                a: one,
                b: temp,
                max_steps: 10,
                expect: -65_536,
            },
            Cases {
                description: "ratchet a is 100_000 steps behind",
                a: one,
                b: one_hundred_thousand,
                max_steps: 10,
                expect: -100_000,
            },
        ];

        for c in cases.iter_mut() {
            let got =
                c.a.compare(c.b, c.max_steps)
                    .unwrap_or_else(|e| panic!("error in case '{}': {:?}", c.description, e));

            assert_eq!(c.expect, got);
        }

        let unrelated = Ratchet::zero(
            salt(),
            &hash_from_hex("500b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
                .into(),
        );

        // Panic if this does not error
        one.compare(&unrelated, 100_000).unwrap_err();
    }

    #[test]
    fn test_ratchet_equal() {
        let a = Ratchet::zero(salt(), &seed());
        let b = Ratchet::zero(salt(), &seed());
        let c = Ratchet::zero(
            salt(),
            &hash_from_hex("0000000000000000000000000000000000000000000000000000000000000000")
                .into(),
        );

        if a != b {
            panic!("Ratchet::equal method incorrectly asserts two equal ratchets are unequal");
        }

        if b == c {
            panic!("Ratchet::equal method incorrectly asserts two unequal ratchets are equal")
        }
    }

    #[test]
    fn test_ratchet_iterator() {
        let mut ratchet = Ratchet::zero(salt(), &seed());
        let mut via_iterator = ratchet.clone();

        ratchet.inc();
        assert_ratchet_equal(&ratchet, &via_iterator.next().unwrap());
        ratchet.inc();
        assert_ratchet_equal(&ratchet, &via_iterator.next().unwrap());
        ratchet.inc();
        assert_ratchet_equal(&ratchet, &via_iterator.next().unwrap());
    }
}

#[cfg(test)]
mod proptests {
    use crate::{prop_assert_ratchet_eq, test_utils::any_ratchet, Ratchet};
    use proptest::prelude::*;
    use test_strategy::proptest;

    #[proptest]
    fn test_ratchet_add_slow_equals_add_fast(
        #[strategy(0..100_000usize)] jumps: usize,
        #[strategy(any_ratchet())] mut ratchet: Ratchet,
    ) {
        let slow = &mut ratchet.clone();
        for _ in 0..jumps {
            slow.inc();
        }

        // Fast jump in ~O(log n) steps
        ratchet.inc_by(jumps);
        prop_assert_ratchet_eq!(slow, ratchet);
    }

    #[proptest]
    fn test_compare(
        #[strategy(0..100_000usize)] jumps: usize,
        #[strategy(any_ratchet())] smaller: Ratchet,
    ) {
        let mut bigger = smaller.clone();
        bigger.inc_by(jumps);
        prop_assert_eq!(bigger.compare(&smaller, jumps).unwrap(), jumps as isize);
    }

    #[proptest]
    fn test_compare_antisymmetry(
        #[strategy(0..100_000usize)] jumps: usize,
        #[strategy(any_ratchet())] smaller: Ratchet,
    ) {
        let mut bigger = smaller.clone();
        bigger.inc_by(jumps);
        let compare_a = bigger.compare(&smaller, jumps).unwrap();
        let compare_b = smaller.compare(&bigger, jumps).unwrap();
        prop_assert_eq!(compare_a, -compare_b);
    }

    #[proptest]
    fn test_compare_unrelated(
        #[strategy(any_ratchet())] ratchet1: Ratchet,
        #[strategy(any_ratchet())] ratchet2: Ratchet,
    ) {
        prop_assert!(matches!(ratchet1.compare(&ratchet2, 100), Err(_)));
    }

    #[cfg(feature = "serde")]
    #[proptest]
    fn test_dag_cbor_serde_roundtrip(#[strategy(any_ratchet())] ratchet: Ratchet) {
        use libipld::{
            cbor::DagCborCodec,
            prelude::{Decode, Encode},
            Ipld,
        };
        use std::io::Cursor;

        let ipld = libipld::serde::to_ipld(&ratchet).unwrap();
        let mut bytes = Vec::new();
        ipld.encode(DagCborCodec, &mut bytes).unwrap();

        let ipld = Ipld::decode(DagCborCodec, &mut Cursor::new(bytes)).unwrap();
        let ratchet_back = libipld::serde::from_ipld::<Ratchet>(ipld).unwrap();

        prop_assert_ratchet_eq!(ratchet_back, ratchet);
    }
}
