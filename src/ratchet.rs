use base64::{self, DecodeError};
use rand::Rng;
use sha3::{Digest, Sha3_256};
use std::error;
use std::fmt;

// Flag the encoding. The default encoding is:
// * base64URL-unpadded (signified with u)
// * SHA-256 (0x16: "F" in base64URL)
const RATCHET_SIGNIFIER: &str = "uF";
// number of iterations a previous search can use before
// ratchets are considered unrelated
const DEFAULT_PREV_BUDGET: isize = 1_000_000;

#[derive(Debug)]
pub enum RatchetErr {
    BadLen(usize),
    BadEncoding(String),
    UnknownRelation,
    Decode(DecodeError),
}

impl fmt::Display for RatchetErr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &*self {
            RatchetErr::BadLen(i) => write!(f, "invalid ratchet length {}", i),
            RatchetErr::BadEncoding(s) => write!(
                f,
                "unsupported ratched encoding: '{}'. only '{}' is supported",
                s, RATCHET_SIGNIFIER
            ),
            RatchetErr::UnknownRelation => write!(f, "cannot relate ratchets"),
            RatchetErr::Decode(e) => write!(f, "{:?}", e),
        }
    }
}

impl error::Error for RatchetErr {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match *self {
            RatchetErr::Decode(ref e) => Some(e),
            _ => None,
        }
    }
}

impl From<DecodeError> for RatchetErr {
    fn from(err: DecodeError) -> RatchetErr {
        RatchetErr::Decode(err)
    }
}

#[derive(Debug)]
pub enum PreviousErr {
    ExhaustedBudget,
    EqualRatchets,
    OlderRatchet,
}

impl fmt::Display for PreviousErr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            PreviousErr::ExhaustedBudget => write!(f, "exhausted ratchet discrepency budget"),
            PreviousErr::EqualRatchets => write!(f, "ratchets are equal"),
            PreviousErr::OlderRatchet => write!(f, "self ratchet is older than given ratchet"),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Ratchet {
    large: [u8; 32],
    medium: [u8; 32],
    medium_counter: u8,
    small: [u8; 32],
    small_counter: u8,
}

impl Ratchet {
    pub fn new() -> Self {
        // 32 bytes for the seed, plus two extra bytes to randomize small & medium starts
        let seed: [u8; 32] = rand::thread_rng().gen::<[u8; 32]>();
        let inc_med = rand::thread_rng().gen::<u8>();
        let inc_small = rand::thread_rng().gen::<u8>();
        let med_seed = hash_32(compliment(seed));
        let small_seed = hash_32(compliment(med_seed));

        Ratchet {
            large: hash_32(seed),
            medium: hash_32_n(med_seed, inc_med),
            medium_counter: inc_med,
            small: hash_32_n(small_seed, inc_small),
            small_counter: inc_small,
        }
    }

    fn zero(seed: [u8; 32]) -> Self {
        let med = hash_32(compliment(seed));
        Ratchet {
            large: hash_32(seed),
            medium: med,
            medium_counter: 0,
            small: hash_32(compliment(med)),
            small_counter: 0,
        }
    }

    pub fn key(self) -> [u8; 32] {
        let v = xor(self.large, xor(self.medium, self.small));
        hash_32(v)
    }

    pub fn summary(self) -> String {
        format!(
            "{:?}-{:?}:{:?}-{:?}:{:?}",
            &self.large[0..3],
            self.medium_counter,
            &self.medium[0..3],
            self.small_counter,
            &self.small[0..3]
        )
    }

    pub fn encode(self) -> String {
        let mut b: [u8; 98] = [0; 98];
        for (i, byte) in self.small.iter().enumerate() {
            b[i] = *byte;
        }
        b[32] = self.small_counter;
        for (i, byte) in self.medium.iter().enumerate() {
            b[i + 33] = *byte;
        }
        b[65] = self.medium_counter;
        for (i, byte) in self.large.iter().enumerate() {
            b[i + 66] = *byte;
        }
        RATCHET_SIGNIFIER.to_owned() + &base64::encode_config(b, base64::URL_SAFE_NO_PAD)
    }

    pub fn inc(&mut self) {
        if self.small_counter == 255 {
            let (r, _) = next_medium_epoch(*self);
            *self = r;
            return;
        }
        self.small = hash_32(self.small);
        self.small_counter += 1;
    }

    pub fn inc_by(&mut self, n: usize) {
        let (jumped, _) = inc_by(*self, n as isize);
        *self = jumped;
    }

    pub fn compare(self, other: &Ratchet, max_steps: usize) -> Result<isize, RatchetErr> {
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
            self_large = hash_32(self_large);
            other_large = hash_32(other_large);
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

    pub fn equal(&self, right: &Ratchet) -> bool {
        self.small == right.small
            && self.small_counter == right.small_counter
            && self.medium == right.medium
            && self.medium_counter == right.medium_counter
            && self.large == right.large
    }

    // known_after is probabilistic. Returns true if self is known to be after b, and false
    // if large counters are inequal (meaning r is before, equal, unrelated, or after)
    pub fn known_after(self, other: Ratchet) -> bool {
        self.large == other.large
            && self.medium_counter >= other.medium_counter
            && self.small_counter > other.small_counter
    }

    // webnative version is a generator
    // go version returns slice of ratchets
    // create PreviousIterator, that satisfies the Iterator trait
    // so calling "next" or "iter" will allow you to iterate over
    // the previous ratchets
    pub fn previous(self, old: &Ratchet, limit: usize) -> Result<Vec<Ratchet>, PreviousErr> {
        self.previous_budget(old, DEFAULT_PREV_BUDGET, limit)
    }

    fn previous_budget(
        self,
        old: &Ratchet,
        discrepency_budget: isize,
        limit: usize,
    ) -> Result<Vec<Ratchet>, PreviousErr> {
        if self.equal(old) {
            return Err(PreviousErr::EqualRatchets);
        } else if old.known_after(self) {
            return Err(PreviousErr::OlderRatchet);
        }
        previous_helper(&self.clone(), old, discrepency_budget, limit)
    }

    fn combined_counter(self) -> usize {
        (256 * self.medium_counter as usize) + self.small_counter as usize
    }
}

impl Default for Ratchet {
    fn default() -> Self {
        Self::new()
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

    let (old_next_large, old_next_large_steps_done) = next_large_epoch(*old);

    if recent.large == old.large || recent.large == old_next_large.large {
        let (old_next_medium, old_next_medium_steps_done) = next_medium_epoch(*old);

        if recent.medium == old.medium || recent.medium == old_next_medium.medium {
            // break out of the recursive pattern at this point because discrepency is
            // within the small ratchet. working sequentially if faster
            let mut revision = *old;
            let mut next = *old;
            let mut revisions = vec![*old];
            next.inc();
            while !next.equal(recent) {
                revision.inc();
                next.inc();
                revisions.push(revision);
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

fn inc_by(mut r: Ratchet, n: isize) -> (Ratchet, isize) {
    if n <= 0 {
        return (r, 0);
    } else if n >= 256 * 256 - r.combined_counter() as isize {
        // n is larger than at least one large epoch jump
        let (jumped, jump_count) = next_large_epoch(r);
        return inc_by(jumped, n - jump_count);
    } else if n >= 256 - r.small_counter as isize {
        // n is larger than at lest one medium epoch jump
        let (jumped, jump_count) = next_medium_epoch(r);
        return inc_by(jumped, n - jump_count);
    }
    r.small = hash_32_n(r.small, n as u8);
    r.small_counter += n as u8;
    (r, n)
}

fn next_large_epoch(r: Ratchet) -> (Ratchet, isize) {
    (
        Ratchet::zero(r.large),
        256 * 256 - r.combined_counter() as isize,
    )
}

fn next_medium_epoch(r: Ratchet) -> (Ratchet, isize) {
    if r.medium_counter == 255 {
        return next_large_epoch(r);
    }

    let jumped = Ratchet {
        large: r.large,
        medium: hash_32(r.medium),
        medium_counter: r.medium_counter + 1,
        small: hash_32(compliment(r.medium)),
        small_counter: 0,
    };
    let jump_count = jumped.combined_counter() - r.combined_counter();
    (jumped, jump_count as isize)
}

pub fn decode_ratchet(s: String) -> Result<Ratchet, RatchetErr> {
    if s.len() != 133 {
        return Err(RatchetErr::BadLen(s.len()));
    }
    if &s[0..2] != RATCHET_SIGNIFIER {
        return Err(RatchetErr::BadEncoding(s[0..2].to_string()));
    }
    let d = base64::decode_config(&s[2..], base64::URL_SAFE_NO_PAD)?;

    let mut s = Ratchet {
        small: [0; 32],
        small_counter: 0,
        medium: [0; 32],
        medium_counter: 0,
        large: [0; 32],
    };

    for (i, byte) in d.iter().enumerate() {
        match i {
            0..=31 => s.small[i] = *byte,
            32 => s.small_counter = *byte,
            33..=64 => s.medium[i - 33] = *byte,
            65 => s.medium_counter = *byte,
            66..=97 => s.large[i - 66] = *byte,
            _ => (),
        }
    }
    Ok(s)
}

fn hash_32(d: [u8; 32]) -> [u8; 32] {
    let mut hasher = Sha3_256::new();
    hasher.update(d);
    let result_vec = hasher.finalize().to_vec();
    let mut arr = [0; 32];
    for (i, byte) in result_vec.iter().enumerate() {
        arr[i] = *byte;
    }
    arr
}

fn hash_32_n(mut d: [u8; 32], n: u8) -> [u8; 32] {
    for _ in 0..n {
        d = hash_32(d);
    }
    d
}

fn xor(a: [u8; 32], b: [u8; 32]) -> [u8; 32] {
    let mut c: [u8; 32] = [0; 32];
    for (i, (a_byte, b_byte)) in a.iter().zip(b.iter()).enumerate() {
        c[i] = a_byte ^ b_byte;
    }
    c
}

fn compliment(d: [u8; 32]) -> [u8; 32] {
    let mut e: [u8; 32] = [0; 32];
    for (i, d_byte) in d.iter().enumerate() {
        e[i] = !d_byte;
    }
    e
}

#[cfg(test)]
mod tests {
    use super::*;
    use hex::FromHex;

    fn shasum_from_hex(s: &str) -> Result<[u8; 32], hex::FromHexError> {
        <[u8; 32]>::from_hex(s)
    }

    #[test]
    fn test_ratchet() {
        // seed pulled from https://whitepaper.fission.codes/file-system/partitions/private-directories/concepts/ratchet-ratchet
        let seed =
            shasum_from_hex("600b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
                .unwrap();

        let mut a = Ratchet::zero(seed);
        let expect = Ratchet {
            large: shasum_from_hex(
                "5aa00b14dd50887cdc0b0b55aa2da1eb5cc3a79cdbe893b2319da378a83ad0c5",
            )
            .unwrap(),
            medium: shasum_from_hex(
                "5a86c2477e2ae4ffcf6373cce82259eb542b72a72db9cf9cddfe06bcc20623b6",
            )
            .unwrap(),
            medium_counter: 0,
            small: shasum_from_hex(
                "962b7f9ac204ffd0fa398e9c875c90806c0cd6646655f7a5994b7a828b70c0da",
            )
            .unwrap(),
            small_counter: 0,
        };
        assert_ratchet_equal(expect, a);

        a.inc();
        let mut b = Ratchet::zero(seed);
        b.inc();
        assert_ratchet_equal(a, b);

        let a_key = a.key();
        let b_key = b.key();
        assert_eq!(a_key, b_key);
    }

    #[test]
    fn test_ratchet_add_256() {
        let seed =
            shasum_from_hex("600b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
                .unwrap();
        // manually advance ratchet 256 (2 ^ 8) times
        let mut slow = Ratchet::zero(seed);
        for _ in 0..256 {
            slow.inc();
        }

        // fast jump 256 values in one shot
        let (fast, _) = next_medium_epoch(Ratchet::zero(seed));
        assert_ratchet_equal(slow, fast);
    }

    // #[test]
    // fn test_fuzz_ratchet {
    //     // TODO: research rust fuzz impl
    // }

    #[test]
    fn test_ratchet_add_65536() {
        let seed =
            shasum_from_hex("600b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
                .unwrap();
        // manually advance ratchet (2 ^ 16) times
        let mut slow = Ratchet::zero(seed);
        for _ in 0..65536 {
            slow.inc();
        }

        // fast jump (2 ^ 16) values in one shot
        let (fast, _) = next_large_epoch(Ratchet::zero(seed));
        assert_ratchet_equal(slow, fast);
    }

    #[test]
    fn test_ratchet_coding() {
        let seed =
            shasum_from_hex("600b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
                .unwrap();
        let a = Ratchet::zero(seed);
        let encoded = a.encode();

        let b = decode_ratchet(encoded).unwrap();
        assert_ratchet_equal(a, b);
    }

    #[test]
    fn test_ratchet_compare() {
        let one = Ratchet::zero(
            shasum_from_hex("600b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
                .unwrap(),
        );
        let mut two = one.clone();
        two.inc();
        let mut twenty_five_thousand = one.clone();
        twenty_five_thousand.inc_by(25000);

        let mut one_hundred_thousand = one.clone();
        one_hundred_thousand.inc_by(100_000);

        let mut temp = one.clone();
        temp.inc_by(65_536);

        struct Cases<'a> {
            description: &'a str,
            a: Ratchet,
            b: Ratchet,
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
                c.a.compare(&c.b, c.max_steps)
                    .unwrap_or_else(|e| panic!("error in case '{}': {:?}", c.description, e));
            assert_eq!(c.expect, got);
        }

        let unrelated = Ratchet::zero(
            shasum_from_hex("500b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
                .unwrap(),
        );
        // panic if this does not error
        one.compare(&unrelated, 100_000).unwrap_err();
    }

    #[test]
    fn test_ratchet_equal() {
        let a = Ratchet::zero(
            shasum_from_hex("600b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
                .unwrap(),
        );
        let b = Ratchet::zero(
            shasum_from_hex("600b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
                .unwrap(),
        );
        let c = Ratchet::zero(
            shasum_from_hex("0000000000000000000000000000000000000000000000000000000000000000")
                .unwrap(),
        );

        if !a.equal(&b) {
            panic!("Ratchet::equal method incorrectly asserts two equal ratchets are unequal");
        }

        if b.equal(&c) {
            panic!("Ratchet::equal method incorrectly asserts two unequal ratchets are equal")
        }
    }

    #[test]
    fn test_ratchet_previous_equal_error() {
        let old = Ratchet::zero(
            shasum_from_hex("600b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
                .unwrap(),
        );
        match old.previous(&old, 5) {
            Ok(r) => panic!("expected PreviousErr::EqualRatchets, got {:?}", r),
            Err(e) => match e {
                PreviousErr::EqualRatchets => (),
                _ => panic!("expected PreviousErr::EqualRatchets, got {:?}", e),
            },
        }
    }

    #[test]
    fn test_ratchet_previous_older_error() {
        let old = Ratchet::zero(
            shasum_from_hex("600b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
                .unwrap(),
        );
        let mut recent = old.clone();
        recent.inc();
        match old.previous(&recent, 5) {
            Ok(r) => panic!("expected PreviousErr::EqualRatchets, got {:?}", r),
            Err(e) => match e {
                PreviousErr::OlderRatchet => (),
                _ => panic!("expected PreviousErr::EqualRatchets, got {:?}", e),
            },
        }
    }

    #[test]
    fn test_ratchet_previous() {
        let old = Ratchet::zero(
            shasum_from_hex("600b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
                .unwrap(),
        );
        let increments: [usize; 5] = [1, 2, 2000, 20_000, 300_000];
        let limit = 5;

        for inc in increments.into_iter() {
            let mut recent = old.clone();
            recent.inc_by(inc);

            let mut limit = limit;
            if inc < limit {
                limit = inc;
            }

            let mut expect: Vec<Ratchet> = vec![];

            let mut r = old.clone();
            for i in 0..limit {
                if i == 0 {
                    // set up the earliest ratchet we will see in
                    // the `previous` vector
                    r.inc_by(inc - limit);
                } else {
                    // otherwise, increment by 1
                    r.inc();
                }
                expect.push(r.clone());
            }

            let got = match recent.previous(&old, limit) {
                Ok(g) => g,
                Err(e) => panic!("error for previous with inc {}: {:?}", inc, e),
            };

            assert_eq!(expect.len(), got.len());
            for (x, g) in expect.into_iter().rev().zip(got.into_iter()).into_iter() {
                assert_ratchet_equal(x, g);
            }
        }
    }

    #[test]
    fn test_xor() {
        let a = [0; 32];
        let b = [0; 32];
        let c = [0; 32];
        assert_eq!(c, xor(a, b));

        let a = [0xFF; 32];
        let b = [0xFF; 32];
        let c = [0; 32];
        assert_eq!(c, xor(a, b));

        let a = [0xFF; 32];
        let b = [0; 32];
        let c = [0xFF; 32];
        assert_eq!(c, xor(a, b));
    }

    #[test]
    fn test_compliment() {
        let d = [0; 32];
        let e = [0xFF; 32];
        assert_eq!(e, compliment(d));

        let d = [0; 32];
        let e = [0xFF; 32];
        assert_eq!(e, compliment(d));
    }

    fn assert_ratchet_equal(expect: Ratchet, got: Ratchet) {
        assert_eq!(hex::encode(expect.large), hex::encode(got.large));
        assert_eq!(hex::encode(expect.medium), hex::encode(got.medium));
        assert_eq!(expect.medium_counter, got.medium_counter);
        assert_eq!(hex::encode(expect.small), hex::encode(got.small));
        assert_eq!(expect.small_counter, got.small_counter);
    }
}
