use std::cmp;

use hex::FromHex;

use crate::{utils, PreviousErr, Ratchet};

fn shasum_from_hex(s: &str) -> Result<[u8; 32], hex::FromHexError> {
    <[u8; 32]>::from_hex(s)
}

const SEED: &str = "600b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33";

#[test]
fn test_ratchet() {
    // Seed pulled from https://whitepaper.fission.codes/file-system/partitions/private-directories/concepts/spiral-ratchet
    let seed = shasum_from_hex(SEED).unwrap();

    let a = &mut Ratchet::zero(seed);
    let expect = &Ratchet {
        large: shasum_from_hex("5aa00b14dd50887cdc0b0b55aa2da1eb5cc3a79cdbe893b2319da378a83ad0c5")
            .unwrap(),
        medium: shasum_from_hex("5a86c2477e2ae4ffcf6373cce82259eb542b72a72db9cf9cddfe06bcc20623b6")
            .unwrap(),
        medium_counter: 0,
        small: shasum_from_hex("962b7f9ac204ffd0fa398e9c875c90806c0cd6646655f7a5994b7a828b70c0da")
            .unwrap(),
        small_counter: 0,
    };
    assert_ratchet_equal(expect, a);

    a.inc();

    let b = &mut Ratchet::zero(seed);
    b.inc();

    assert_ratchet_equal(a, b);

    let a_key = a.key();
    let b_key = b.key();
    assert_eq!(a_key, b_key);
}

#[test]
fn test_ratchet_add_256() {
    let seed = shasum_from_hex(SEED).unwrap();
    // manually advance ratchet 256 (2 ^ 8) times
    let slow = &mut Ratchet::zero(seed);
    for _ in 0..256 {
        slow.inc();
    }

    // fast jump 256 values in one shot
    let (ref fast, _) = Ratchet::zero(seed).next_medium_epoch();
    assert_ratchet_equal(slow, fast);
}

// #[test]
// fn test_fuzz_ratchet {
//     // TODO: research rust fuzz impl
// }

#[test]
fn test_ratchet_add_65536() {
    let seed = shasum_from_hex(SEED).unwrap();
    // Manually advance ratchet (2 ^ 16) times
    let slow = &mut Ratchet::zero(seed);
    for _ in 0..65536 {
        slow.inc();
    }

    // Fast jump (2 ^ 16) values in one shot
    let (ref fast, _) = Ratchet::zero(seed).next_large_epoch();

    assert_ratchet_equal(slow, fast);
}

#[test]
fn test_ratchet_coding() {
    let seed = shasum_from_hex(SEED).unwrap();

    let a = &Ratchet::zero(seed);

    let encoded: String = a.into();

    let b = &Ratchet::try_from(encoded).unwrap();

    assert_ratchet_equal(a, b);
}

#[test]
fn test_ratchet_compare() {
    let one = &mut Ratchet::zero(shasum_from_hex(SEED).unwrap());

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
        shasum_from_hex("500b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
            .unwrap(),
    );

    // Panic if this does not error
    one.compare(&unrelated, 100_000).unwrap_err();
}

#[test]
fn test_ratchet_equal() {
    let a = Ratchet::zero(shasum_from_hex(SEED).unwrap());
    let b = Ratchet::zero(shasum_from_hex(SEED).unwrap());
    let c = Ratchet::zero(
        shasum_from_hex("0000000000000000000000000000000000000000000000000000000000000000")
            .unwrap(),
    );

    if a != b {
        panic!("Ratchet::equal method incorrectly asserts two equal ratchets are unequal");
    }

    if b == c {
        panic!("Ratchet::equal method incorrectly asserts two unequal ratchets are equal")
    }
}

#[test]
fn test_ratchet_previous_equal_error() {
    let old = Ratchet::zero(shasum_from_hex(SEED).unwrap());
    match old.previous(&old, 5) {
        Ok(_) => panic!("expected PreviousErr::EqualRatchets, got an iterator instead"),
        Err(e) => match e {
            PreviousErr::EqualRatchets => (),
            _ => panic!("expected PreviousErr::EqualRatchets, got {:?}", e),
        },
    }
}

#[test]
fn test_ratchet_previous_older_error() {
    let old = Ratchet::zero(shasum_from_hex(SEED).unwrap());
    let mut recent = old.clone();
    recent.inc();
    match old.previous(&recent, 5) {
        Ok(_) => panic!("expected PreviousErr::EqualRatchets, got an iterator instead"),
        Err(e) => match e {
            PreviousErr::OlderRatchet => (),
            _ => panic!("expected PreviousErr::EqualRatchets, got {:?}", e),
        },
    }
}

#[test]
fn test_ratchet_previous() {
    let old = Ratchet::zero(shasum_from_hex(SEED).unwrap());
    let increments: [usize; 5] = [1, 2, 2000, 20_000, 300_000];
    let limit = 5;

    for inc in increments.into_iter() {
        let mut recent = old.clone();
        recent.inc_by(inc);

        let limit = cmp::min(limit, inc);

        let mut expect: Vec<Ratchet> = vec![];
        let mut r = old.clone();
        for i in 0..limit {
            if i == 0 {
                // Set up the earliest ratchet we will see in the `previous` vector
                r.inc_by(inc - limit);
            } else {
                // Otherwise, increment by 1
                r.inc();
            }
            expect.push(r.clone());
        }

        let got = match recent.previous(&old, limit) {
            Ok(iter) => iter.collect::<Vec<_>>(),
            Err(e) => panic!("error for previous with inc {}: {:?}", inc, e),
        };

        assert_eq!(expect.len(), got.len());
        for (x, g) in expect.iter().rev().zip(got.iter()) {
            assert_ratchet_equal(x, g);
        }
    }
}

#[test]
fn test_xor() {
    let a = [0; 32];
    let b = [0; 32];
    let c = [0; 32];
    assert_eq!(c, utils::xor(&a, &b));

    let a = [0xFF; 32];
    let b = [0xFF; 32];
    let c = [0; 32];
    assert_eq!(c, utils::xor(&a, &b));

    let a = [0xFF; 32];
    let b = [0; 32];
    let c = [0xFF; 32];
    assert_eq!(c, utils::xor(&a, &b));
}

#[test]
fn test_compliment() {
    let d = [0; 32];
    let e = [0xFF; 32];
    assert_eq!(e, utils::compliment(&d));

    let d = [0; 32];
    let e = [0xFF; 32];
    assert_eq!(e, utils::compliment(&d));
}

fn assert_ratchet_equal(expect: &Ratchet, got: &Ratchet) {
    assert_eq!(hex::encode(expect.large), hex::encode(got.large));
    assert_eq!(hex::encode(expect.medium), hex::encode(got.medium));
    assert_eq!(expect.medium_counter, got.medium_counter);
    assert_eq!(hex::encode(expect.small), hex::encode(got.small));
    assert_eq!(expect.small_counter, got.small_counter);
}
