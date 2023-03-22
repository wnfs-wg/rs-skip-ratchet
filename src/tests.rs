use crate::{
    constants::LARGE_EPOCH_LENGTH, hash::Hash, ratchet::PreviousIterator, seek::JumpSize,
    PreviousErr, Ratchet, RatchetSeeker,
};
use hex::FromHex;
use proptest::prelude::*;
use std::vec;
use test_strategy::proptest;

fn hash_from_hex(s: &str) -> Hash {
    Hash::from_raw(<[u8; 32]>::from_hex(s).unwrap())
}

const SEED: &str = "600b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33";

#[test]
fn test_ratchet_zero() {
    // Seed pulled from https://whitepaper.fission.codes/file-system/partitions/private-directories/concepts/spiral-ratchet
    let seed = hash_from_hex(SEED);

    let a = &mut Ratchet::zero(seed.into());
    let expect = &Ratchet {
        large: hash_from_hex("5aa00b14dd50887cdc0b0b55aa2da1eb5cc3a79cdbe893b2319da378a83ad0c5"),
        medium: hash_from_hex("5a86c2477e2ae4ffcf6373cce82259eb542b72a72db9cf9cddfe06bcc20623b6"),
        small: hash_from_hex("962b7f9ac204ffd0fa398e9c875c90806c0cd6646655f7a5994b7a828b70c0da"),
        medium_counter: 0,
        small_counter: 0,
    };

    assert_ratchet_equal(expect, a);

    a.inc();

    let b = &mut Ratchet::zero(seed.into());
    b.inc();

    assert_ratchet_equal(a, b);

    let a_key = a.derive_key();
    let b_key = b.derive_key();
    assert_eq!(a_key, b_key);
}

#[test]
fn test_ratchet_add_256() {
    let seed = hash_from_hex(SEED);
    // manually advance ratchet 256 (2 ^ 8) times
    let slow = &mut Ratchet::zero(seed.into());
    for _ in 0..256 {
        slow.inc();
    }

    // fast jump 256 values in one shot
    let (ref fast, _) = Ratchet::zero(seed.into()).next_medium_epoch();
    assert_ratchet_equal(slow, fast);
}

// TODO(appcypher): Let's find out about property-based testing and see if we can use it here.

#[test]
fn test_ratchet_add_65536() {
    let seed = hash_from_hex(SEED);
    // Manually advance ratchet (2 ^ 16) times
    let slow = &mut Ratchet::zero(seed.into());
    for _ in 0..65536 {
        slow.inc();
    }

    // Fast jump (2 ^ 16) values in one shot
    let (ref fast, _) = Ratchet::zero(seed.into()).next_large_epoch();

    assert_ratchet_equal(slow, fast);
}

#[test]
fn test_ratchet_coding() {
    let seed = hash_from_hex(SEED);

    let a = &Ratchet::zero(seed.into());

    let encoded: String = a.into();

    let b = &Ratchet::try_from(encoded).unwrap();

    assert_ratchet_equal(a, b);
}

#[test]
fn test_ratchet_compare() {
    let one = &mut Ratchet::zero(hash_from_hex(SEED).into());

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
        hash_from_hex("500b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33").into(),
    );

    // Panic if this does not error
    one.compare(&unrelated, 100_000).unwrap_err();
}

#[test]
fn test_ratchet_equal() {
    let a = Ratchet::zero(hash_from_hex(SEED).into());
    let b = Ratchet::zero(hash_from_hex(SEED).into());
    let c = Ratchet::zero(
        hash_from_hex("0000000000000000000000000000000000000000000000000000000000000000").into(),
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
    let old = Ratchet::zero(hash_from_hex(SEED).into());
    match old.previous(&old, 10) {
        Ok(_) => panic!("expected PreviousErr::EqualRatchets, got an iterator instead"),
        Err(e) => match e {
            PreviousErr::EqualRatchets => (),
            _ => panic!("expected PreviousErr::EqualRatchets, got {:?}", e),
        },
    }
}

#[test]
fn test_ratchet_previous_older_error() {
    let old = Ratchet::zero(hash_from_hex(SEED).into());
    let mut recent = old.clone();
    recent.inc();
    match old.previous(&recent, 10) {
        Ok(_) => panic!("expected PreviousErr::EqualRatchets, got an iterator instead"),
        Err(e) => match e {
            PreviousErr::OlderRatchet => (),
            _ => panic!("expected PreviousErr::EqualRatchets, got {:?}", e),
        },
    }
}

#[test]
fn test_ratchet_previous_increments() {
    let discrepancy_budget = 1_000_000;
    let old = Ratchet::zero(hash_from_hex(SEED).into());
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
            Err(e) => panic!("error for previous with inc {}: {:?}", inc, e),
        };

        assert_eq!(expected_ratchets.len(), got_ratchets.len());
        for (expected, got) in expected_ratchets.iter().rev().zip(got_ratchets.iter()) {
            assert_ratchet_equal(expected, got);
        }
    }
}

#[test]
fn test_ratchet_previous_budget() {
    let old_ratchet = Ratchet::zero(hash_from_hex(SEED).into());
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

#[test]
fn test_ratchet_iterator() {
    let mut ratchet = Ratchet::zero(hash_from_hex(SEED).into());
    let mut via_iterator = ratchet.clone();

    ratchet.inc();
    assert_ratchet_equal(&ratchet, &via_iterator.next().unwrap());
    ratchet.inc();
    assert_ratchet_equal(&ratchet, &via_iterator.next().unwrap());
    ratchet.inc();
    assert_ratchet_equal(&ratchet, &via_iterator.next().unwrap());
}

#[test]
fn test_step_count_regression() {
    let old_ratchet = Ratchet::new(&mut rand::thread_rng());
    let mut new_ratchet = old_ratchet.clone();
    new_ratchet.inc_by(LARGE_EPOCH_LENGTH + 10);

    let mut iterator = PreviousIterator::new(&old_ratchet, &new_ratchet, 1_000_000_000).unwrap();

    for _ in 0..LARGE_EPOCH_LENGTH {
        assert!(iterator.next().is_some());
    }

    assert_ne!(iterator.step_count(), 0);

    for _ in 0..10 {
        assert!(iterator.next().is_some());
    }

    assert!(iterator.next().is_none());
}

fn assert_ratchet_equal(expected: &Ratchet, got: &Ratchet) {
    assert_eq!(expected.large, got.large);
    assert_eq!(expected.medium, got.medium);
    assert_eq!(expected.small, got.small);
    assert_eq!(expected.medium_counter, got.medium_counter);
    assert_eq!(expected.small_counter, got.small_counter);
}

fn any_jump_size() -> impl Strategy<Value = JumpSize> {
    (0..3).prop_map(|n| match n {
        0 => JumpSize::Zero,
        1 => JumpSize::Small,
        2 => JumpSize::Medium,
        3 => JumpSize::Large,
        _ => unreachable!(),
    })
}

#[proptest]
fn prop_ratchet_seek_finds(
    #[strategy(any::<[u8; 32]>().no_shrink())] seed: [u8; 32],
    #[strategy(0..10_000_000usize)] jump: usize,
    #[strategy(any_jump_size())] initial_jump_size: JumpSize,
) {
    let initial = Ratchet::zero(seed);
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
    assert_ratchet_equal(&goal, seeker.current())
}

#[proptest]
fn prop_ratchet_seek_finds_zero(
    #[strategy(any::<[u8; 32]>().no_shrink())] seed: [u8; 32],
    #[strategy(any_jump_size())] initial_jump_size: JumpSize,
) {
    let ratchet = Ratchet::zero(seed);

    let mut seeker = RatchetSeeker::new(ratchet.clone(), initial_jump_size);

    loop {
        if !seeker.step(std::cmp::Ordering::Greater) {
            break;
        }
    }

    assert_ratchet_equal(&ratchet, seeker.current());
}

#[proptest]
fn prop_ratchet_seek_finds_only_greater_and_less(
    #[strategy(any::<[u8; 32]>().no_shrink())] seed: [u8; 32],
    #[strategy(0..10_000_000usize)] jump: usize,
    #[strategy(any_jump_size())] initial_jump_size: JumpSize,
) {
    let initial = Ratchet::zero(seed);
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
    assert_ratchet_equal(&goal, seeker.current())
}

#[proptest]
fn prop_ratchet_step_count_is_inc_by(
    #[strategy(any::<[u8; 32]>().no_shrink())] seed: [u8; 32],
    #[strategy(0..10_000_000usize)] jump: usize,
) {
    let initial = Ratchet::zero(seed);
    let goal = {
        let mut goal = initial.clone();
        goal.inc_by(jump);
        goal
    };

    let iterator = PreviousIterator::new(&initial, &goal, 1_000_000_000).unwrap();

    assert_eq!(iterator.step_count(), jump);
}

#[proptest]
fn prop_ratchet_step_count_is_inc_by_minus_steps(
    #[strategy(any::<[u8; 32]>().no_shrink())] seed: [u8; 32],
    #[strategy(0..100usize)] previous_steps: usize,
    #[strategy(0..100_000usize)] additional_jumps: usize,
) {
    let jumps = previous_steps + additional_jumps;
    let initial = Ratchet::zero(seed);
    let goal = {
        let mut goal = initial.clone();
        goal.inc_by(jumps);
        goal
    };

    let mut iterator = PreviousIterator::new(&initial, &goal, 1_000_000_000).unwrap();

    for _ in 0..previous_steps {
        assert!(iterator.next().is_some());
    }

    // println!("{:#?}", iterator);

    assert_eq!(iterator.step_count(), jumps - previous_steps);
}

#[proptest]
fn prop_ratchet_previous_of_equal_is_none(
    #[strategy(any::<[u8; 32]>().no_shrink())] seed: [u8; 32],
    #[strategy(1..LARGE_EPOCH_LENGTH)] jump: usize,
) {
    let mut initial = Ratchet::zero(seed);
    initial.inc_by(jump);

    let mut iterator = PreviousIterator::new(&initial.clone(), &initial, 1_000).unwrap();

    assert_eq!(iterator.next(), None);
}

#[proptest]
fn prop_ratchet_previous_is_inc_reverse(
    #[strategy(any::<[u8; 32]>().no_shrink())] seed: [u8; 32],
    #[strategy(1..10_000usize)] jump: usize,
) {
    let initial = Ratchet::zero(seed);
    let goal = {
        let mut goal = initial.clone();
        goal.inc_by(jump);
        goal
    };

    let previous_iterator = PreviousIterator::new(&initial, &goal, 1_000_000_000).unwrap();

    let forward_iterator = initial.clone().take(jump - 1);

    let mut forward_collected_reversed = forward_iterator.collect::<Vec<Ratchet>>();
    forward_collected_reversed.reverse();
    forward_collected_reversed.push(initial.clone());

    assert_eq!(
        previous_iterator.collect::<Vec<Ratchet>>(),
        forward_collected_reversed
    );
}
