use sha3::{Digest, Sha3_256};

pub(crate) fn hash_32(d: [u8; 32]) -> [u8; 32] {
    let mut hasher = Sha3_256::new();
    hasher.update(d);
    let result_vec = hasher.finalize().to_vec();
    let mut arr = [0; 32];
    for (i, byte) in result_vec.iter().enumerate() {
        arr[i] = *byte;
    }
    arr
}

pub(crate) fn hash_32_n(mut d: [u8; 32], n: u8) -> [u8; 32] {
    for _ in 0..n {
        d = hash_32(d);
    }
    d
}

pub(crate) fn xor(a: [u8; 32], b: [u8; 32]) -> [u8; 32] {
    let mut c: [u8; 32] = [0; 32];
    for (i, (a_byte, b_byte)) in a.iter().zip(b.iter()).enumerate() {
        c[i] = a_byte ^ b_byte;
    }
    c
}

pub(crate) fn compliment(d: [u8; 32]) -> [u8; 32] {
    let mut e: [u8; 32] = [0; 32];
    for (i, d_byte) in d.iter().enumerate() {
        e[i] = !d_byte;
    }
    e
}
