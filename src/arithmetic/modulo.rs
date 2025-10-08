use crate::*;

/// optimized calculation of n % 10
#[allow(dead_code)]
pub(crate) fn mod_ten_uint(n: &BigUint) -> u8 {
    mod_ten_2p64_le(n.iter_u64_digits())
}

/// optimized calculation of n % 10
pub(crate) fn mod_ten_2p64_le(mut digits: impl Iterator<Item = u64>) -> u8 {
    let d0 = digits.next().unwrap_or(0) % 10;
    let mut acc: u64 = digits.map(|d| d % 10).sum();
    acc *= 6;
    acc += d0;
    (acc % 10) as u8
}

/// optimized calculation of n % 100
pub(crate) fn mod_100_uint(n: &BigUint) -> u8 {
    mod_100_2p64_le(n.iter_u64_digits())
}

/// optimized calculation of n % 100
/// TODO: compare implementations: https://rust.godbolt.org/z/Kcxor1MT5
pub(crate) fn mod_100_2p64_le(mut digits: impl Iterator<Item = u64>) -> u8 {
    let mods_2p64 = [16, 56, 96, 36, 76];
    let mut acc_v = [ 0,  0,  0,  0,  0];
    let d0 = digits.next().unwrap_or(0) % 100;

    for (i, d) in digits.enumerate() {
        acc_v[i % 5] += d % 100;
    }

    let mut acc = d0;
    for (&a, m) in acc_v.iter().zip(mods_2p64.iter()) {
        acc += m * (a % 100);
    }
    (acc % 100) as u8
}
