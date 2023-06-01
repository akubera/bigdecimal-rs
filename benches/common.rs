// to be included by benches
use std::fs::File;
use std::io::BufReader;
use bigdecimal::BigDecimal;

use std::str::FromStr;
use std::io::BufRead;

/// Read vector of big decimals from lines in file
pub fn read_bigdecimals(file: File) -> Vec<BigDecimal> {
    let buf_reader = BufReader::new(file);
    buf_reader
        .lines()
        .map(|maybe_string| maybe_string.unwrap())
        .map(|line| BigDecimal::from_str(&line).unwrap())
        .collect()
}

/// Iterate over vector in random order
pub struct RandomIterator<'a, T> {
    v: &'a Vec<T>,
    rng: oorandom::Rand32,
}

impl<'a, T: Copy> RandomIterator<'a, T> {
    pub fn new(v: &'a Vec<T>) -> Self {
        let seed = v.as_ptr() as u64;
        Self {
            v: v,
            rng: oorandom::Rand32::new(seed),
        }
    }

    pub fn next(&mut self) -> T {
        let randval = self.rng.rand_u32() as usize % self.v.len();
        let idx = randval % self.v.len();
        self.v[idx]
    }
}
