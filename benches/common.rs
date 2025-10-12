//! common routines to be included by benches

use bigdecimal::BigDecimal;

use std::str::FromStr;

macro_rules! resolve_benchmark_data_file {
    ( $filename:literal ) => {
        concat!(env!("BIGDECIMAL_BENCHMARK_DATA_PATH"), "/", $filename)
    }
}

macro_rules! include_benchmark_data_file {
    ( $filename:literal ) => {{
        include_str!( resolve_benchmark_data_file!($filename) )
    }};
}

/// Collect big-decimals from lines in string
pub fn collect_bigdecimals(src: &str) -> Vec<BigDecimal> {
    src.lines()
       .map(|line| BigDecimal::from_str(&line).unwrap())
       .collect()
}


/// Randomly iterates through items in vector
pub struct RandomIterator<'a, T> {
    v: &'a Vec<T>,
    rng: oorandom::Rand32,
}

impl<'a, T: Copy> RandomIterator<'a, T> {
    pub fn new(v: &'a Vec<T>) -> Self {
        let seed = v.as_ptr() as u64;
        Self::new_with_seed(v, seed)
    }

    pub fn new_with_seed(v: &'a Vec<T>, seed: u64) -> Self {
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
