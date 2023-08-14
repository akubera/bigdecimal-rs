#![allow(clippy::style)]

use std::env;
use std::path::PathBuf;

fn main() {
    let ac = autocfg::new();
    ac.emit_rustc_version(1, 70);

    let env_var = env::var("RUST_BIGDECIMAL_DEFAULT_PRECISION").unwrap_or_else(|_| "100".to_owned());
    println!("cargo:rerun-if-env-changed=RUST_BIGDECIMAL_DEFAULT_PRECISION");

    let outdir = std::env::var_os("OUT_DIR").unwrap();
    let rust_file_path = PathBuf::from(outdir).join("default_precision.rs");

    let default_prec: u32 = env_var
        .parse::<std::num::NonZeroU32>()
        .expect("$RUST_BIGDECIMAL_DEFAULT_PRECISION must be an integer > 0")
        .into();

    let rust_file_contents = format!("const DEFAULT_PRECISION: u64 = {};", default_prec);

    std::fs::write(rust_file_path, rust_file_contents).unwrap();
}