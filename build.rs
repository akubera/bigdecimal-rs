#![allow(clippy::style)]

use std::env;
use std::path::PathBuf;

fn main() {
    let ac = autocfg::new();
    ac.emit_rustc_version(1, 70);

    // Option::zip
    ac.emit_rustc_version(1, 46);

    let outdir: PathBuf = std::env::var_os("OUT_DIR").unwrap().into();
    write_default_precision_file(&outdir);
}


/// Create default_precision.rs, containg definition of constant DEFAULT_PRECISION loaded in src/lib.rs
fn write_default_precision_file(outdir: &PathBuf) {
    let env_var = env::var("RUST_BIGDECIMAL_DEFAULT_PRECISION").unwrap_or_else(|_| "100".to_owned());
    println!("cargo:rerun-if-env-changed=RUST_BIGDECIMAL_DEFAULT_PRECISION");

    let rust_file_path = outdir.join("default_precision.rs");

    let default_prec: u32 = env_var
        .parse::<std::num::NonZeroU32>()
        .expect("$RUST_BIGDECIMAL_DEFAULT_PRECISION must be an integer > 0")
        .into();

    let rust_file_contents = format!("const DEFAULT_PRECISION: u64 = {};", default_prec);

    std::fs::write(rust_file_path, rust_file_contents).unwrap();
}
