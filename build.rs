
use std::env;
use std::path::{Path, PathBuf};


fn main() {
    let ac = autocfg::new();
    ac.emit_rustc_version(1, 70);

    // Option::zip
    ac.emit_rustc_version(1, 46);

    // Remove this comment if enabled proptests
    // ::PROPERTY-TESTS:: autocfg::emit("property_tests");

    let outdir: PathBuf = std::env::var_os("OUT_DIR").unwrap().into();
    write_default_precision_file(&outdir);
    write_default_rounding_mode(&outdir);
}


/// Create default_precision.rs, containing definition of constant DEFAULT_PRECISION loaded in src/lib.rs
fn write_default_precision_file(outdir: &Path) {
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

/// Create default_rounding_mode.rs, using value of RUST_BIGDECIMAL_DEFAULT_ROUNDING_MODE environment variable
fn write_default_rounding_mode(outdir: &Path) {
    let rounding_mode_name = env::var("RUST_BIGDECIMAL_DEFAULT_ROUNDING_MODE").unwrap_or_else(|_| "HalfEven".to_owned());
    println!("cargo:rerun-if-env-changed=RUST_BIGDECIMAL_DEFAULT_ROUNDING_MODE");

    let rust_file_path = outdir.join("default_rounding_mode.rs");
    let rust_file_contents = format!("const DEFAULT_ROUNDING_MODE: RoundingMode = RoundingMode::{};", rounding_mode_name);

    std::fs::write(rust_file_path, rust_file_contents).unwrap();
}
