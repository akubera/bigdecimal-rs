use std::env;
use std::path::{Path, PathBuf};

// configuration defaults
const DEFAULT_PRECISION: &str = "100";
const DEFAULT_ROUNDING_MODE: &str = "HalfEven";
const EXPONENTIAL_FORMAT_THRESHOLD: &str = "5";
const EXPONENTIAL_FORMAT_UPPER_THRESHOLD: &str = "12";


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
    write_exponential_format_threshold_file(&outdir);
}

/// Loads the environment variable string or default
macro_rules! load_env {
    ($env:ident, $name:literal, $default:ident) => {{
        println!("cargo:rerun-if-env-changed={}", $name);
        $env::var($name).unwrap_or_else(|_| $default.to_owned())
    }};
}

/// Create default_precision.rs, containing definition of constant DEFAULT_PRECISION loaded in src/lib.rs
fn write_default_precision_file(outdir: &Path) {
    let env_var = load_env!(env, "RUST_BIGDECIMAL_DEFAULT_PRECISION", DEFAULT_PRECISION);
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
    let rounding_mode_name = load_env!(env, "RUST_BIGDECIMAL_DEFAULT_ROUNDING_MODE", DEFAULT_ROUNDING_MODE);

    let rust_file_path = outdir.join("default_rounding_mode.rs");
    let rust_file_contents = format!("const DEFAULT_ROUNDING_MODE: RoundingMode = RoundingMode::{};", rounding_mode_name);

    std::fs::write(rust_file_path, rust_file_contents).unwrap();
}

/// Create write_default_rounding_mode.rs, containing definition of constant EXPONENTIAL_FORMAT_THRESHOLD loaded in src/impl_fmt.rs
fn write_exponential_format_threshold_file(outdir: &Path) {
    let low_value = load_env!(env, "RUST_BIGDECIMAL_EXPONENTIAL_FORMAT_THRESHOLD", EXPONENTIAL_FORMAT_THRESHOLD);
    let high_value = load_env!(env, "RUST_BIGDECIMAL_EXPONENTIAL_FORMAT_UPPER_THRESHOLD", EXPONENTIAL_FORMAT_UPPER_THRESHOLD);

    let low_value: u32 = low_value
        .parse::<std::num::NonZeroU32>()
        .expect("$RUST_BIGDECIMAL_EXPONENTIAL_FORMAT_THRESHOLD must be an integer > 0")
        .into();

    let high_value: u32 = high_value
        .parse::<u32>()
        .expect("$RUST_BIGDECIMAL_EXPONENTIAL_FORMAT_UPPER_THRESHOLD must be valid u32");

    let rust_file_path = outdir.join("exponential_format_threshold.rs");

    let rust_file_contents = [
        format!("const EXPONENTIAL_FORMAT_LEADING_ZERO_THRESHOLD: usize = {};", low_value),
        format!("const EXPONENTIAL_FORMAT_TRAILING_ZERO_THRESHOLD: usize = {};", high_value),
    ];

    std::fs::write(rust_file_path, rust_file_contents.join("\n")).unwrap();
}
