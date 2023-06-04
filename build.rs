
use std::env;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;

fn main() -> std::io::Result<()> {
    let outdir = match std::env::var_os("OUT_DIR") {
        None => return Ok(()),
        Some(outdir) => outdir,
    };
    let outdir_path = PathBuf::from(outdir);

    write_default_precision(&outdir_path, "default_precision.rs")?;
    Ok(())
}

/// Create default_precision.rs, containg definition of constant DEFAULT_PRECISION
fn write_default_precision(outdir_path: &PathBuf, filename: &str) -> std::io::Result<()>
{

    let default_prec = env::var("RUST_BIGDECIMAL_DEFAULT_PRECISION")
        .map(|s| s.parse::<std::num::NonZeroU32>().expect("$RUST_BIGDECIMAL_DEFAULT_PRECISION must be an integer > 0"))
        .map(|nz_num| nz_num.into())
        .unwrap_or(100u32);

    let default_precision_rs_path = outdir_path.join(filename);

    let mut default_precision_rs = File::create(&default_precision_rs_path).expect("Could not create default_precision.rs");
    write!(default_precision_rs, "const DEFAULT_PRECISION: u64 = {};", default_prec)?;

    println!("cargo:rerun-if-changed={}", default_precision_rs_path.display());
    println!("cargo:rerun-if-env-changed={}", "RUST_BIGDECIMAL_DEFAULT_PRECISION");

    Ok(())
}
