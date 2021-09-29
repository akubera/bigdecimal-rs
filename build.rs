extern crate autocfg;

fn main() {
    let ac = autocfg::new();

    // Support if/match/loop in const functions
    ac.emit_rustc_version(1, 46);
}
