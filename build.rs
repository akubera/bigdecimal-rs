
extern crate autocfg;


fn main() {
    let ac = autocfg::new();

    // support if/match/loop in const functions
    ac.emit_rustc_version(1, 46);

    // support use of <int-type>::MAX constants
    ac.emit_rustc_version(1, 43);
}
