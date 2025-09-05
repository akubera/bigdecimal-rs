
// Wrap std:: modules in namespace
#[allow(unused_imports)]
mod stdlib {

    pub use std::{
        cmp,
        convert,
        default,
        fmt,
        hash,
        marker,
        mem,
        num,
        ops,
        iter,
        slice,
        str,
        string,
        f32,
        f64,
    };


    #[cfg(test)]
    pub use std::collections::hash_map::DefaultHasher;

    pub use std::borrow;
    pub use std::boxed::{self, Box};
    pub use std::vec::{self, Vec};
}
