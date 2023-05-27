
// Wrap std:: modules in namespace
#[allow(unused_imports)]
mod stdlib {

    pub use std::{
        cmp,
        convert,
        default,
        fmt,
        hash,
        mem,
        num,
        ops,
        iter,
        str,
        string,
        i8,
        f32,
        f64,
    };


    #[cfg(test)]
    pub use std::collections::hash_map::DefaultHasher;
}
