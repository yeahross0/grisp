#![forbid(unsafe_code)]

pub mod compiler;
pub mod eval;
pub mod parser;
pub mod utils;

mod default_environment;
pub use default_environment::default_env;

#[macro_use]
mod macros;

use cfg_if::cfg_if;
cfg_if! {
    if #[cfg(feature = "bigint")] {
        use num_bigint::BigInt;
    }
}

cfg_if! {
    if      #[cfg(feature = "bigint")] { pub type IntType = BigInt; }
    else if #[cfg(feature = "i128")]   { pub type IntType = i128;   }
    else if #[cfg(feature = "i64")]    { pub type IntType = i64;    }
    else if #[cfg(feature = "i16")]    { pub type IntType = i16;    }
    else if #[cfg(feature = "i8")]     { pub type IntType = i8;     }
    else                               {
        /// The underlying type to use for storing lisp integers. Controlled via feature-flags.
        pub type IntType = i32;
    }
}

cfg_if! {
    if #[cfg(feature = "f64")] { pub type FloatType = f64; }
    else                       {
        /// The underlying type to use for storing lisp floats. Controlled via feature-flags.
        pub type FloatType = f32;
    }
}

mod env;
mod errors;
mod lambda;
mod list;
mod symbol;
mod value;

pub use env::Env;
pub use errors::{CompileError, RuntimeError};
pub use lambda::Lambda;
pub use list::ConsIterator;
pub use list::List;
pub use symbol::Symbol;
pub use value::{HashMapRc, NativeFunc, Value};
