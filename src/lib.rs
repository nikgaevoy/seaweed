#![no_std]

mod affine;
pub mod local_lcs;
mod permutation;

pub use affine::build_affine_permutation;
pub use affine::AffineIndex;
pub use affine::AffinePermutation;
pub use permutation::Permutation;
