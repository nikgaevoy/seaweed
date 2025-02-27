#![no_std]

mod affine;
mod permutation;
pub mod local_lcs;

pub use affine::build_affine_permutation;
pub use affine::AffineIndex;
pub use affine::AffinePermutation;
pub use permutation::Permutation;
