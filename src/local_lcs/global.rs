extern crate alloc;

mod local;

use crate::Permutation;
use alloc::vec;
use alloc::vec::Vec;
use local::LocalDistanceOracle;
use local::RWArray;

#[derive(Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct GlobalDistanceOracle {
    local: Vec<LocalDistanceOracle>,
    rw: Vec<RWArray>,
}

pub fn antidiagonals<T: Eq>(a: &[T], b: &[T]) -> Vec<Permutation> {
    if a.is_empty() || b.is_empty() {
        return vec![];
    }

    let m = a.len() + b.len();
    let mut result = vec![Permutation::id(m); m - 1];

    for i in 0..a.len() {
        for j in 0..b.len() {
            if a[i] != b[j] {
                let ind = i + b.len() - 1 - j;

                result[i + j].swap(ind, ind + 1);
            }
        }
    }

    result
}
