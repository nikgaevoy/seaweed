extern crate alloc;

use alloc::vec;
use alloc::vec::Vec;
use core::ops::Range;

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Naive<T: Eq> {
    a: Vec<T>,
    b: Vec<T>,
}

impl<T: Eq> Naive<T> {
    pub fn new(a: Vec<T>, b: Vec<T>) -> Self {
        Self { a, b }
    }

    pub fn query(&self, x: Range<usize>, y: Range<usize>) -> usize {
        lcs(&self.a[x], &self.b[y])
    }
}

pub fn lcs<T: Eq>(a: &[T], b: &[T]) -> usize {
    let mut dp = vec![vec![0; b.len() + 1]; 2];

    for i in 0..a.len() {
        for j in 0..b.len() {
            dp[1][j + 1] = if a[i] == b[j] {
                dp[0][j] + 1
            } else {
                dp[0][j + 1].max(dp[1][j])
            };
        }

        dp.swap(0, 1);
    }

    dp[0][b.len()]
}
