extern crate alloc;

use crate::Permutation;
use alloc::vec;
use alloc::vec::Vec;

#[derive(Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct LocalDistanceOracle {
    h: usize,
    dist: Vec<Vec<usize>>,
}

impl LocalDistanceOracle {
    pub fn new(h: usize, inverse_perm: &Permutation) -> Self {
        let n = inverse_perm.len();

        let mut dist: Vec<Vec<usize>> = (0..=n)
            .map(|x| vec![0; n.min(x + h) - x.saturating_sub(h) + 1])
            .collect();

        for x in 0..=n {
            let start = x.saturating_sub(h);

            for i in 1..dist[x].len() {
                let y = start + i;

                dist[x][i] = dist[x][i - 1] + if inverse_perm[y - 1] >= x { 1 } else { 0 };
            }
        }

        Self { h, dist }
    }

    pub fn start(&self, x: usize) -> usize {
        x.saturating_sub(self.height())
    }

    pub fn height(&self) -> usize {
        self.h
    }

    pub fn len(&self) -> usize {
        self.dist.len()
    }

    pub fn ask(&self, x: usize, y: usize) -> usize {
        self.dist[x][y.saturating_sub(self.start(x))]
    }

    pub fn distances_from(&self, x: usize) -> &[usize] {
        &self.dist[x]
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct RWArray {
    h: usize,
    rw: Vec<Vec<usize>>,
}

impl RWArray {
    pub fn new(h: usize, a_inv: &Permutation, b: &Permutation) -> Self {
        assert_eq!(a_inv.len(), b.len());

        let n = a_inv.len();

        let rw: Vec<Vec<usize>> = (0..n)
            .map(|x| {
                let mid = x.saturating_sub(h)..n.min(x + h);
                let mut bot = mid.start.saturating_sub(h)..n.min(mid.end + h) + 1;

                let shift = bot.start;

                let mut ans = vec![mid.end; bot.len()];

                for i in mid {
                    if a_inv[i] >= x {
                        while bot.start < b[i] {
                            ans[bot.next().unwrap() - shift] = i;
                        }
                    }
                }

                ans
            })
            .collect();

        Self { h: 2 * h, rw }
    }

    pub fn start(&self, x: usize) -> usize {
        x.saturating_sub(self.height())
    }

    pub fn height(&self) -> usize {
        self.h
    }

    pub fn ask(&self, x: usize, y: usize) -> usize {
        self.rw[x][y.saturating_sub(self.start(x))]
    }

    #[allow(dead_code)]
    pub fn len(&self) -> usize {
        self.rw.len()
    }
}
