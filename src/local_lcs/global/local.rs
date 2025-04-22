extern crate alloc;

use core::cmp::Reverse;
use core::ops::Range;

use crate::Permutation;
use alloc::vec;
use alloc::vec::Vec;

#[derive(Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct LocalDistanceOracle {
    h: usize,
    dist: Vec<Vec<usize>>,
}

impl LocalDistanceOracle {
    pub fn new(h: usize, inverse_perm: Permutation) -> Self {
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
        self.dist[x][y - self.start(x)]
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
    fn build(
        a: &LocalDistanceOracle,
        b: &LocalDistanceOracle,
        x: usize,
        mid: Range<usize>,
        ans: &mut [usize],
        shift: usize,
    ) {
        if ans.is_empty() {
            return;
        }

        let t = ans.len() / 2;
        let y = shift + t;

        ans[t] = (mid.start.max(y.saturating_sub(b.height()))..mid.end.min(y + b.height() + 1))
            .max_by_key(|&m| (Reverse(a.ask(x, m) + b.ask(m, y)), m))
            .unwrap();

        Self::build(a, b, x, mid.start..ans[t] + 1, &mut ans[..t], shift);
        Self::build(a, b, x, ans[t]..mid.end, &mut ans[t + 1..], shift + t + 1);
    }

    pub fn new(a: &LocalDistanceOracle, b: &LocalDistanceOracle) -> Self {
        assert_eq!(a.len(), b.len());

        let n = a.len() - 1;
        let h = a.h + b.h;

        let rw: Vec<Vec<usize>> = (0..=n)
            .map(|x| {
                let mut ans = vec![0; n.min(x + h) - (x.saturating_sub(h)) + 1];

                Self::build(
                    a,
                    b,
                    x,
                    x.saturating_sub(a.h)..n.min(x + a.h) + 1,
                    &mut ans,
                    x.saturating_sub(h),
                );

                ans
            })
            .collect();

        Self { h, rw }
    }

    pub fn start(&self, x: usize) -> usize {
        x.saturating_sub(self.height())
    }

    pub fn height(&self) -> usize {
        self.h
    }

    pub fn ask(&self, x: usize, y: usize) -> usize {
        self.rw[x][y - self.start(x)]
    }

    #[allow(dead_code)]
    pub fn len(&self) -> usize {
        self.rw.len()
    }
}
