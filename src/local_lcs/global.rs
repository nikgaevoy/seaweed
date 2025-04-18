extern crate alloc;
mod mock;

mod jellyfish;
mod local;

use core::iter::repeat_n;
use core::ops::Bound::Excluded;
use core::ops::Bound::Included;
use core::ops::Bound::Unbounded;
use core::ops::Range;
use core::ops::RangeBounds;

use crate::Permutation;
use alloc::vec;
use alloc::vec::Vec;
use jellyfish::Jellyfish;
use local::LocalDistanceOracle;
use local::RWArray;

#[derive(Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct GlobalDistanceOracle {
    n: usize,
    m: usize,
    local: Vec<LocalDistanceOracle>,
    rw: Vec<RWArray>,
    jellyfishes: Vec<Vec<Jellyfish>>,
}

impl GlobalDistanceOracle {
    fn next_waypoint(&self, strip: usize, ax: usize, (bx, by): (usize, usize)) -> usize {
        let shift = self.jellyfishes[strip][ax].ask(&self.rw, (bx, by));
        let h = self.rw[strip].height();

        ax.saturating_sub(h) + shift
    }

    fn get_strips(len: usize, mut l: usize, mut r: usize) -> Vec<usize> {
        l += len;
        r += len;

        let mut left = Vec::new();
        let mut right = Vec::new();

        while l < r {
            if l % 2 != 0 {
                left.push(l);
                l += 1;
            }
            if r % 2 != 0 {
                r -= 1;
                right.push(r);
            }

            l /= 2;
            r /= 2;
        }

        right.reverse();
        left.extend_from_slice(&right[..]);

        left
    }

    fn distance(&self, (ax, ay): (usize, usize), (bx, by): (usize, usize)) -> usize {
        let strips = Self::get_strips(self.rw.len(), ay, by);

        let mut x = ax;
        let mut ans = 0;

        for s in strips {
            let w = self.next_waypoint(s, x, (bx, by));
            ans += self.local[s].ask(x, w);
            x = w;
        }

        ans
    }

    pub fn rotate45(&self, (x, y): (usize, usize)) -> (usize, usize) {
        (self.n - y + x, x + y)
    }

    pub fn ask(&self, x: impl RangeBounds<usize>, y: impl RangeBounds<usize>) -> usize {
        let x = remove_bounds(self.m, x);
        let y = remove_bounds(self.n, y);

        let source = self.rotate45((x.start, y.start));
        let target = self.rotate45((x.end, y.end));

        x.len() - self.distance(source, target)
    }

    pub fn new<T: Eq>(a: &[T], b: &[T]) -> Self {
        let mut rows = antidiagonals(a, b);

        let len = rows.len().saturating_sub(1).next_power_of_two();
        rows.resize(len, Permutation::id(a.len() + b.len()));

        let mut inv_perms: Vec<(Permutation, usize)> = repeat_n((Permutation::default(), 0), len)
            .chain(rows.into_iter().map(|x| (x, 1)))
            .collect();

        for j in (1..len).rev() {
            inv_perms[j].0 = &inv_perms[2 * j + 1].0 + &inv_perms[2 * j].0;
            inv_perms[j].1 = inv_perms[2 * j + 1].1 + inv_perms[2 * j].1;
        }

        let local: Vec<_> = inv_perms
            .into_iter()
            .map(|(perm, h)| LocalDistanceOracle::new(h, perm))
            .collect();

        let rw = (0..len)
            .map(|i| {
                if i == 0 {
                    Default::default()
                } else {
                    RWArray::new(&local[2 * i], &local[2 * i + 1])
                }
            })
            .collect();

        let mut ans = Self {
            n: b.len(),
            m: a.len(),
            local,
            rw,
            jellyfishes: vec![Default::default(); 2 * len],
        };

        ans.build_jellyfishes();

        ans
    }

    fn build_jellyfishes(&mut self) {
        todo!()
    }
}

fn remove_bounds(n: usize, range: impl RangeBounds<usize>) -> Range<usize> {
    let start = match range.start_bound() {
        Included(&x) => x,
        Excluded(&x) => x + 1,
        Unbounded => 0,
    };

    let end = match range.start_bound() {
        Included(&x) => x + 1,
        Excluded(&x) => x,
        Unbounded => n,
    };

    start..end
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
