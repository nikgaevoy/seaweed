#[cfg(test)]
extern crate std;
#[cfg(test)]
use std::dbg;

extern crate alloc;
mod mock;

mod jellyfish;
mod local;

use core::cmp::Reverse;
use core::iter::repeat_n;
use core::ops::Bound::Excluded;
use core::ops::Bound::Included;
use core::ops::Bound::Unbounded;
use core::ops::Range;
use core::ops::RangeBounds;

use crate::Permutation;
use alloc::vec;
use alloc::vec::Vec;
use jellyfish::Arm;
use jellyfish::Jellyfish;
use local::LocalDistanceOracle;
use local::RWArray;

#[derive(Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct GlobalDistanceOracle {
    n: usize,
    m: usize,
    w: usize,
    h: usize,
    local: Vec<LocalDistanceOracle>,
    rw: Vec<RWArray>,
    jellyfishes: Vec<Vec<Jellyfish>>,
}

impl GlobalDistanceOracle {
    fn next_waypoint(&self, strip: usize, ax: usize, (bx, by): (usize, usize)) -> usize {
        let shift = self.jellyfishes[strip][ax].ask(&self.rw, (bx, by));
        let h = self.local[strip].height();

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

        #[cfg(test)]
        dbg!(ax, ay);
        #[cfg(test)]
        dbg!(bx, by);

        for s in strips {
            let w = self.next_waypoint(s, x, (bx, by));
            #[cfg(test)]
            dbg!(s, w);
            ans += self.local[s].ask(x, w);
            x = w;
        }

        assert_eq!(x, bx);

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

        let ans = self.distance(source, target);

        #[cfg(test)]
        dbg!(&x, &y, ans);

        x.len() - ans
    }

    pub fn new<T: Eq>(a: &[T], b: &[T]) -> Self {
        let mut rows = antidiagonals(a, b);

        let w = a.len() + b.len();
        let len = rows.len().saturating_sub(1).next_power_of_two();
        rows.resize(len, Permutation::id(w));

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
            w,
            h: len,
            local,
            rw,
            jellyfishes: vec![Default::default(); 2 * len],
        };

        ans.build_jellyfishes();

        #[cfg(test)]
        {
            dbg!(&ans.local);
            dbg!(&ans.rw);
        }

        ans
    }

    fn divide_and_conquer(
        &self,
        positions: &mut [Option<usize>],
        row: usize,
        mut segment: Range<usize>,
        arms: &Vec<Arm>,
        dist: &[usize],
        alive: &[usize],
    ) {
        if segment.is_empty() {
            return;
        }
        if alive.len() == 1 {
            let t = segment.next_back().unwrap();

            if positions[0].is_none_or(|prev| prev < t) {
                positions[0] = Some(t);
            }

            return;
        }

        let t = (segment.start + segment.end) / 2;

        let best = alive
            .iter()
            .copied()
            .enumerate()
            .map(|(ind, val)| {
                (
                    Reverse(dist[val] + self.distance(arms[val].shoulder(), (t, row))),
                    ind,
                )
            })
            .max()
            .unwrap()
            .1;

        if positions[best].is_none_or(|prev| prev < t) {
            positions[best] = Some(t);
        }

        self.divide_and_conquer(
            &mut positions[..=best],
            row,
            segment.start..t,
            arms,
            dist,
            &alive[..=best],
        );
        self.divide_and_conquer(
            &mut positions[best..],
            row,
            t + 1..segment.end,
            arms,
            dist,
            &alive[best..],
        );
    }

    fn build_row(
        &self,
        head: (usize, usize),
        row: usize,
        arms: &Vec<Arm>,
        dist: &[usize],
        alive: &[usize],
    ) -> Vec<Option<usize>> {
        let mut positions = vec![None; alive.len()];

        self.divide_and_conquer(
            &mut positions,
            row,
            head.0.saturating_sub(row - head.1)..self.w.min(head.0 + row - head.1) + 1,
            arms,
            dist,
            alive,
        );

        positions
    }

    fn build_inside_strip(
        &self,
        head: (usize, usize),
        start: usize,
        strip: usize,
        arms: &mut Vec<Arm>,
        dist: &[usize],
        alive: &[usize],
    ) {
        if strip > self.rw.len() {
            return;
        }

        let h = self.local[strip].height() / 2;
        let mid = start + h;

        let positions = self.build_row(head, mid, arms, dist, alive);

        let mut l = 0;

        debug_assert!(positions[0].is_some());

        while let Some(t) = positions[l..].iter().position(|p| p.is_none()) {
            l += t;
            let t = positions[l..]
                .iter()
                .position(|p| p.is_some())
                .unwrap_or(positions[l..].len());

            let r = l + t;
            l -= 1;

            self.build_inside_strip(head, start, 2 * strip, arms, dist, &alive[l..r]);

            l = r;
        }

        let mut long = Vec::new();

        for (ind, pos) in alive.iter().copied().zip(positions.iter().copied()) {
            if let Some(p) = pos {
                arms[ind].push((p, mid));
                long.push(ind);
            }
        }

        self.build_inside_strip(head, start + h, 2 * strip + 1, arms, dist, &long);
    }

    fn build_strip(
        &self,
        head: (usize, usize),
        start: usize,
        strip: usize,
        arms: &mut Vec<Arm>,
        dist: &[usize],
        alive: &mut Vec<usize>,
    ) {
        let row = start + self.local[strip].height();

        let positions = self.build_row(head, row, arms, dist, alive);

        let mut l = 0;

        debug_assert!(positions[0].is_some());

        while let Some(t) = positions[l..].iter().position(|p| p.is_none()) {
            l += t;
            let t = positions[l..]
                .iter()
                .position(|p| p.is_some())
                .unwrap_or(positions[l..].len());

            let r = l + t;
            l -= 1;

            self.build_inside_strip(head, start, strip, arms, dist, &alive[l..r]);

            l = r;
        }

        for (ind, pos) in alive.iter().copied().zip(positions.iter().copied()) {
            if let Some(p) = pos {
                arms[ind].push((p, row));
            }
        }

        let mut iter = positions.into_iter();
        alive.retain(|_| iter.next().is_some());
    }

    fn build_jellyfishes(&mut self) {
        for body in (1..self.local.len()).rev() {
            self.jellyfishes[body] = Vec::with_capacity(self.local[body].len());

            for x in 0..self.local[body].len() {
                let h = self.local[body].height();

                let mut cur = body;
                while cur < self.rw.len() {
                    cur *= 2;
                }
                cur -= self.rw.len();
                let head = (x, cur);
                cur += h;

                let mut arms: Vec<_> = (x.saturating_sub(h)..(x + h).min(self.local[body].len()))
                    .map(|t| Arm::new((t, cur)))
                    .collect();

                let strips = Self::get_strips(h, cur, h);
                let mut alive = (0..=arms.len()).collect();

                for s in strips {
                    self.build_strip(
                        head,
                        cur,
                        s,
                        &mut arms,
                        self.local[s].distances_from(x),
                        &mut alive,
                    );
                    cur += self.local[s].height();
                }

                self.jellyfishes[body].push(Jellyfish::new(arms));
            }
        }
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
