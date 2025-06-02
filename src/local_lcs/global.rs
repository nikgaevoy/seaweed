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
#[cfg(test)]
use crate::TikzPicture;
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
        self.jellyfishes[strip][ax].ask(&self.rw, (bx, by))
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

    fn is_reachable((ax, ay): (usize, usize), (bx, by): (usize, usize)) -> bool {
        ay <= by && bx <= ax + (by - ay)
    }

    fn distance(&self, (ax, ay): (usize, usize), (bx, by): (usize, usize)) -> usize {
        assert!(Self::is_reachable((ax, ay), (bx, by)));
        assert!(bx <= self.w && ax <= self.w);
        assert!(by <= self.h);

        let strips = Self::get_strips(self.rw.len(), ay, by);

        let mut x = ax;
        let mut ans = 0;

        #[cfg(test)]
        {
            // dbg!(ax, ay);
            // dbg!(bx, by);
        }

        for s in strips {
            let w = self.next_waypoint(s, x, (bx, by));
            #[cfg(test)]
            {
                // dbg!(s, w);
                // dbg!(&self.local[s].height());
                // dbg!(&self.jellyfishes[s][x]);
            }
            ans += self.local[s].ask(x, w);
            x = w;
        }

        assert!(bx <= x);

        ans
    }

    pub fn rotate45(&self, (x, y): (usize, usize)) -> (usize, usize) {
        (self.n - x + y, x + y)
    }

    pub fn ask(&self, x: impl RangeBounds<usize>, y: impl RangeBounds<usize>) -> usize {
        let x = remove_bounds(self.n, x);
        let y = remove_bounds(self.m, y);

        let source = self.rotate45((x.start, y.start));
        let target = self.rotate45((x.end, y.end));

        let ans = self.distance(source, target);

        #[cfg(test)]
        dbg!(&x, &y, ans);

        y.len() - ans
    }

    fn build_permutations(
        w: usize,
        mut antidiagonals: Vec<Permutation>,
    ) -> Vec<(Permutation, Permutation, usize)> {
        let len = antidiagonals.len().next_power_of_two();
        antidiagonals.resize(len, Permutation::id(w));

        let mut perms: Vec<(Permutation, Permutation, usize)> =
            repeat_n((Permutation::default(), Permutation::default(), 0), len)
                .chain(antidiagonals.into_iter().map(|x| {
                    let r = x.recip();

                    (x, r, 1)
                }))
                .collect();

        for j in (1..len).rev() {
            perms[j].0 = &perms[2 * j].0 + &perms[2 * j + 1].0;
            perms[j].1 = perms[j].0.recip();
            perms[j].2 = perms[2 * j].2 + perms[2 * j + 1].2;
        }

        perms
    }

    fn build_local(perms: &Vec<(Permutation, Permutation, usize)>) -> Vec<LocalDistanceOracle> {
        perms
            .iter()
            .map(|(_perm, perm_inv, h)| LocalDistanceOracle::new(*h, perm_inv))
            .collect()
    }

    fn build_rw(perms: &Vec<(Permutation, Permutation, usize)>) -> Vec<RWArray> {
        (0..perms.len() / 2)
            .map(|i| {
                if i == 0 {
                    Default::default()
                } else {
                    let ans = RWArray::new(perms[2 * i].2, &perms[2 * i].1, &perms[2 * i + 1].0);

                    #[cfg(test)]
                    if perms[2 * i].2 == 2 {
                        dbg!(&perms[2 * i], &perms[2 * i + 1], &ans);
                    }

                    ans
                }
            })
            .collect()
    }

    fn build_local_oracles<T: Eq>(a: &[T], b: &[T]) -> Self {
        let w = a.len() + b.len();

        let antidiagonals = antidiagonals(a, b);

        let perms = Self::build_permutations(w, antidiagonals);
        let local = Self::build_local(&perms);
        let rw = Self::build_rw(&perms);

        #[cfg(test)]
        {
            let mut l = rw.len();
            let mut r = perms.len();
            let mut step = 1;

            while l < r {
                let mut pic = TikzPicture::new();

                let mut pos = 0;

                for t in l..r {
                    let top = pos as f32;
                    let bot = (pos + step) as f32;
                    pic.draw(&perms[t].0, top, bot, "black");
                    if t % 2 == 0 {
                        pic.draw(&rw[t / 2], top, (pos + 2 * step) as f32, "green");
                    }
                    pos += step;
                }

                l /= 2;
                r /= 2;
                step *= 2;

                extern crate std;
                std::eprintln!("{}", pic.to_string());
            }
        }

        let len = rw.len();

        Self {
            n: a.len(),
            m: b.len(),
            w,
            h: len,
            local,
            rw,
            jellyfishes: vec![Default::default(); 2 * len],
        }
    }

    pub fn new<T: Eq>(a: &[T], b: &[T]) -> Self {
        Self::build_seminaive(a, b)
    }

    fn build_seminaive<T: Eq>(a: &[T], b: &[T]) -> Self {
        let mut ans = Self::build_naive(a, b);

        for j in ans.jellyfishes.iter_mut().flatten().rev() {
            j.check_consistency(&ans.rw);
            j.retain_canonical_landmarks();
        }

        ans
    }

    fn build_naive<T: Eq>(a: &[T], b: &[T]) -> Self {
        let mut ans = Self::build_local_oracles(a, b);

        ans.build_naive_jellyfishes();

        ans
    }

    fn divide_and_conquer(
        &self,
        positions: &mut [Option<usize>],
        shoulder_row: usize,
        shoulders: &[(usize, usize)],
        row: usize,
        mut segment: Range<usize>,
    ) {
        if segment.is_empty() {
            return;
        }
        if shoulders.len() == 1 {
            let t = segment.next_back().unwrap();

            if positions[0].is_none_or(|prev| prev < t) {
                positions[0] = Some(t);
            }

            return;
        }

        let t = (segment.start + segment.end) / 2;

        let best = shoulders
            .iter()
            .copied()
            .enumerate()
            .filter_map(|(ind, (pos, dist))| {
                let wp = (pos, shoulder_row);

                if Self::is_reachable(wp, (t, row)) {
                    Some((Reverse(dist + self.distance(wp, (t, row))), ind))
                } else {
                    None
                }
            })
            .max()
            .unwrap()
            .1;

        if positions[best].is_none_or(|prev| prev < t) {
            positions[best] = Some(t);
        }

        self.divide_and_conquer(
            &mut positions[..=best],
            shoulder_row,
            &shoulders[..=best],
            row,
            segment.start..t,
        );
        self.divide_and_conquer(
            &mut positions[best..],
            shoulder_row,
            &shoulders[best..],
            row,
            t + 1..segment.end,
        );
    }

    fn build_row(
        &self,
        shoulder_row: usize,
        shoulders: &[(usize, usize)],
        row: usize,
    ) -> Vec<Option<usize>> {
        let mut positions = vec![None; shoulders.len()];

        self.divide_and_conquer(
            &mut positions,
            shoulder_row,
            shoulders,
            row,
            0..self.w.min(shoulders.last().unwrap().0 + row - shoulder_row) + 1,
        );

        positions
    }

    fn build_naive_jellyfishes(&mut self) {
        for shoulder_row in (1..=self.h).rev() {
            let mut body = shoulder_row + self.rw.len() - 1;

            while body > 0 {
                let h = self.local[body].height();

                self.jellyfishes[body] = Vec::with_capacity(self.local[body].len());

                for x in 0..self.local[body].len() {
                    let head = (x, shoulder_row - h);

                    if head == (2, 2) {
                        #[cfg(test)]
                        {
                            dbg!("here");
                        }
                    }

                    let mut shoulders = Vec::with_capacity(h + 1);

                    let dist = self.local[body].distances_from(x);

                    for j in 0..dist.len().saturating_sub(1) {
                        if dist[j] < dist[j + 1] {
                            shoulders.push((self.local[body].start(x) + j, dist[j]));
                        }
                    }
                    shoulders.push((
                        self.local[body].start(x) + dist.len() - 1,
                        *dist.last().unwrap(),
                    ));

                    let mut arms: Vec<_> = shoulders
                        .iter()
                        .map(|(j, _d)| Arm::new((*j, shoulder_row)))
                        .collect();

                    for r in shoulder_row + 1..=self.h {
                        let positions = self.build_row(shoulder_row, &shoulders, r);

                        for (p, arm) in positions
                            .into_iter()
                            .zip(arms.iter_mut())
                            .filter(|(p, _arm)| p.is_some())
                        {
                            arm.push((p.unwrap(), r));
                        }
                    }

                    self.jellyfishes[body].push(Jellyfish::new(head, arms));
                }

                if body % 2 == 0 {
                    break;
                } else {
                    body /= 2;
                }
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

    let end = match range.end_bound() {
        Included(&x) => x + 1,
        Excluded(&x) => x,
        Unbounded => n,
    };

    start..end
}

pub fn antidiagonals<T: Eq>(a: &[T], b: &[T]) -> Vec<Permutation> {
    let h = a.len() + b.len();
    let mut result = vec![Permutation::id(h); h];

    for i in 0..a.len() {
        for j in 0..b.len() {
            if a[i] != b[j] {
                let ind = a.len() - 1 - i + j;

                result[i + j].swap(ind, ind + 1);
            }
        }
    }

    result
}
