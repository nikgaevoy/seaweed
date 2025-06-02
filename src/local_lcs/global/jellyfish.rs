extern crate alloc;

use core::cmp::Ordering;
use core::cmp::Ordering::{Equal, Greater, Less};

use alloc::vec;
use alloc::vec::Vec;

#[derive(Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Arm {
    landmarks: Vec<(usize, usize)>,
}

impl Arm {
    pub fn new(root: (usize, usize)) -> Self {
        Self {
            landmarks: vec![root],
        }
    }

    pub fn push(&mut self, landmark: (usize, usize)) {
        debug_assert!(self
            .landmarks
            .last()
            .is_none_or(|prev| { prev.1 < landmark.1 && (landmark.1 - prev.1).is_power_of_two() }));

        self.landmarks.push(landmark);
    }

    pub fn shoulder(&self) -> (usize, usize) {
        self.landmarks.first().copied().unwrap()
    }

    pub fn intercept(&self) -> (usize, usize) {
        self.landmarks.last().copied().unwrap()
    }

    fn get(&self, rw: &Vec<RWArray>, y: usize) -> usize {
        match self.landmarks.binary_search_by(|(_lx, ly)| ly.cmp(&y)) {
            Ok(ind) => self.landmarks[ind].0,
            Err(ind) => {
                assert!(0 < ind && ind < self.landmarks.len());

                let (mut ax, mut ay) = self.landmarks[ind - 1];
                let (mut bx, mut by) = self.landmarks[ind];

                let mut strip = (ay + rw.len()) >> (by - ay).trailing_zeros();

                loop {
                    let ty = (ay + by) / 2;
                    let tx = rw[strip].ask(ax, bx);

                    match y.cmp(&ty) {
                        Less => {
                            strip *= 2;
                            bx = tx;
                            by = ty;
                        }
                        Equal => {
                            break tx;
                        }
                        Greater => {
                            strip = 2 * strip + 1;
                            ax = tx;
                            ay = ty;
                        }
                    }
                }
            }
        }
    }

    pub fn retain_canonical_landmarks(&mut self) {
        let mut l = self.shoulder().1;
        let mut r = self.intercept().1;

        for j in 1..self.landmarks.len() {
            assert_eq!(self.landmarks[j - 1].1 + 1, self.landmarks[j].1);
            assert!(self.landmarks[j - 1].0.abs_diff(self.landmarks[j].0) <= 1);
        }

        let mut left = Vec::new();
        let mut right = Vec::new();

        for lvl in 0.. {
            if l == r {
                left.push(l);

                break;
            }

            let step = 1 << lvl;

            if l & step != 0 {
                left.push(l);
                l += step;
            }
            if r & step != 0 {
                right.push(r);
                r -= step;
            }
        }

        left.extend(right.into_iter().rev());
        let mut iter = left.into_iter().peekable();

        self.landmarks
            .retain(|(_x, y)| iter.next_if_eq(y).is_some());
    }

    fn get_full_path(&self, rw: &[RWArray]) -> Self {
        fn dfs<const REV: bool>(
            ans: &mut Vec<(usize, usize)>,
            l: (usize, usize),
            r: (usize, usize),
            rw: &[RWArray],
            ind: usize,
        ) {
            if ind >= rw.len() {
                return;
            }

            let mid = (rw[ind].ask(l.0, r.0), (l.1 + r.1) / 2);

            if !REV {
                dfs::<REV>(ans, l, mid, rw, 2 * ind);
                ans.push(mid);
                dfs::<REV>(ans, mid, r, rw, 2 * ind + 1);
            } else {
                dfs::<REV>(ans, mid, r, rw, 2 * ind + 1);
                ans.push(mid);
                dfs::<REV>(ans, l, mid, rw, 2 * ind);
            }
        }

        let mut left = vec![];
        let mut right = vec![];

        let mut l = self.shoulder().1 + rw.len();
        let mut r = self.intercept().1 + rw.len();

        let mut slice = self.landmarks.as_slice();

        while l < r {
            if l % 2 != 0 {
                let a = slice[0];
                let b = slice[1];
                slice = &slice[1..];

                left.push(a);

                dfs::<false>(&mut left, a, b, rw, l);

                l += 1;
            }
            if r % 2 != 0 {
                r -= 1;

                let b = slice.last().copied().unwrap();
                slice = &slice[..slice.len() - 1];
                let a = slice.last().copied().unwrap();

                left.push(b);

                dfs::<true>(&mut right, a, b, rw, r);
            }

            l /= 2;
            r /= 2;
        }

        assert_eq!(slice.len(), 1);
        left.push(slice[0]);
        left.extend(right.into_iter().rev());

        Self { landmarks: left }
    }

    fn cmp(&self, rw: &Vec<RWArray>, (x, y): (usize, usize)) -> Ordering {
        self.get(rw, y).cmp(&x).then(Greater)
    }
}

use super::local::RWArray;
use super::mock::MockPersistentSet;

#[derive(Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Jellyfish {
    head: (usize, usize),
    arms: Vec<Arm>,
    versions: Vec<usize>,
    intercepts: Vec<MockPersistentSet>,
}

impl Jellyfish {
    pub fn ask(&self, rw: &Vec<RWArray>, (x, y): (usize, usize)) -> usize {
        let ver = self.versions.binary_search(&y).unwrap_or_else(|i| i - 1);

        let ind = self.intercepts[ver]
            .binary_search_by(|&index| {
                let arm = &self.arms[index];

                arm.cmp(rw, (x, y))
            })
            .unwrap_err();

        self.arms[*self.intercepts[ver].get(ind).unwrap()]
            .shoulder()
            .0
    }

    pub fn retain_canonical_landmarks(&mut self) {
        for a in &mut self.arms {
            a.retain_canonical_landmarks();
        }
    }

    pub fn check_consistency(&self, rw: &[RWArray]) {
        for a in &self.arms {
            let mut b = a.clone();
            b.retain_canonical_landmarks();

            if b.landmarks == [(2, 3), (3, 4), (4, 8)] {
                b.get_full_path(rw);
            }

            let c = b.get_full_path(rw);

            assert_eq!(&c, a, "{:?}\n{:?}", &self, &b.landmarks);
        }
    }

    pub fn new(head: (usize, usize), arms: Vec<Arm>) -> Self {
        let mut deaths: Vec<_> = arms
            .iter()
            .enumerate()
            .map(|(ind, arm)| (arm.intercept().1, ind))
            .collect();
        deaths.sort();

        let mut set = MockPersistentSet::from_iter(0..deaths.len());
        let mut versions = vec![0];
        let mut intercepts = vec![set.clone()];

        let mut l = 0;

        while l < deaths.len() {
            let r = l + deaths[l..]
                .iter()
                .position(|&(y, _)| y != deaths[l].0)
                .unwrap_or(deaths[l..].len());

            for &(_, i) in &deaths[l..r] {
                set = set.remove(i);
            }

            versions.push(deaths[l].0 + 1);
            intercepts.push(set.clone());

            l = r;
        }

        Self {
            head,
            intercepts,
            arms,
            versions,
        }
    }
}
