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
        self.landmarks.push(landmark);
    }

    pub fn shoulder(&self) -> (usize, usize) {
        self.landmarks[0]
    }

    pub fn intercept(&self) -> (usize, usize) {
        self.landmarks.last().copied().unwrap()
    }

    fn get(&self, rw: &Vec<RWArray>, y: usize) -> usize {
        match self.landmarks.binary_search_by(|(_lx, ly)| y.cmp(ly)) {
            Ok(ind) => self.landmarks[ind].0,
            Err(ind) => {
                assert!(ind < self.landmarks.len());

                let (mut ax, mut ay) = self.landmarks[ind];
                let (mut bx, mut by) = self.landmarks[ind + 1];

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

    fn cmp(&self, rw: &Vec<RWArray>, (x, y): (usize, usize)) -> Ordering {
        self.get(rw, y).cmp(&x).then(Greater)
    }
}

use super::local::RWArray;
use super::mock::MockPersistentSet;

#[derive(Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Jellyfish {
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

        self.intercepts[ver]
            .get(ind)
            .copied()
            .unwrap_or(self.arms.len())
    }

    pub fn new(arms: Vec<Arm>) -> Self {
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

        Self { intercepts, arms, versions }
    }
}
