use num::traits::{Euclid, NumAssign, RefNum};
use num::{Integer, Signed};
use std::fmt::Debug;
use std::iter::{IntoIterator, Sum};
use std::mem::replace;
use std::mem::swap;
use std::ops::{Add, Index, Mul};

use permutation::Permutation;

mod permutation;

pub trait AffineIndex:
    Signed + RefNum<Self> + NumAssign + Debug + From<usize> + Into<usize> + Clone + Ord + Sum + Euclid
{
}

impl<
        S: Signed
            + RefNum<Self>
            + NumAssign
            + Debug
            + From<usize>
            + Into<usize>
            + Clone
            + Ord
            + Sum
            + Euclid,
    > AffineIndex for S
{
}

#[derive(Default, Debug, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct AffinePermutation<S: AffineIndex> {
    perm: Vec<S>,
}

impl<S: AffineIndex> AffinePermutation<S> {
    fn is_valid(&self) -> bool {
        let mut tmp = self.perm.clone();
        tmp.sort();
        for i in (0..tmp.len()).skip(1) {
            if tmp[i - 1] == tmp[i] {
                return false;
            }
        }
        true
    }
}

impl<S: AffineIndex> AffinePermutation<S> {
    pub fn id(n: usize) -> Self {
        Self {
            perm: (0..n).map(|x| S::try_from(x).unwrap()).collect(),
        }
    }

    pub fn len(&self) -> usize {
        self.perm.len()
    }

    pub fn lcs(&self, repetitions: S) -> S {
        (0..self.len())
            .map(|index| repetitions.clone().min(self.period_at(index)))
            .sum::<S>()
    }

    pub fn period(&self, value: S) -> S {
        (S::from(self.len()) - S::from(1) - value).div_euclid(&self.len().into())
    }

    pub fn period_at(&self, index: usize) -> S {
        self.period(self.perm[index].clone())
    }

    pub fn recip(&self) -> AffinePermutation<S> {
        let mut perm = vec![0.into(); self.len()];

        for i in 0..self.len() {
            let p = self.period_at(i);
            let shift = p * S::from(self.len());

            let val = S::from(i) + shift.clone();

            perm[(self.perm[i].clone() + shift).into()] = val;
        }

        AffinePermutation { perm }
    }

    pub fn repeat(&self, times: usize) -> Self {
        Self {
            perm: (0..times)
                .flat_map(|k| self.perm.iter().map(move |x| S::from(k * self.len()) + x))
                .collect(),
        }
    }

    fn ends(&self) -> Vec<S> {
        let mut ans = self.perm.clone();
        ans.sort();

        ans
    }
}

impl<S: AffineIndex> Index<usize> for AffinePermutation<S> {
    type Output = S;

    fn index(&self, index: usize) -> &Self::Output {
        &self.perm[index]
    }
}

pub fn solve_one_infty<'a, S: AffineIndex, T: PartialEq + 'a>(
    a: impl IntoIterator<Item = &'a T>,
    b: &[T],
) -> AffinePermutation<S> {
    let mut perm: Vec<_> = (0..b.len()).map(|x| S::from(x)).collect();

    for ch in a.into_iter() {
        if let Some((mut pos, _val)) = b.iter().enumerate().find(|(_ind, val)| ch.eq(val)) {
            let mut horizontal = perm[pos].clone();

            for _i in 0..b.len() {
                pos += 1;
                if pos == b.len() {
                    pos = 0;
                    horizontal -= S::from(b.len());
                }

                if b[pos] == *ch || horizontal > perm[pos] {
                    swap(&mut horizontal, &mut perm[pos]);
                }
            }
        }
    }

    AffinePermutation { perm }
}

impl<S: AffineIndex> From<&AffinePermutation<S>> for Permutation {
    fn from(value: &AffinePermutation<S>) -> Self {
        let mut srt: Vec<_> = value.perm.iter().enumerate().collect();
        srt.sort_by_key(|x| x.1);
        srt.iter()
            .map(|(ind, _)| ind)
            .copied()
            .collect::<Self>()
            .recip()
    }
}

impl<S: AffineIndex, U: Integer + From<u8>> Mul<U> for &AffinePermutation<S> {
    type Output = AffinePermutation<S>;

    fn mul(self, rhs: U) -> Self::Output {
        if rhs.is_zero() {
            AffinePermutation::id(self.len())
        } else if rhs.is_one() {
            self.clone()
        } else {
            if rhs.is_odd() {
                &(self * (rhs - 1.into())) + self
            } else {
                let half = self * (rhs / 2.into());

                &half + &half
            }
        }
    }
}

impl<'a, S: AffineIndex> Add<&AffinePermutation<S>> for &'a AffinePermutation<S> {
    type Output = AffinePermutation<S>;

    fn add(self, rhs: &AffinePermutation<S>) -> Self::Output {
        assert_eq!(self.len(), rhs.len());

        let up = self.repeat(3);
        let down = rhs.repeat(3);

        let rdown = down.recip();

        let starts = up.ends();
        let ends = rdown.ends();

        let a = Permutation::from(&up);
        let rb = Permutation::from(&rdown);
        let b = rb.recip();

        let c = &b + &a;

        let mut ans = vec![S::zero(); self.len()];
        let mut used = vec![false; ans.len()];

        for i in self.len()..2 * self.len() {
            let from = starts[c[rb[i]]].clone();
            let to = ends[rb[i]].clone();

            let ind = to.rem_euclid(&S::from(ans.len()));
            let shift = to - &ind;

            ans[ind.clone().into()] = from - shift;
            debug_assert!(!replace(
                &mut used[ans[ind.into()].rem_euclid(&S::from(ans.len())).into()],
                true,
            ));
        }

        let ans = Self::Output { perm: ans };

        debug_assert!(ans.is_valid());

        ans
    }
}
