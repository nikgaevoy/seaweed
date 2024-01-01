use num::integer::div_rem;
use num::traits::{Euclid, NumAssignRef, NumRef};
use num::{FromPrimitive, Integer, Signed, ToPrimitive};
use std::fmt::Debug;
use std::iter::{IntoIterator, Sum};
use std::mem::replace;
use std::mem::swap;
use std::ops::{Add, Index, Mul};

use permutation::Permutation;

mod permutation;

pub trait AffineIndex:
    Signed + NumRef + NumAssignRef + Debug + FromPrimitive + ToPrimitive + Clone + Ord + Euclid + Sum
{
}

impl<
        S: Signed
            + NumRef
            + NumAssignRef
            + Debug
            + FromPrimitive
            + ToPrimitive
            + Clone
            + Ord
            + Euclid
            + Sum,
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
        tmp.sort_unstable();
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
            perm: (0..n).map(|x| S::from_usize(x).unwrap()).collect(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.perm.is_empty()
    }

    pub fn len(&self) -> usize {
        self.perm.len()
    }

    pub fn braid_period(&self) -> usize {
        let mut z = vec![0; self.len()];

        let mut l = 0;
        let mut r = 0;

        let get = |i| self[i].clone() - S::from_usize(i).unwrap();

        for i in 1..self.len() {
            if i < r {
                z[i] = (r - i).min(z[i - l]);
            }
            while i + z[i] < self.len() && get(z[i]) == get(i + z[i]) {
                z[i] += 1;
            }

            if i + z[i] > r {
                l = i;
                r = i + z[i];
            }

            if i + z[i] == self.len() && self.len() % i == 0 {
                return i;
            }
        }

        self.len()
    }

    pub fn truncate_to_braid_period(&mut self) {
        self.perm.truncate(self.braid_period());
    }

    pub fn shrink_to_fit(&mut self) {
        self.perm.shrink_to_fit();
    }

    fn len_as_s(&self) -> S {
        S::from_usize(self.len()).unwrap()
    }

    fn element_period(&self, value: &S) -> S {
        (S::from_usize(self.len() - 1).unwrap() - value).div_euclid(&self.len_as_s())
    }

    fn element_period_at(&self, index: usize) -> S {
        self.element_period(&self.perm[index])
    }

    pub fn lcs_repeat(&self, repetitions: &S) -> S {
        let mut ans = S::zero();

        for period in self.perm.iter().map(|element| self.element_period(element)) {
            ans += repetitions.min(&period);
        }

        ans
    }

    pub fn recip(&self) -> AffinePermutation<S> {
        let mut perm = vec![S::zero(); self.len()];

        for i in 0..self.len() {
            let p = self.element_period_at(i);
            let shift = p * self.len_as_s();

            let val = S::from_usize(i).unwrap() + &shift;

            perm[(shift + &self.perm[i]).to_usize().unwrap()] = val;
        }

        AffinePermutation { perm }
    }

    pub fn repeat(&self, times: usize) -> Self {
        Self {
            perm: (0..times)
                .flat_map(|k| {
                    self.perm
                        .iter()
                        .map(move |x| S::from_usize(k * self.len()).unwrap() + x)
                })
                .collect(),
        }
    }

    fn ends(&self) -> Vec<S> {
        let mut ans = self.perm.clone();
        ans.sort_unstable();

        ans
    }
}

impl<S: AffineIndex + Integer> AffinePermutation<S> {
    pub fn lcs_len(&self, len: S) -> S {
        let (div, rem) = div_rem(len, self.len_as_s());
        let prefix = rem.to_usize().unwrap();

        let le = S::one() + &div;
        let ri = div;

        (0..prefix)
            .map(|index| le.clone().min(self.element_period_at(index)))
            .chain((prefix..self.len()).map(|index| ri.clone().min(self.element_period_at(index))))
            .sum::<S>()
    }
}

impl<S: AffineIndex> Index<usize> for AffinePermutation<S> {
    type Output = S;

    fn index(&self, index: usize) -> &Self::Output {
        &self.perm[index]
    }
}

pub fn solve_one_infty<'a, S: AffineIndex, T: PartialEq + 'a>(
    vertical: impl IntoIterator<Item = &'a T>,
    repeating: &[T],
) -> AffinePermutation<S> {
    let mut perm: AffinePermutation<S> = AffinePermutation::<S>::id(repeating.len());

    for ch in vertical.into_iter() {
        if let Some((mut pos, _val)) = repeating.iter().enumerate().find(|(_ind, val)| ch.eq(val)) {
            let mut horizontal = perm[pos].clone();

            for _i in 0..repeating.len() {
                pos += 1;
                if pos == repeating.len() {
                    pos = 0;
                    horizontal -= S::from_usize(repeating.len()).unwrap();
                }

                if repeating[pos] == *ch || horizontal > perm[pos] {
                    swap(&mut horizontal, &mut perm.perm[pos]);
                }
            }
        }
    }

    perm
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

impl<S: AffineIndex, U: Integer + FromPrimitive> Mul<U> for &AffinePermutation<S> {
    type Output = AffinePermutation<S>;

    fn mul(self, rhs: U) -> Self::Output {
        if rhs.is_zero() {
            AffinePermutation::<S>::id(self.len())
        } else if rhs.is_one() {
            self.clone()
        } else {
            if rhs.is_odd() {
                &(self * (rhs - U::one())) + self
            } else {
                let half = self * (rhs / U::from_u8(2).unwrap());

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

            let ind = (&to).rem_euclid(&S::from_usize(ans.len()).unwrap());
            let shift = to - &ind;
            let ind = ind.to_usize().unwrap();

            ans[ind] = from - shift;
            debug_assert!(!replace(
                &mut used[ans[ind]
                    .rem_euclid(&S::from_usize(ans.len()).unwrap())
                    .to_usize()
                    .unwrap()],
                true,
            ));
        }

        let ans = Self::Output { perm: ans };

        debug_assert!(ans.is_valid());

        ans
    }
}
