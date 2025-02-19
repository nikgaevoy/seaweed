extern crate alloc;

use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::fmt::Debug;
use core::hash::{Hash, Hasher};
use core::iter::{IntoIterator, Sum};
#[cfg(test)]
use core::mem::replace;
use core::mem::swap;
use core::ops::{Add, Index, Mul, Range};
use num::integer::div_rem;
use num::traits::{Euclid, NumAssignRef, NumRef};
use num::{FromPrimitive, Integer, Signed, ToPrimitive};

pub use crate::Permutation;

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

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, Eq)]
pub struct AffinePermutation<S: AffineIndex> {
    perm: Vec<S>,
}

impl<S: AffineIndex + Hash> Hash for AffinePermutation<S> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.perm[0..self.period()].hash(state)
    }
}

impl<S: AffineIndex> PartialEq for AffinePermutation<S> {
    fn eq(&self, other: &Self) -> bool {
        self.perm[0..self.period()] == other.perm[0..other.period()]
    }
}

impl<S: AffineIndex> PartialOrd for AffinePermutation<S> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<S: AffineIndex> Ord for AffinePermutation<S> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.perm[0..self.period()].cmp(&other.perm[0..other.period()])
    }
}

impl<S: AffineIndex> Default for AffinePermutation<S> {
    fn default() -> Self {
        Self {
            perm: Vec::default(),
        }
    }
}

impl<S: AffineIndex> AffinePermutation<S> {
    /// Constructs an empty AffinePermutation.
    pub fn new() -> Self {
        Default::default()
    }

    /// Constructs an identity affine permutation of a given length.
    pub fn id(n: usize) -> Self {
        Self {
            perm: (0..n).map(|x| S::from_usize(x).unwrap()).collect(),
        }
    }

    /// Returns the number of elements in the stored period.
    /// Note that this could be not the shortest possible period.
    /// For the shortest period see the [`period`] method.
    /// Works in constant time.
    ///
    /// # Examples
    /// ```
    /// # use seaweed::AffinePermutation;
    /// # fn main() {
    /// assert_eq!(AffinePermutation::<isize>::id(7).len(), 7);
    /// # }
    /// ```
    ///
    /// [`period`]: AffinePermutation::period
    pub fn len(&self) -> usize {
        self.perm.len()
    }

    /// Returns `true` if the permutation contains no elements.
    pub fn is_empty(&self) -> bool {
        self.perm.is_empty()
    }

    /// Computes smallest period of an affine permutation.
    /// Note that this is different from the [`len`] method because the period could be repeated several times.
    /// Works in linear time.
    ///
    /// # Examples
    /// ```
    /// # use seaweed::AffinePermutation;
    /// # fn main() {
    /// assert_eq!(AffinePermutation::<isize>::id(10).period(), 1);
    /// # }
    /// ```
    ///
    /// [`len`]: AffinePermutation::len
    pub fn period(&self) -> usize {
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

    /// Shortens the affine permutation to the smallest period.
    pub fn truncate_to_period(&mut self) {
        self.perm.truncate(self.period());
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

    /// Constructs inverse permutation.
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

    /// Builds an equivalent permutation by repeating the period given number of times.
    ///
    /// # Examples
    ///
    /// ```
    /// # use seaweed::AffinePermutation;
    /// # fn repeat_test() {
    /// assert_eq!(AffinePermutation::<isize>::id(3).repeat(2).len(), 6);
    /// # }
    /// ```
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

    #[cfg(test)]
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

    #[allow(unused_variables)]
    pub fn lcs_range(&self, range: Range<S>) -> S {
        todo!()
    }
}

impl<S: AffineIndex> Index<usize> for AffinePermutation<S> {
    type Output = S;

    fn index(&self, index: usize) -> &Self::Output {
        &self.perm[index]
    }
}

pub fn build_affine_permutation<'a, S: AffineIndex, T: PartialEq + 'a>(
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
        let mut perm: Vec<_> = (0..value.len()).collect();
        perm.sort_unstable_by_key(|x| &value.perm[*x]);

        Self { perm }.recip()
    }
}

impl<S: AffineIndex, U: Integer + FromPrimitive> Mul<U> for &AffinePermutation<S> {
    type Output = AffinePermutation<S>;

    fn mul(self, rhs: U) -> Self::Output {
        if rhs.is_zero() {
            AffinePermutation::<S>::id(self.len())
        } else if rhs.is_one() {
            self.clone()
        } else if rhs.is_odd() {
            &(self * (rhs - U::one())) + self
        } else {
            let half = self * (rhs / U::from_u8(2).unwrap());

            &half + &half
        }
    }
}

fn the_algorithm<S: AffineIndex>(
    lhs: &AffinePermutation<S>,
    rhs: &AffinePermutation<S>,
) -> AffinePermutation<S> {
    let up = lhs.repeat(3);
    let down = rhs.repeat(3);

    let rdown = down.recip();

    let starts = up.ends();
    let ends = rdown.ends();

    let a = Permutation::from(&up);
    let rb = Permutation::from(&rdown);
    let b = rb.recip();

    let c = &b + &a;

    let mut ans = vec![S::zero(); lhs.len()];

    #[cfg(test)]
    let mut used = vec![false; ans.len()];

    for i in lhs.len()..2 * lhs.len() {
        let from = starts[c[rb[i]]].clone();
        let to = ends[rb[i]].clone();

        let ind = to.rem_euclid(&S::from_usize(ans.len()).unwrap());
        let shift = to - &ind;
        let ind = ind.to_usize().unwrap();

        ans[ind] = from - shift;

        #[cfg(test)]
        debug_assert!(!replace(
            &mut used[ans[ind]
                .rem_euclid(&S::from_usize(ans.len()).unwrap())
                .to_usize()
                .unwrap()],
            true,
        ));
    }

    let ans = AffinePermutation { perm: ans };

    #[cfg(test)]
    debug_assert!(ans.is_valid());

    ans
}

impl<'a, S: AffineIndex> Add<&AffinePermutation<S>> for &'a AffinePermutation<S> {
    type Output = AffinePermutation<S>;

    fn add(self, rhs: &AffinePermutation<S>) -> Self::Output {
        assert_eq!(self.len(), rhs.len());

        the_algorithm(self, rhs)
    }
}

#[cfg(test)]
mod test {
    extern crate alloc;
    extern crate std;

    use alloc::vec::Vec;
    use std::collections::hash_map::DefaultHasher;

    use crate::{build_affine_permutation, AffinePermutation};
    use core::hash::{Hash, Hasher};
    use rand::rngs::ThreadRng;
    use rand::{thread_rng, Rng};

    fn calculate_hash<T: Hash>(t: &T) -> u64 {
        let mut s = DefaultHasher::new();
        t.hash(&mut s);
        s.finish()
    }

    #[test]
    fn test_ord_and_hash() {
        assert_eq!(
            AffinePermutation::<isize>::id(3),
            AffinePermutation::<isize>::id(4)
        );
        assert_eq!(
            calculate_hash(&AffinePermutation::<isize>::id(5)),
            calculate_hash(&AffinePermutation::<isize>::id(6)),
        );

        let a: AffinePermutation<isize> = build_affine_permutation(b"ABAC", b"AABBAAC");

        let a_repeated = a.repeat(5);

        assert_eq!(&a, &a_repeated);
        assert_eq!(calculate_hash(&a), calculate_hash(&a_repeated));

        let a_doubled = &a * 2u8;

        assert_ne!(&a, &a_doubled);
    }

    fn random_perm(rng: &mut ThreadRng, n: usize, shift: i128) -> AffinePermutation<i128> {
        let mut perm: Vec<_> = (0..n)
            .map(|x| x as i128 + rng.gen_range(-shift..=0) * n as i128)
            .collect();

        for i in 0..perm.len() {
            perm.swap(rng.gen_range(0..=i), i);
        }

        AffinePermutation { perm }
    }

    #[test]
    fn equivalence_on_random_tests() {
        let mut rng = thread_rng();

        for n in [3, 5, 7, 10] {
            for _i in 0..30 {
                for shift in 0..3 {
                    let a = random_perm(&mut rng, n, shift);
                    let b = random_perm(&mut rng, n, shift);

                    let sum = &a + &b;

                    assert_eq!(&(&sum + &sum) + &sum, &sum + &(&sum + &sum));
                    assert_eq!(&(&a + &a) + &a, &a + &(&a + &a));
                }
            }
        }
    }
}
