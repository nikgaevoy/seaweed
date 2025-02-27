extern crate alloc;

use alloc::vec;
use alloc::vec::Vec;
use core::iter::{FromIterator, IntoIterator};
use core::mem::replace;
use core::ops::{Add, AddAssign, Index, Mul, MulAssign};
use core::slice::Iter;

use self::recursive_steady_ant::recursive_steady_ant;
use self::steady_ant::steady_ant;

mod knuth;
mod recursive_steady_ant;
mod steady_ant;

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Default, Debug, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Permutation {
    pub(crate) perm: Vec<usize>,
}

impl Index<usize> for Permutation {
    type Output = usize;

    fn index(&self, index: usize) -> &Self::Output {
        &self.perm[index]
    }
}

/// Constructs a permutation from iterator.
/// Assumes that the contents of an iterator indeed represents a permutation of numbers in range `0..iter.len()`.
/// Panics in the debug mode if this condition fails.
/// Failing the condition in release mode results in unspecified behavior.
impl FromIterator<usize> for Permutation {
    fn from_iter<T: IntoIterator<Item = usize>>(iter: T) -> Self {
        let ans = Self {
            perm: Vec::from_iter(iter),
        };

        debug_assert!(ans.check_validity().is_ok());

        ans
    }
}

impl IntoIterator for Permutation {
    type Item = usize;
    type IntoIter = <Vec<usize> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.perm.into_iter()
    }
}

impl<'a> IntoIterator for &'a Permutation {
    type Item = &'a usize;
    type IntoIter = <&'a Vec<usize> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.perm.iter()
    }
}

impl Permutation {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn id(n: usize) -> Self {
        Self {
            perm: (0..n).collect(),
        }
    }

    pub fn len(&self) -> usize {
        self.perm.len()
    }

    pub fn is_empty(&self) -> bool {
        self.perm.is_empty()
    }

    pub fn iter(&self) -> Iter<'_, usize> {
        self.perm.iter()
    }

    pub fn as_vec(&self) -> &Vec<usize> {
        &self.perm
    }

    pub fn as_slice(&self) -> &[usize] {
        &self.perm
    }

    pub fn into_vec(self) -> Vec<usize> {
        self.perm
    }

    pub fn swap(&mut self, a: usize, b: usize) {
        self.perm.swap(a, b);
    }

    pub fn recip(&self) -> Self {
        let mut perm = vec![0; self.len()];

        for i in 0..self.len() {
            perm[self[i]] = i;
        }

        Self { perm }
    }

    fn check_validity(&self) -> Result<(), &'static str> {
        let mut used = vec![false; self.perm.len()];

        for &i in &self.perm {
            if replace(
                used.get_mut(i)
                    .ok_or("Element of the permutation is larger than its len")?,
                true,
            ) {
                return Err("Repeated element in the permutation");
            }
        }

        Ok(())
    }

    /// Performs relative combing of `self` to `other`.
    /// Equivalent to `other.recip() * (self + other)`.
    pub fn relative_combing(&self, other: &Self) -> Self {
        other.recip() * (self + other)
    }
}

fn add_sticky(lhs: &Permutation, rhs: &Permutation) -> Permutation {
    assert_eq!(
        lhs.len(),
        rhs.len(),
        "Permutations have different sizes: {} != {}",
        lhs.len(),
        rhs.len()
    );

    if cfg!(test) {
        debug_assert_eq!(recursive_steady_ant(lhs, rhs), steady_ant(lhs, rhs));
    }

    steady_ant(lhs, rhs)
}

/// Performs sticky multiplication of permutations.
/// Permutations are required to have the same size.
impl<'a> Add<&Permutation> for &'a Permutation {
    type Output = Permutation;

    fn add(self, rhs: &Permutation) -> Self::Output {
        add_sticky(self, rhs)
    }
}

impl<'a> Add<Permutation> for &'a Permutation {
    type Output = Permutation;

    fn add(self, rhs: Permutation) -> Self::Output {
        add_sticky(self, &rhs)
    }
}

impl Add<&Permutation> for Permutation {
    type Output = Permutation;

    fn add(self, rhs: &Permutation) -> Self::Output {
        add_sticky(&self, rhs)
    }
}

impl Add<Permutation> for Permutation {
    type Output = Permutation;

    fn add(self, rhs: Permutation) -> Self::Output {
        add_sticky(&self, &rhs)
    }
}

impl AddAssign<&Permutation> for Permutation {
    fn add_assign(&mut self, rhs: &Permutation) {
        *self = &*self + rhs;
    }
}

impl AddAssign<Permutation> for Permutation {
    fn add_assign(&mut self, rhs: Permutation) {
        *self = &*self + rhs;
    }
}

/// Performs regular multiplication of permutations.
/// Permutations are required to have the same size.
impl MulAssign<&Permutation> for Permutation {
    fn mul_assign(&mut self, rhs: &Permutation) {
        assert_eq!(
            self.len(),
            rhs.len(),
            "Permutations have different sizes: {} != {}",
            self.len(),
            rhs.len()
        );

        for i in &mut self.perm {
            *i = rhs[*i];
        }
    }
}

impl MulAssign<Permutation> for Permutation {
    fn mul_assign(&mut self, rhs: Permutation) {
        *self *= &rhs;
    }
}

impl<'a> Mul<&Permutation> for &'a Permutation {
    type Output = Permutation;

    fn mul(self, rhs: &Permutation) -> Self::Output {
        self.clone() * rhs
    }
}

impl<'a> Mul<Permutation> for &'a Permutation {
    type Output = Permutation;

    fn mul(self, rhs: Permutation) -> Self::Output {
        self.clone() * rhs
    }
}

impl Mul<&Permutation> for Permutation {
    type Output = Permutation;

    fn mul(mut self, rhs: &Permutation) -> Self::Output {
        self *= rhs;

        self
    }
}

impl Mul<Permutation> for Permutation {
    type Output = Permutation;

    fn mul(mut self, rhs: Permutation) -> Self::Output {
        self *= rhs;

        self
    }
}

#[cfg(test)]
mod test {
    extern crate std;

    use std::vec::Vec;

    use std::cmp::Ordering;

    use crate::permutation::knuth::{knuth_tropical_multiplication, Core};
    use crate::permutation::recursive_steady_ant::recursive_steady_ant;
    use crate::permutation::Permutation;

    pub fn next_permutation(perm: &mut [usize]) -> bool {
        let last_ascending = match perm.windows(2).rposition(|w| w[0] < w[1]) {
            Some(i) => i,
            None => {
                perm.reverse();
                return false;
            }
        };

        let swap_with = perm[last_ascending + 1..]
            .binary_search_by(|n| usize::cmp(&perm[last_ascending], n).then(Ordering::Less))
            .unwrap_err();
        perm.swap(last_ascending, last_ascending + swap_with);
        perm[last_ascending + 1..].reverse();

        true
    }

    fn test_add(a: &[usize], b: &[usize]) {
        assert_eq!(a.len(), b.len());

        let a = Permutation { perm: Vec::from(a) };
        let b = Permutation { perm: Vec::from(b) };

        assert_eq!(&a + &b, recursive_steady_ant(&a, &b));
        assert_eq!(
            &a + &b,
            Permutation::from(&knuth_tropical_multiplication(
                &Core::from(&a),
                &Core::from(&b),
            ))
        );
    }

    fn test_recip(a: &[usize]) {
        let n = a.len();

        let a = Permutation { perm: Vec::from(a) };
        let b = a.recip();

        assert_eq!(a * b, Permutation::id(n));
    }

    #[test]
    fn add_and_recip() {
        for n in 1..6 {
            let mut a: Vec<_> = (0..n).collect();
            let mut b = a.clone();

            loop {
                loop {
                    test_add(&a, &b);

                    if !next_permutation(&mut b) {
                        break;
                    }
                }

                test_recip(&a);
                if !next_permutation(&mut a) {
                    break;
                }
            }
        }
    }

    #[test]
    fn operator_overloading() {
        let id = Permutation::id(3);
        let swap_12 = Permutation::from_iter([1, 0, 2]);
        let cycle = Permutation::from_iter([2, 0, 1]);

        assert_eq!(&cycle * &cycle * &cycle, id);
        assert_eq!(&swap_12 * &swap_12, id);
        assert_eq!(swap_12.clone() * swap_12.clone(), id);

        let mut tmp = cycle.clone();

        tmp *= &swap_12;
        tmp *= swap_12.clone();
        tmp += &swap_12;
        tmp += swap_12.clone();

        let double_tmp = &tmp * &tmp;
        assert_eq!(&tmp * tmp.clone(), double_tmp);
        assert_eq!(tmp.clone() * &tmp, double_tmp);
        assert_eq!(tmp.clone() * tmp.clone(), double_tmp);

        let double_tmp = &tmp + &tmp;
        assert_eq!(&tmp + tmp.clone(), double_tmp);
        assert_eq!(tmp.clone() + &tmp, double_tmp);
        assert_eq!(tmp.clone() + tmp.clone(), double_tmp);
    }
}
