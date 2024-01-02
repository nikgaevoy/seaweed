use std::iter::{FromIterator, IntoIterator};
use std::ops::{Add, Index};
use std::slice::Iter;

use self::recursive_steady_ant::recursive_steady_ant;
use self::steady_ant::steady_ant;

mod knuth;
mod recursive_steady_ant;
mod steady_ant;

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Default, Debug, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Permutation {
    perm: Vec<usize>,
}

impl Index<usize> for Permutation {
    type Output = usize;

    fn index(&self, index: usize) -> &Self::Output {
        &self.perm[index]
    }
}

impl FromIterator<usize> for Permutation {
    fn from_iter<T: IntoIterator<Item = usize>>(iter: T) -> Self {
        let ans = Self {
            perm: Vec::from_iter(iter),
        };

        debug_assert!(ans.is_valid());

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
        (&self.perm).into_iter()
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

    fn is_valid(&self) -> bool {
        let mut tmp = self.perm.clone();
        tmp.sort();
        if let Some(&x) = tmp.first() {
            if x != 0 {
                return false;
            }
        }
        for i in (0..tmp.len()).skip(1) {
            if tmp[i - 1] + 1 != tmp[i] {
                return false;
            }
        }

        true
    }
}

impl<'a> Add<&Permutation> for &'a Permutation {
    type Output = Permutation;

    fn add(self, rhs: &Permutation) -> Self::Output {
        debug_assert_eq!(recursive_steady_ant(self, rhs), steady_ant(self, rhs));

        steady_ant(self, rhs)
    }
}

#[cfg(test)]
mod test {
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

    #[test]
    fn add() {
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

                if !next_permutation(&mut a) {
                    break;
                }
            }
        }
    }
}
