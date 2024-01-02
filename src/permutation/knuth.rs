use alloc::vec;
use alloc::vec::Vec;
use core::ops::Index;

use super::Permutation;

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Default, Debug, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub(crate) struct Core(Vec<Vec<usize>>);

impl Core {
    pub fn first(&self) -> Option<&Vec<usize>> {
        self.0.first()
    }
}

impl Core {
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl Index<usize> for Core {
    type Output = Vec<usize>;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl From<&Core> for Permutation {
    fn from(core: &Core) -> Self {
        assert!(!core.is_empty());

        let mut perm = vec![usize::MAX; core.len() - 1];

        for i in 0..perm.len() {
            for j in 0..perm.len() {
                if core[i][j + 1] == core[i][j] + 1
                    && core[i + 1][j + 1] == core[i][j]
                    && core[i + 1][j] == core[i][j]
                {
                    perm[i] = j;
                }
            }
        }

        debug_assert!(!perm.contains(&usize::MAX));

        let ans = Self { perm };

        debug_assert!(ans.is_valid());

        ans
    }
}

impl From<&Permutation> for Core {
    fn from(perm: &Permutation) -> Self {
        let mut ans = vec![Vec::default(); perm.len() + 1];
        *ans.last_mut().unwrap() = vec![0; perm.len() + 1];

        for i in (0..perm.len()).rev() {
            ans[i] = ans[i + 1].clone();

            for j in &mut ans[i][perm[i] + 1..] {
                *j += 1;
            }
        }

        let ans = Core(ans);

        debug_assert_eq!(*perm, Permutation::from(&ans));

        ans
    }
}

#[allow(dead_code)]
pub fn knuth_tropical_multiplication(a: &Core, b: &Core) -> Core {
    let rows = a.len();
    let cols = match b.first() {
        None => 0,
        Some(x) => x.len(),
    };

    let mut c = vec![vec![usize::MAX; cols]; rows];
    let mut opt = vec![vec![0; cols]; rows];

    for l in 0..rows {
        for r in (0..cols).rev() {
            let left_ind = if l == 0 { 0 } else { opt[l - 1][r] };
            let right_ind = if r + 1 == cols {
                b.len() - 1
            } else {
                opt[l][r + 1]
            };

            let (res, ind) = (left_ind..=right_ind)
                .map(|ind| (a[l][ind] + b[ind][r], ind))
                .min()
                .unwrap();

            c[l][r] = res;
            opt[l][r] = ind;
        }
    }

    Core(c)
}
