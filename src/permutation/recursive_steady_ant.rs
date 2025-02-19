extern crate alloc;

use alloc::vec;
use alloc::vec::Vec;
use core::iter::FromIterator;
use core::ops::Index;
use core::slice::Iter;

use super::Permutation;

use self::Color::{Blue, Red};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
enum Color {
    Red,
    Blue,
}

#[derive(Debug, Default, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
struct ColoredPermutation {
    perm: Vec<(Color, usize)>,
}

impl Index<usize> for ColoredPermutation {
    type Output = (Color, usize);

    fn index(&self, index: usize) -> &Self::Output {
        &self.perm[index]
    }
}

impl FromIterator<(Color, usize)> for ColoredPermutation {
    fn from_iter<T: IntoIterator<Item = (Color, usize)>>(iter: T) -> Self {
        let ans = Self {
            perm: Vec::from_iter(iter),
        };

        debug_assert!(ans.check_validity().is_ok());

        ans
    }
}

impl ColoredPermutation {
    pub fn len(&self) -> usize {
        self.perm.len()
    }

    pub fn recip(&self) -> Self {
        let mut perm = vec![(Red, usize::MAX); self.len()];

        for i in 0..self.len() {
            perm[self.perm[i].1] = (self.perm[i].0, i);
        }

        Self { perm }
    }

    pub fn iter(&self) -> Iter<'_, (Color, usize)> {
        self.perm.iter()
    }

    fn check_validity(&self) -> Result<(), &'static str> {
        Permutation {
            perm: self.iter().map(|(_, ind)| *ind).collect(),
        }
        .check_validity()
    }
}

fn split(recip: &Permutation) -> (Permutation, Permutation) {
    debug_assert!(recip.len() >= 2);

    let mut le = vec![usize::MAX; recip.len() / 2];
    let mut ri = vec![usize::MAX; recip.len() - le.len()];

    let mut index_le = 0usize..;
    let mut index_ri = 0usize..;

    for &value in &recip.perm {
        if value < le.len() {
            le[value] = index_le.next().unwrap();
        } else {
            ri[value - le.len()] = index_ri.next().unwrap();
        }
    }

    (Permutation { perm: le }, Permutation { perm: ri })
}

fn color_cols(perm: &Permutation) -> (Vec<usize>, Vec<usize>) {
    let mut colors = vec![Blue; perm.len()];

    for &i in &perm.perm[0..perm.len() / 2] {
        colors[i] = Red;
    }

    let mut red = Vec::with_capacity(perm.len() / 2);
    let mut blue = Vec::with_capacity(perm.len() - red.len());

    for (i, color) in colors.into_iter().enumerate() {
        match color {
            Red => red.push(i),
            Blue => blue.push(i),
        }
    }

    (red, blue)
}

pub fn recursive_steady_ant(a: &Permutation, b: &Permutation) -> Permutation {
    assert_eq!(a.len(), b.len());

    if a.len() < 2 {
        return a.clone();
    }

    let br = b.recip();

    let (red_cols, blue_cols) = color_cols(b);

    let (ar_red, ar_blue) = split(a);
    let (b_red, b_blue) = split(&br);

    let red = &ar_red.recip() + &b_red;
    let blue = &ar_blue.recip() + &b_blue;

    let mut ired = red.iter();
    let mut iblue = blue.iter();

    let c: ColoredPermutation = a
        .iter()
        .map(|&middle_index| {
            if middle_index < red.len() {
                (Red, red_cols[*ired.next().unwrap()])
            } else {
                (Blue, blue_cols[*iblue.next().unwrap()])
            }
        })
        .collect();

    let cr = c.recip();

    let mut perm = vec![usize::MAX; c.len()];

    let mut col: usize = 0;

    for row in (0..perm.len()).rev() {
        let (hcolor, hcol) = c[row];

        if hcol == col {
            col += 1;

            continue;
        }

        if (hcolor == Blue) == (hcol < col) {
            while col < c.len() {
                let (vcolor, vrow) = cr[col];

                if vrow == row {
                    col += 1;
                    break;
                }

                if (vcolor == Blue) == (vrow < row) {
                    perm[row] = col; // green
                    col += 1;

                    break;
                }

                col += 1;
            }
        }
    }

    for (ind, (_color, value)) in c.iter().enumerate() {
        if perm[ind] == usize::MAX {
            perm[ind] = *value;
        }
    }

    Permutation { perm }
}
