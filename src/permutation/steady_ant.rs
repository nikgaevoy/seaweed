extern crate alloc;

use super::Permutation;
use alloc::vec;
use alloc::vec::Vec;

pub fn steady_ant(a: &Permutation, b: &Permutation) -> Permutation {
    #[cfg(test)]
    assert_eq!(a.len(), b.len());

    let br = b.recip();

    let mut c: Permutation = a.iter().map(|&mid| b[mid]).collect();
    let mut cr = c.recip();

    for lvl in (0..).take_while(|lvl| 1 << lvl < a.len()) {
        let half = 1 << lvl;
        let block = 2 << lvl;

        let is_blue = |row: usize| a.perm[row] & half != 0;

        let mut cols = vec![Vec::with_capacity(block); (a.len() + block - 1) >> (lvl + 1)];

        for (value, index) in br.iter().copied().enumerate() {
            cols[index >> (lvl + 1)].push(value);
        }

        for row in 0..c.len() {
            let rectangle = &mut cols[a[row] >> (lvl + 1)];
            let hcol = c[row];

            if rectangle.last() == Some(&hcol) {
                rectangle.pop();

                continue;
            }

            if is_blue(row) == (rectangle.last().map_or(true, |&col| hcol < col)) {
                while let Some(&col) = rectangle.last() {
                    let vrow = cr[col];

                    if vrow == row {
                        rectangle.pop();

                        break;
                    }

                    if is_blue(vrow) == (vrow < row) {
                        c.perm[row] = col;
                        cr.perm[col] = row;
                        rectangle.pop();

                        break;
                    }

                    rectangle.pop();
                }
            }
        }
    }

    c
}
