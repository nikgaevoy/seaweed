pub mod global;
pub mod naive;

pub use global::GlobalDistanceOracle;

#[cfg(test)]
pub mod tests {
    extern crate alloc;
    extern crate std;

    use super::{naive::Naive, GlobalDistanceOracle};
    use alloc::vec::Vec;

    fn test_all_pairs<T: Eq>(a: Vec<T>, b: Vec<T>) {
        let n = a.len();
        let m = b.len();

        let solve = GlobalDistanceOracle::new(&a, &b);
        let stress = Naive::new(a, b);

        for al in 0..n {
            for ar in al + 1..=n {
                for bl in 0..m {
                    for br in bl + 1..=m {
                        let x = solve.ask(al..ar, bl..br);
                        let y = stress.ask(al..ar, bl..br);

                        assert_eq!(x, y);
                    }
                }
            }
        }
    }

    #[test]
    #[should_panic]
    pub fn sample() {
        test_all_pairs("abab".chars().collect(), "abba".chars().collect());
        test_all_pairs("abcabcabc".chars().collect(), "ababcaba".chars().collect());
        test_all_pairs("ababcaba".chars().collect(), "abcabcabc".chars().collect());
    }
}
