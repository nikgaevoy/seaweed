extern crate alloc;

use alloc::vec::Vec;

use core::cmp::Ordering;

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MockPersistentSet {
    set: Vec<usize>,
}

impl FromIterator<usize> for MockPersistentSet {
    fn from_iter<T: IntoIterator<Item = usize>>(iter: T) -> Self {
        let mut set = Vec::from_iter(iter);
        set.sort();
        set.dedup();

        Self { set }
    }
}

#[allow(dead_code)]
impl MockPersistentSet {
    pub fn new() -> Self {
        Self { set: Vec::new() }
    }

    pub fn insert(&self, value: usize) -> Self {
        let mut res = self.clone();

        res.set
            .insert(res.set.binary_search(&value).unwrap_err(), value);

        res
    }

    pub fn remove(&self, value: usize) -> Self {
        let mut res = self.clone();

        res.set.remove(res.set.binary_search(&value).unwrap());

        res
    }

    pub fn binary_search_by<'a, F: FnMut(&'a usize) -> Ordering>(
        &'a self,
        f: F,
    ) -> Result<usize, usize> {
        self.set.binary_search_by(f)
    }

    pub fn get(&self, index: usize) -> Option<&usize> {
        self.set.get(index)
    }
}
