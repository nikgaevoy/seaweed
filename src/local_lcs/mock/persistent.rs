#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MockPersistentSet {
    versions: Vec<BTreeSet<usize>>,
}

impl MockPersistentSet {
    pub fn new() -> Self {
        Self {
            versions: vec![BTreeSet::new()],
        }
    }

    pub fn get_version(&self, version: usize) -> Option<&BTreeSet<usize>> {
        self.versions.get(version)
    }

    pub fn add_version(&mut self, version: usize) {
        self.versions.push(self.versions.last().unwrap().clone());
    }

    pub fn insert(&mut self) {
        self.versions.last_mut().unwrap().insert(version);
    }

    pub fn remove(&mut self) {
        self.versions.last_mut().unwrap().remove(&version);
    }

    pub fn is_empty(&self) -> bool {
        self.versions.last().unwrap().is_empty()
    }

    pub fn iter(&self) -> Iter<'_, usize> {
        self.versions.last().unwrap().iter()
    }

    pub fn as_set(&self) -> &BTreeSet<usize> {
        &self.versions.last().unwrap()
    }

    pub fn as_slice(&self) -> &[usize] {
        self.versions.last().unwrap().as_slice()
    }

    pub fn into_vec(self) -> Vec<usize> {
        self.versions.last().unwrap().iter().copied().collect()
    }
}
