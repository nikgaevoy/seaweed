#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Mock2DQuery {
    data: Vec<usize>,
}

impl FromIterator<Vec<usize>> for Mock2DQuery {
    fn from_iter<I: IntoIterator<Item = usize>>(iter: I) -> Self {
        Self { data: iter.into_iter().collect() }
    }
}

impl Mock2DQuery {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn query(&self, x: Range<usize>, y: Range<usize>) -> usize {
        self.data[x].iter().filter(|value| y.contains(&value)).count()
    }
}
