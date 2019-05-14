use std::cmp::Ordering;

pub trait Combiner<Data, Aug> {
    fn combine(&self, data: &Data, left: Option<&Aug>, right: Option<&Aug>) -> Aug;
}

pub trait Traverser<Data, Aug, Out>
where
    Self: std::marker::Sized,
{
    fn step(self, data: &Data, aug: &Aug) -> Step<Self, Out>;
    fn finish(self) -> Out;
}

pub enum Step<T, U> {
    Left(T),
    Right(T),
    Done(U),
}

pub struct AugTree<Data, Aug, C: Combiner<Data, Aug>> {
    root: Link<Data, Aug>,
    combiner: C,
}

type Link<Data, Aug> = Option<Box<Node<Data, Aug>>>;

struct Node<Data, Aug> {
    left: Link<Data, Aug>,
    right: Link<Data, Aug>,
    data: Data,
    aug: Aug,
}

impl<Data: Ord, Aug, C: Combiner<Data, Aug>> AugTree<Data, Aug, C> {
    pub fn new(combiner: C) -> Self {
        Self {
            root: None,
            combiner,
        }
    }
    pub fn insert(&mut self, data: Data) -> bool {
        Node::link_insert(&mut self.root, data, &self.combiner)
    }
    pub fn traverse<T, Out>(&self, traverser: T) -> Out
    where
        T: Traverser<Data, Aug, Out>,
    {
        Node::link_traverse(&self.root, traverser)
    }
}

impl<Data: Ord, Aug> Node<Data, Aug> {
    fn link_insert<C>(link: &mut Link<Data, Aug>, data: Data, combiner: &C) -> bool
    where
        C: Combiner<Data, Aug>,
    {
        if let Some(node) = link {
            node.insert(data, combiner)
        } else {
            *link = Some(Box::new(Self::make(data, combiner)));
            true
        }
    }
    fn link_traverse<T, Out>(link: &Link<Data, Aug>, traverser: T) -> Out
    where
        T: Traverser<Data, Aug, Out>,
    {
        if let Some(node) = link {
            node.traverse(traverser)
        } else {
            traverser.finish()
        }
    }
}

impl<Data: Ord, Aug> Node<Data, Aug> {
    fn make<C>(data: Data, combiner: &C) -> Self
    where
        C: Combiner<Data, Aug>,
    {
        let aug = combiner.combine(&data, None, None);
        Self {
            left: None,
            right: None,
            data,
            aug,
        }
    }
    fn insert<C>(&mut self, data: Data, combiner: &C) -> bool
    where
        C: Combiner<Data, Aug>,
    {
        match data.cmp(&self.data) {
            Ordering::Equal => return false,
            Ordering::Less => {
                let was_present = Self::link_insert(&mut self.left, data, combiner);
                self.update_aug(combiner);
                was_present
            }
            Ordering::Greater => {
                let was_present = Self::link_insert(&mut self.right, data, combiner);
                self.update_aug(combiner);
                was_present
            }
        }
    }
    fn update_aug<C>(&mut self, combiner: &C)
    where
        C: Combiner<Data, Aug>,
    {
        self.aug = combiner.combine(
            &self.data,
            self.left.as_ref().map(|l| &l.aug),
            self.right.as_ref().map(|r| &r.aug),
        );
    }
    fn traverse<T, Out>(&self, traverser: T) -> Out
    where
        T: Traverser<Data, Aug, Out>,
    {
        match traverser.step(&self.data, &self.aug) {
            Step::Done(out) => out,
            Step::Left(next_traverser) => Self::link_traverse(&self.left, next_traverser),
            Step::Right(next_traverser) => Self::link_traverse(&self.right, next_traverser),
        }
    }
}

struct IndexCombiner {}

impl<Data> Combiner<Data, (usize, usize)> for IndexCombiner {
    fn combine(
        &self,
        _data: &Data,
        left: Option<&(usize, usize)>,
        right: Option<&(usize, usize)>,
    ) -> (usize, usize) {
        (
            left.map_or(0, |l| 1 + l.0 + l.1),
            right.map_or(0, |r| 1 + r.0 + r.1),
        )
    }
}

struct IndexTraverser(usize);

impl<Data: Clone> Traverser<Data, (usize, usize), Option<Data>> for IndexTraverser {
    fn step(self, data: &Data, child_sizes: &(usize, usize)) -> Step<Self, Option<Data>> {
        let IndexTraverser(index) = self;
        if index < child_sizes.0 {
            Step::Left(IndexTraverser(index))
        } else if index == child_sizes.0 {
            Step::Done(Some(data.clone()))
        } else if index < child_sizes.0 + child_sizes.1 + 1 {
            Step::Right(IndexTraverser(index - child_sizes.0 - 1))
        } else {
            Step::Done(None)
        }
    }
    fn finish(self) -> Option<Data> {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn empty() {
        let tree: AugTree<i32, _, _> = AugTree::new(IndexCombiner{});
        let zeroth = tree.traverse(IndexTraverser(0));
        assert!(zeroth.is_none());
    }
    #[test]
    fn insert() {
        let mut tree: AugTree<i32, _, _> = AugTree::new(IndexCombiner{});
        let was_new = tree.insert(1);
        assert!(was_new);
        let was_new = tree.insert(2);
        assert!(was_new);
        let was_new = tree.insert(1);
        assert!(!was_new);
    }
    #[test]
    fn full() {
        let mut tree: AugTree<i32, _, _> = AugTree::new(IndexCombiner{});
        tree.insert(1);
        tree.insert(2);
        tree.insert(1);
        assert_eq!(tree.traverse(IndexTraverser(0)), Some(1));
        assert_eq!(tree.traverse(IndexTraverser(1)), Some(2));
    }
}

pub struct SimpleAugTree {
    root: SimpleLink,
}

type SimpleLink = Option<Box<SimpleNode>>;

struct SimpleNode {
    left: SimpleLink,
    right: SimpleLink,
    data: i32,
    size: usize,
}

impl SimpleAugTree {
    pub fn new() -> Self {
        Self { root: None }
    }
    // was new
    pub fn insert(&mut self, data: i32) -> bool {
        SimpleNode::link_insert(&mut self.root, data)
    }
    // nth element in sorted order
    pub fn nth(&self, index: usize) -> Option<i32> {
        SimpleNode::link_nth(&self.root, index)
    }
}

// SimpleLink Methods
impl SimpleNode {
    fn link_insert(link: &mut SimpleLink, data: i32) -> bool {
        if let Some(node) = link {
            node.insert(data)
        } else {
            *link = Some(Box::new(Self::make(data)));
            true
        }
    }
    fn link_nth(link: &SimpleLink, index: usize) -> Option<i32> {
        link.as_ref().and_then(|n| n.nth(index))
    }
}

impl SimpleNode {
    fn make(data: i32) -> Self {
        Self {
            left: None,
            right: None,
            data,
            size: 1,
        }
    }
    fn insert(&mut self, data: i32) -> bool {
        match data.cmp(&self.data) {
            Ordering::Equal => return false,
            Ordering::Less => {
                self.size += 1;
                Self::link_insert(&mut self.left, data)
            }
            Ordering::Greater => {
                self.size += 1;
                Self::link_insert(&mut self.right, data)
            }
        }
    }
    fn nth(&self, index: usize) -> Option<i32> {
        let left_size = self.left.as_ref().map_or(0, |n| n.size);
        if index < left_size {
            Self::link_nth(&self.left, index)
        } else if index == left_size {
            Some(self.data)
        } else if index < self.size {
            Self::link_nth(&self.right, index - left_size - 1)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod simple_tests {
    use super::*;
    #[test]
    fn empty() {
        let tree = SimpleAugTree::new();
        let zeroth = tree.nth(0);
        assert!(zeroth.is_none());
    }
    #[test]
    fn insert() {
        let mut tree = SimpleAugTree::new();
        let was_new = tree.insert(1);
        assert!(was_new);
        let was_new = tree.insert(2);
        assert!(was_new);
        let was_new = tree.insert(1);
        assert!(!was_new);
    }
    #[test]
    fn full() {
        let mut tree = SimpleAugTree::new();
        tree.insert(1);
        tree.insert(2);
        tree.insert(1);
        assert_eq!(tree.nth(0), Some(1));
        assert_eq!(tree.nth(1), Some(2));
    }
}
