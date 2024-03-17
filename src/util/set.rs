use crate::base::LinkedList;
use std::{
    borrow::Borrow,
    collections::{BTreeSet, HashSet},
    hash::{BuildHasher, Hash},
};

pub struct OrderedSet<S, T> {
    set: S,
    list: LinkedList<T>,
}

impl<S, T> OrderedSet<S, T> {
    pub fn new() -> Self
    where
        S: Default,
    {
        Self {
            set: S::default(),
            list: LinkedList::new(),
        }
    }

    pub fn insert_next<Q: ?Sized>(&mut self, key: &Q, value: T) -> bool
    where
        S: Set<Q, Item = T>,
    {
        todo!()
    }
}
pub trait Set<Q: ?Sized> {
    type Item;

    fn get(&self, key: &Q) -> Option<&Self::Item>;
    fn take(&mut self, key: &Q) -> Option<Self::Item>;
    fn replace(&mut self, key: Self::Item) -> Option<Self::Item>;
}

impl<I: Eq + Hash + Borrow<Q>, Q: Eq + Hash + ?Sized, S: BuildHasher + Default> Set<Q>
    for HashSet<I, S>
{
    type Item = I;

    fn get(&self, key: &Q) -> Option<&Self::Item> {
        HashSet::get(self, key)
    }

    fn take(&mut self, key: &Q) -> Option<Self::Item> {
        HashSet::take(self, key)
    }

    fn replace(&mut self, key: Self::Item) -> Option<Self::Item> {
        HashSet::replace(self, key)
    }
}

impl<I: Ord + Borrow<Q>, Q: Ord + ?Sized> Set<Q> for BTreeSet<I> {
    type Item = I;

    fn get(&self, key: &Q) -> Option<&Self::Item> {
        BTreeSet::get(self, key)
    }

    fn take(&mut self, key: &Q) -> Option<Self::Item> {
        BTreeSet::take(self, key)
    }

    fn replace(&mut self, key: Self::Item) -> Option<Self::Item> {
        BTreeSet::replace(self, key)
    }
}
