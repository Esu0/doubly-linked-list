use crate::base::{LinkedList, Pointer};
use std::{
    borrow::Borrow,
    collections::{BTreeMap, HashMap},
    hash::{BuildHasher, Hash},
};

pub struct OrderedSet<M, T> {
    set: M,
    list: LinkedList<T>,
}

impl<M, T> OrderedSet<M, T> {
    pub fn new() -> Self
    where
        M: Default,
    {
        Self {
            set: M::default(),
            list: LinkedList::new(),
        }
    }

    pub fn insert_next<Q: ?Sized>(&mut self, key: &Q, value: T) -> bool
    where
        M: Map<Q, Key = T, Item = Pointer<T>>,
    {
        todo!()
    }
}
pub trait Map<Q: ?Sized> {
    type Key;
    type Item;

    fn get_key_value(&self, key: &Q) -> Option<(&Self::Key, &Self::Item)>;
    fn remove_entry(&mut self, key: &Q) -> Option<(Self::Key, Self::Item)>;
    fn insert(&mut self, key: Self::Key, value: Self::Item) -> Option<Self::Item>;
}

impl<K: Eq + Hash + Borrow<Q>, Q: Eq + Hash + ?Sized, V, S: BuildHasher + Default> Map<Q>
    for HashMap<K, V, S>
{
    type Key = K;
    type Item = V;

    fn get_key_value(&self, key: &Q) -> Option<(&Self::Key, &Self::Item)> {
        HashMap::get_key_value(self, key)
    }

    fn insert(&mut self, key: Self::Key, value: Self::Item) -> Option<Self::Item> {
        HashMap::insert(self, key, value)
    }

    fn remove_entry(&mut self, key: &Q) -> Option<(Self::Key, Self::Item)> {
        HashMap::remove_entry(self, key)
    }
}

impl<K: Ord + Borrow<Q>, V, Q: Ord + ?Sized> Map<Q> for BTreeMap<K, V> {
    type Key = K;
    type Item = V;

    fn get_key_value(&self, key: &Q) -> Option<(&Self::Key, &Self::Item)> {
        BTreeMap::get_key_value(self, key)
    }

    fn insert(&mut self, key: Self::Key, value: Self::Item) -> Option<Self::Item> {
        BTreeMap::insert(self, key, value)
    }

    fn remove_entry(&mut self, key: &Q) -> Option<(Self::Key, Self::Item)> {
        BTreeMap::remove_entry(self, key)
    }
}
