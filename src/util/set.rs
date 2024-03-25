use crate::base::{LinkedList, Pointer};
use std::{
    borrow::Borrow,
    cmp,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    hash::{BuildHasher, Hash, Hasher},
};

pub struct OrderedSet<S, T> {
    set: S,
    list: LinkedList<T>,
}

/// [`OrderedSet`]のジェネリクスを指定するための型で、インスタンスを作成する手段はない
pub struct BorrowPtr<T: ?Sized>(Pointer<T>);

impl<T: ?Sized> Clone for BorrowPtr<T> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}

impl<T: ?Sized> Copy for BorrowPtr<T> {}

impl<T: ?Sized + PartialEq> PartialEq for BorrowPtr<T> {
    fn eq(&self, other: &Self) -> bool {
        Borrow::<T>::borrow(self).eq(other.borrow())
    }

    fn ne(&self, other: &Self) -> bool {
        Borrow::<T>::borrow(self).ne(other.borrow())
    }
}

impl<T: ?Sized + Eq> Eq for BorrowPtr<T> {}

impl<T: ?Sized + PartialOrd> PartialOrd for BorrowPtr<T> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Borrow::<T>::borrow(self).partial_cmp(other.borrow())
    }

    fn ge(&self, other: &Self) -> bool {
        Borrow::<T>::borrow(self).ge(other.borrow())
    }

    fn gt(&self, other: &Self) -> bool {
        Borrow::<T>::borrow(self).gt(other.borrow())
    }

    fn le(&self, other: &Self) -> bool {
        Borrow::<T>::borrow(self).le(other.borrow())
    }

    fn lt(&self, other: &Self) -> bool {
        Borrow::<T>::borrow(self).lt(other.borrow())
    }
}

impl<T: ?Sized + Ord> Ord for BorrowPtr<T> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        Borrow::<T>::borrow(self).cmp(other.borrow())
    }
}

impl<T: ?Sized + Hash> Hash for BorrowPtr<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Borrow::<T>::borrow(self).hash(state);
    }
}

impl<T> Borrow<T> for BorrowPtr<T>
where
    T: ?Sized,
{
    fn borrow(&self) -> &T {
        unsafe { self.0.get().value() }
    }
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

    pub fn insert_after<Q: ?Sized>(&mut self, key: &Q, value: T) -> bool
    where
        S: Set<T, Key = BorrowPtr<T>>,
        Q: Borrow<T>,
    {
        let Some(&ptr) = self.set.get(key.borrow()) else {
            return false;
        };
        if self.set.get(&value).is_some() {
            return false;
        }
        let new = unsafe { self.list.insert_after_pointer(Some(ptr.0), value) };
        if self.set.replace(BorrowPtr(new)).is_some() {
            panic!("returned `None` value. Maybe using broken `Set` or `Allocator`.")
        }
        true
    }

    pub fn insert_before<Q: ?Sized>(&mut self, key: &Q, value: T) -> bool
    where
        S: Set<T, Key = BorrowPtr<T>>,
        Q: Borrow<T>,
    {
        let Some(&ptr) = self.set.get(key.borrow()) else {
            return false;
        };
        if self.set.get(&value).is_some() {
            return false;
        }
        let new = unsafe { self.list.insert_before_pointer(Some(ptr.0), value) };
        if self.set.replace(BorrowPtr(new)).is_some() {
            panic!("returned `None` value. Maybe using broken `Set` or `Allocator`.")
        }
        true
    }
}

pub trait Set<Q: ?Sized> {
    type Key;

    fn get(&self, key: &Q) -> Option<&Self::Key>;
    fn take(&mut self, key: &Q) -> Option<Self::Key>;
    fn replace(&mut self, key: Self::Key) -> Option<Self::Key>;
}

impl<K, Q, S> Set<Q> for HashSet<K, S>
where
    K: Eq + Hash + Borrow<Q>,
    Q: Eq + Hash + ?Sized,
    S: BuildHasher,
{
    type Key = K;

    fn get(&self, key: &Q) -> Option<&Self::Key> {
        HashSet::get(self, key)
    }

    fn take(&mut self, key: &Q) -> Option<Self::Key> {
        HashSet::take(self, key)
    }

    fn replace(&mut self, key: Self::Key) -> Option<Self::Key> {
        HashSet::replace(self, key)
    }
}

impl<K, Q> Set<Q> for BTreeSet<K>
where
    K: Ord + Borrow<Q>,
    Q: Ord + ?Sized,
{
    type Key = K;

    fn get(&self, key: &Q) -> Option<&Self::Key> {
        BTreeSet::get(self, key)
    }

    fn take(&mut self, key: &Q) -> Option<Self::Key> {
        BTreeSet::take(self, key)
    }

    fn replace(&mut self, key: Self::Key) -> Option<Self::Key> {
        BTreeSet::replace(self, key)
    }
}

pub trait Map<Q: ?Sized> {
    type Key;
    type Item;

    fn get_key_value(&self, key: &Q) -> Option<(&Self::Key, &Self::Item)>;
    fn remove_entry(&mut self, key: &Q) -> Option<(Self::Key, Self::Item)>;
    fn insert(&mut self, key: Self::Key, value: Self::Item) -> Option<Self::Item>;
}

impl<K, Q, V, S> Map<Q> for HashMap<K, V, S>
where
    K: Eq + Hash + Borrow<Q>,
    Q: Eq + Hash + ?Sized,
    S: BuildHasher,
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

impl<K, V, Q> Map<Q> for BTreeMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: Ord + ?Sized,
{
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
