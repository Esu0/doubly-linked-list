use std::{
    alloc::{Allocator, Global},
    fmt::{self, Debug},
    marker::PhantomData,
    mem::{self, ManuallyDrop},
    ptr::NonNull,
};

use crate::base::{self as base, IterPtr, Node};

pub struct LinkedList<T: ?Sized, A: Allocator + Clone = Global> {
    list: base::LinkedList<T, A>,
    len: usize,
}

impl<T, A: Allocator + Clone> LinkedList<T, A> {
    pub fn push_front(&mut self, value: T) {
        self.len += 1;
        self.list.push_front(value);
    }

    pub fn push_back(&mut self, value: T) {
        self.len += 1;
        self.list.push_back(value);
    }

    pub fn pop_front(&mut self) -> Option<T> {
        self.len = self.len.saturating_sub(1);
        self.list.pop_front()
    }

    pub fn pop_back(&mut self) -> Option<T> {
        self.len = self.len.saturating_sub(1);
        self.list.pop_back()
    }
}

impl<T: ?Sized> LinkedList<T, Global> {
    pub const fn new() -> Self {
        Self {
            list: base::LinkedList::new(),
            len: 0,
        }
    }
}

impl<T: ?Sized, A: Allocator + Clone> LinkedList<T, A> {
    pub const fn new_in(alloc: A) -> Self {
        Self {
            list: base::LinkedList::new_in(alloc),
            len: 0,
        }
    }

    pub const fn is_empty(&self) -> bool {
        self.list.is_empty()
    }

    pub const fn len(&self) -> usize {
        self.len
    }

    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            iter_ptr: self.iter_ptr(),
            _marker: PhantomData,
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            iter_ptr: self.iter_ptr(),
            _marker: PhantomData,
        }
    }

    pub fn front(&self) -> Option<&T> {
        self.list.front()
    }

    pub fn back(&self) -> Option<&T> {
        self.list.back()
    }

    pub fn front_mut(&mut self) -> Option<&mut T> {
        self.list.front_mut()
    }

    pub fn back_mut(&mut self) -> Option<&mut T> {
        self.list.back_mut()
    }

    pub fn cursor_front(&self) -> Option<Cursor<'_, T>> {
        self.list.cursor_front()
    }

    pub fn cursor_back(&self) -> Option<Cursor<'_, T>> {
        self.list.cursor_back()
    }

    pub fn cursor_front_mut(&mut self) -> CursorMut<'_, T, A> {
        CursorMut {
            cursor: CursorMutWithoutIndex {
                pointer: self.pointer_front(),
                list: self,
            },
            index: 0,
        }
    }

    pub fn cursor_back_mut(&mut self) -> CursorMut<'_, T, A> {
        CursorMut {
            index: self.len.checked_sub(1).unwrap_or(0),
            cursor: CursorMutWithoutIndex {
                pointer: self.pointer_back(),
                list: self,
            },
        }
    }

    pub fn pointer_front(&self) -> Option<Pointer<T>> {
        self.list.pointer_front().map(From::from)
    }

    pub fn pointer_back(&self) -> Option<Pointer<T>> {
        self.list.pointer_back().map(From::from)
    }

    pub fn append(&mut self, other: &mut Self) {
        self.len += mem::take(&mut other.len);
        self.list.append(&mut other.list);
    }

    pub fn clear(&mut self) {
        *self = Self::new_in(self.list.alloc().clone());
    }

    fn iter_ptr(&self) -> IterPtrWithLen<T> {
        IterPtrWithLen {
            iter: self.list.iter_ptr(),
            len: self.len,
        }
    }
}

struct IterPtrWithLen<T: ?Sized> {
    iter: IterPtr<T>,
    len: usize,
}

impl<T: ?Sized> Iterator for IterPtrWithLen<T> {
    type Item = NonNull<Node<T>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.len = self.len.saturating_sub(1);
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    fn last(self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.iter.last()
    }
}

impl<T: ?Sized> DoubleEndedIterator for IterPtrWithLen<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.len = self.len.saturating_sub(1);
        self.iter.next_back()
    }
}

impl<T: ?Sized> ExactSizeIterator for IterPtrWithLen<T> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<I> FromIterator<I> for LinkedList<I, Global> {
    fn from_iter<T: IntoIterator<Item = I>>(iter: T) -> Self {
        let mut list = Self::new();
        for item in iter {
            list.push_back(item);
        }
        list
    }
}

impl<T, A: Allocator + Clone> IntoIterator for LinkedList<T, A> {
    type IntoIter = IntoIter<T, A>;
    type Item = T;

    fn into_iter(self) -> Self::IntoIter {
        let slf = ManuallyDrop::new(self);
        IntoIter {
            iter_ptr: slf.iter_ptr(),
            alloc: slf.list.alloc().clone(),
            _marker: PhantomData,
        }
    }
}

impl<'a, T: ?Sized, A: Allocator + Clone> IntoIterator for &'a LinkedList<T, A> {
    type IntoIter = Iter<'a, T>;
    type Item = &'a T;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T: ?Sized, A: Allocator + Clone> IntoIterator for &'a mut LinkedList<T, A> {
    type IntoIter = IterMut<'a, T>;
    type Item = &'a mut T;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

pub struct IntoIter<T, A: Allocator + Clone> {
    iter_ptr: IterPtrWithLen<T>,
    alloc: A,
    _marker: PhantomData<LinkedList<T, A>>,
}

impl<T, A: Allocator + Clone> Iterator for IntoIter<T, A> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_ptr
            .next()
            .map(|ptr| unsafe { Box::from_raw_in(ptr.as_ptr(), self.alloc.clone()).into_value() })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter_ptr.size_hint()
    }
}

impl<T, A: Allocator + Clone> DoubleEndedIterator for IntoIter<T, A> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter_ptr
            .next_back()
            .map(|ptr| unsafe { Box::from_raw_in(ptr.as_ptr(), self.alloc.clone()).into_value() })
    }
}

impl<T, A: Allocator + Clone> ExactSizeIterator for IntoIter<T, A> {
    fn len(&self) -> usize {
        self.iter_ptr.len()
    }
}

impl<T, A: Allocator + Clone> Drop for IntoIter<T, A> {
    fn drop(&mut self) {
        unsafe {
            // lenの変更を避けてdrop
            drop(base::IntoIter::from_iter_ptr(
                self.iter_ptr.iter.clone(),
                self.alloc.clone(),
            ))
        }
    }
}

pub struct Iter<'a, T: ?Sized> {
    iter_ptr: IterPtrWithLen<T>,
    _marker: PhantomData<&'a Node<T>>,
}

impl<'a, T: ?Sized> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_ptr
            .next()
            .map(|ptr| unsafe { (*ptr.as_ptr()).value() })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter_ptr.size_hint()
    }

    fn last(self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.iter_ptr
            .last()
            .map(|ptr| unsafe { (*ptr.as_ptr()).value() })
    }
}

impl<T: ?Sized> DoubleEndedIterator for Iter<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter_ptr
            .next_back()
            .map(|ptr| unsafe { (*ptr.as_ptr()).value() })
    }
}

impl<T: ?Sized> ExactSizeIterator for Iter<'_, T> {
    fn len(&self) -> usize {
        self.iter_ptr.len()
    }
}

pub struct IterMut<'a, T: ?Sized> {
    iter_ptr: IterPtrWithLen<T>,
    _marker: PhantomData<&'a mut Node<T>>,
}

impl<'a, T: ?Sized> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_ptr
            .next()
            .map(|ptr| unsafe { (*ptr.as_ptr()).value_mut() })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter_ptr.size_hint()
    }

    fn last(self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.iter_ptr
            .last()
            .map(|ptr| unsafe { (*ptr.as_ptr()).value_mut() })
    }
}

impl<T: ?Sized> DoubleEndedIterator for IterMut<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter_ptr
            .next_back()
            .map(|ptr| unsafe { (*ptr.as_ptr()).value_mut() })
    }
}

impl<T: ?Sized> ExactSizeIterator for IterMut<'_, T> {
    fn len(&self) -> usize {
        self.iter_ptr.len()
    }
}

impl<T: Debug + ?Sized, A: Allocator + Clone> Debug for LinkedList<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.list.fmt(f)
    }
}

impl<T: ?Sized> Default for LinkedList<T, Global> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const N: usize> From<[T; N]> for LinkedList<T, Global> {
    fn from(value: [T; N]) -> Self {
        value.into_iter().collect()
    }
}

impl<T> From<Vec<T>> for LinkedList<T, Global> {
    fn from(value: Vec<T>) -> Self {
        value.into_iter().collect()
    }
}

impl<T: Clone> From<&[T]> for LinkedList<T, Global> {
    fn from(value: &[T]) -> Self {
        value.iter().cloned().collect()
    }
}

// TODO: impl PartialEq for LinkedList
// TODO: impl Eq for LinkedList
// TODO: impl PartialOrd for LinkedList
// TODO: impl Ord for LinkedList

pub type Pointer<T> = base::Pointer<T>;

impl<T: ?Sized, A: Allocator + Clone> LinkedList<T, A> {
    unsafe fn cut_node(&mut self, pointer: Pointer<T>) -> Box<Node<T>, A> {
        self.len = self.len.saturating_sub(1);
        self.list.cut_node(pointer.into())
    }

    pub unsafe fn remove(&mut self, pointer: Pointer<T>) {
        drop(self.cut_node(pointer));
    }

    pub unsafe fn get(&self, pointer: Pointer<T>) -> &T {
        self.list.get(pointer)
    }

    pub unsafe fn get_mut(&mut self, pointer: Pointer<T>) -> &mut T {
        self.list.get_mut(pointer)
    }

    pub unsafe fn get_cursor(&self, pointer: Pointer<T>) -> Cursor<'_, T> {
        self.list.get_cursor(pointer)
    }
}

pub type Cursor<'a, T> = base::Cursor<'a, T>;

pub struct CursorMutWithoutIndex<'a, T: ?Sized, A: Allocator + Clone> {
    pointer: Option<Pointer<T>>,
    list: &'a mut LinkedList<T, A>,
}

impl<'a, T: ?Sized, A: Allocator + Clone> CursorMutWithoutIndex<'a, T, A> {
    pub fn move_next(&mut self) {
        unsafe {
            self.pointer = self.list.list.next_pointer(self.pointer);
        }
    }

    pub fn move_prev(&mut self) {
        unsafe {
            self.pointer = self.list.list.prev_pointer(self.pointer);
        }
    }

    fn cut_node_current(&mut self) -> Option<Box<Node<T>, A>> {
        self.pointer.map(|pointer| unsafe {
            self.pointer = pointer.next();
            self.list.cut_node(pointer)
        })
    }

    pub fn remove_current(&mut self) {
        drop(self.cut_node_current());
    }

    pub unsafe fn set_from_pointer(&mut self, pointer: Pointer<T>) {
        self.pointer = Some(pointer);
    }

    pub fn list(&mut self) -> &mut LinkedList<T, A> {
        self.list
    }

    pub fn splice_after(&mut self, list: LinkedList<T, A>) {
        self.list.len += list.len;
        unsafe {
            self.list
                .list
                .splice_after_with_pointer(self.pointer, list.list)
        }
    }

    pub fn splice_before(&mut self, list: LinkedList<T, A>) {
        self.list.len += list.len;
        unsafe {
            self.list
                .list
                .splice_before_with_pointer(self.pointer, list.list)
        }
    }

    pub fn is_dummy(&self) -> bool {
        self.pointer.is_none()
    }

    pub fn get(&self) -> Option<&T> {
        unsafe { self.pointer.map(|pointer| self.list.list.get(pointer)) }
    }

    pub fn get_mut(&mut self) -> Option<&mut T> {
        unsafe { self.pointer.map(|pointer| self.list.list.get_mut(pointer)) }
    }

    pub unsafe fn add_index_unchecked(self, index: usize) -> CursorMut<'a, T, A> {
        CursorMut {
            cursor: self,
            index,
        }
    }

    pub fn add_index(self) -> CursorMut<'a, T, A> {
        unsafe {
            let index = if let Some(pointer) = self.pointer {
                self.list
                    .list
                    .iter_ptr()
                    .enumerate()
                    .find(|(_, ptr)| *ptr == pointer.as_ptr_node())
                    .map(|(i, _)| i)
                    .unwrap_unchecked()
            } else {
                self.list.len
            };
            self.add_index_unchecked(index)
        }
    }
}

impl<'a, T, A: Allocator + Clone> CursorMutWithoutIndex<'a, T, A> {
    pub fn cut_current(&mut self) -> Option<T> {
        self.cut_node_current().map(|node| node.into_value())
    }

    pub fn insert_after(&mut self, value: T) {
        self.list.len += 1;
        unsafe {
            self.list.list.insert_after_pointer(self.pointer, value);
        }
    }

    pub fn insert_before(&mut self, value: T) {
        self.list.len += 1;
        unsafe {
            self.list.list.insert_before_pointer(self.pointer, value);
        }
    }
}

pub struct CursorMut<'a, T: ?Sized, A: Allocator + Clone> {
    cursor: CursorMutWithoutIndex<'a, T, A>,
    index: usize,
}

impl<'a, T: ?Sized, A: Allocator + Clone> CursorMut<'a, T, A> {
    pub fn move_next(&mut self) {
        self.index = if self.index == self.cursor.list.len {
            0
        } else {
            self.index + 1
        };
        self.cursor.move_next();
    }

    pub fn move_prev(&mut self) {
        self.index -= self.index.checked_sub(1).unwrap_or(self.cursor.list.len);
        self.cursor.move_prev();
    }

    fn cut_node_current(&mut self) -> Option<Box<Node<T>, A>> {
        self.cursor.cut_node_current()
    }

    pub fn remove_current(&mut self) {
        drop(self.cut_node_current());
    }

    pub fn list(&mut self) -> &mut LinkedList<T, A> {
        self.cursor.list
    }

    pub fn splice_after(&mut self, list: LinkedList<T, A>) {
        self.cursor.splice_after(list);
        if self.cursor.pointer.is_none() {
            self.index = self.cursor.list.len;
        }
    }

    pub fn splice_before(&mut self, list: LinkedList<T, A>) {
        self.index += list.len;
        self.cursor.splice_before(list);
    }

    pub fn split_after(&mut self) -> LinkedList<T, A> {
        let new_len = if self.index == self.cursor.list.len {
            self.index = 0;
            0
        } else {
            self.index + 1
        };
        let old_len = mem::replace(&mut self.cursor.list.len, new_len);
        unsafe {
            LinkedList {
                len: old_len - new_len,
                list: self
                    .cursor
                    .list
                    .list
                    .split_after_with_pointer(self.cursor.pointer),
            }
        }
    }

    pub fn split_before(&mut self) -> LinkedList<T, A> {
        self.cursor.list.len -= self.index;
        unsafe {
            LinkedList {
                len: mem::replace(&mut self.index, 0),
                list: self
                    .cursor
                    .list
                    .list
                    .split_before_with_pointer(self.cursor.pointer),
            }
        }
    }

    pub fn is_dummy(&self) -> bool {
        self.cursor.is_dummy()
    }

    pub fn index(&self) -> usize {
        self.index
    }

    pub fn get(&self) -> Option<&T> {
        self.cursor.get()
    }

    pub fn get_mut(&mut self) -> Option<&mut T> {
        self.cursor.get_mut()
    }

    pub fn downgrade(self) -> CursorMutWithoutIndex<'a, T, A> {
        self.cursor
    }
}

impl<'a, T, A: Allocator + Clone> CursorMut<'a, T, A> {
    pub fn cut_current(&mut self) -> Option<T> {
        self.cut_node_current().map(|node| node.into_value())
    }

    pub fn insert_after(&mut self, value: T) {
        self.cursor.insert_after(value);
        if self.cursor.pointer.is_none() {
            self.index = self.cursor.list.len;
        }
    }

    pub fn insert_before(&mut self, value: T) {
        self.index += 1;
        self.cursor.insert_before(value);
    }
}

impl<'a, T, A: Allocator + Clone> From<CursorMut<'a, T, A>> for CursorMutWithoutIndex<'a, T, A> {
    fn from(value: CursorMut<'a, T, A>) -> Self {
        value.cursor
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn push_pop() {
        let mut list = LinkedList::new();
        list.push_front("abc".to_owned());
        list.push_front("def".to_owned());
        list.push_front("ghij".to_owned());

        assert_eq!(list.len(), 3);
        assert_eq!(list.pop_back().unwrap().as_str(), "abc");
        assert_eq!(list.pop_back().unwrap().as_str(), "def");
        assert_eq!(list.pop_back().unwrap().as_str(), "ghij");
        assert_eq!(list.pop_back(), None);
        assert_eq!(list.len(), 0);
    }

    #[test]
    fn test2() {
        let mut list = LinkedList::new();
        list.push_back(100i32);
        list.push_back(88);
        list.push_front(105);
        list.push_front(110);

        assert_eq!(list.len(), 4);
        assert_eq!(list.pop_back().unwrap(), 88);
        assert_eq!(list.len(), 3);
        assert_eq!(list.pop_front().unwrap(), 110);
        assert_eq!(list.len(), 2);
        assert_eq!(list.pop_back().unwrap(), 100);
        assert_eq!(list.len(), 1);
        assert_eq!(list.pop_front().unwrap(), 105);
        assert_eq!(list.len(), 0);
        assert_eq!(list.pop_front(), None);
        assert_eq!(list.len(), 0);
    }

    use detect_drop::DetectDrop;
    fn check_send<T: Send>(_: &T) {}
    fn check_sync<T: Sync>(_: &T) {}

    #[test]
    fn check_drop() {
        let mut list = LinkedList::new();
        check_send(&list);
        check_sync(&list);
        list.push_back(DetectDrop(1));
        list.push_back(DetectDrop(2));
        list.push_back(DetectDrop(3));
        list.push_back(DetectDrop(4));
        list.pop_back().unwrap().into_inner();
    }

    #[test]
    fn iterator() {
        let mut list: LinkedList<_> = [1i32, 3, 4, 6, 7].into_iter().collect();
        assert_eq!(list.len(), 5);
        for (i, elem) in list.iter_mut().rev().enumerate() {
            *elem *= (i + 1) as i32;
        }
        println!("{list:?}");
        println!("{:?}", [1, 2, 3, 4, 5]);
    }

    #[test]
    fn append_test() {
        let mut list = (1i32..=10).collect::<LinkedList<_>>();
        let mut list2 = (11i32..=20).collect::<LinkedList<_>>();
        assert_eq!(list.len(), 10);
        assert_eq!(list2.len(), 10);
        list.append(&mut list2);

        assert_eq!(list.len(), 20);
        assert_eq!(list2.len(), 0);
        assert!(list.into_iter().eq(1..=20));
    }

    #[test]
    fn cursor_test() {
        let mut list = [2, 4, 5, 6, 8].into_iter().collect::<LinkedList<_>>();
        assert_eq!(list.len(), 5);
        let mut cursor = list.cursor_front_mut();

        assert!(!cursor.is_dummy());
        cursor.move_next();
        assert!(!cursor.is_dummy());
        assert_eq!(*cursor.get().unwrap(), 4);
        cursor.move_next();
        assert_eq!(*cursor.get().unwrap(), 5);
        assert_eq!(cursor.cut_current().unwrap(), 5);
        assert_eq!(cursor.list().len(), 4);
        assert_eq!(*cursor.get().unwrap(), 6);
        cursor.move_next();
        assert_eq!(*cursor.get().unwrap(), 8);
        cursor.move_next();
        assert!(cursor.is_dummy());
        assert!(cursor.get().is_none());
        cursor.move_next();
        assert!(!cursor.is_dummy());
        assert_eq!(*cursor.get().unwrap(), 2);

        for _ in 0..4 {
            cursor.remove_current();
        }
        assert_eq!(cursor.list().len(), 0);
        assert!(cursor.is_dummy());
        cursor.move_next();
        assert!(cursor.is_dummy());

        cursor.insert_after(30);
        assert_eq!(cursor.list().len(), 1);
        cursor.insert_after(25);
        assert_eq!(cursor.list().len(), 2);
        cursor.move_next();
        cursor.insert_after(28);
        assert_eq!(cursor.list().len(), 3);
        cursor.move_next();
        cursor.insert_after(29);
        assert_eq!(cursor.list().len(), 4);
        assert!(cursor.list().iter().eq(&[25, 28, 29, 30]));
    }

    #[test]
    fn splice_test() {
        let mut list = (-3i32..4).collect::<LinkedList<_>>();
        let mut cursor = list.cursor_back_mut();
        for _ in 0..3 {
            cursor.move_prev();
        }
        let list2 = [7, 10, 11].into_iter().collect::<LinkedList<_>>();
        assert_eq!(cursor.cut_current().unwrap(), 0);
        cursor.move_prev();
        cursor.splice_after(list2);
        assert!(cursor.list().iter().eq(&[-3, -2, -1, 7, 10, 11, 1, 2, 3]));

        let mut cursor = list.cursor_back_mut();
        cursor.splice_after([0, -3].into_iter().collect());
        assert!(cursor
            .list()
            .iter()
            .eq(&[-3, -2, -1, 7, 10, 11, 1, 2, 3, 0, -3]));

        cursor.splice_after(LinkedList::new());
        assert!(cursor
            .list()
            .iter()
            .eq(&[-3, -2, -1, 7, 10, 11, 1, 2, 3, 0, -3]));

        let mut cursor = list.cursor_back_mut();
        cursor.splice_after(LinkedList::new());
        assert!(cursor
            .list()
            .iter()
            .eq(&[-3, -2, -1, 7, 10, 11, 1, 2, 3, 0, -3]));

        list.clear();
        let mut cursor = list.cursor_front_mut();
        cursor.splice_before([1, 2, 3, 4].into_iter().collect());
        assert!(cursor.list().iter().eq(&[1, 2, 3, 4]));

        cursor.splice_before([5, 6].into_iter().collect());
        assert!(cursor.list().iter().copied().eq(1..=6));
        let tail_old = cursor.list().pointer_back().unwrap();
        cursor.list().append(&mut [9, 10, 11].into_iter().collect());
        let mut cursor = cursor.downgrade();
        unsafe { cursor.set_from_pointer(tail_old) };
        cursor.splice_after([7, 8].into_iter().collect());
        assert!(cursor.list().iter().copied().eq(1..=11));
    }

    #[test]
    fn split_test() {
        let mut list = LinkedList::new();
        let mut cursor = list.cursor_front_mut();

        cursor.splice_after((3i32..6).collect());
        cursor.move_next();
        cursor.splice_before((3..6).rev().collect());
        assert!(cursor.list().iter().eq(&[5, 4, 3, 3, 4, 5]));

        cursor.move_prev();
        cursor.move_prev();
        let splitted = cursor.split_after();
        assert!(splitted.iter().eq(&[3, 3, 4, 5]));
        assert!(list.iter().eq(&[5, 4]));

        let mut cursor = list.cursor_front_mut();
        cursor.splice_before(splitted);
        assert!(list.iter().eq(&[3, 3, 4, 5, 5, 4]));
    }

    #[test]
    fn set_index_test() {
        let mut list = LinkedList::from([2u32, 6, 9, 3, 9, 9]);
        let mut cursor = list.cursor_back_mut();
        let index = cursor.index;
        cursor.insert_after(5);
        cursor.insert_after(7);
        let cursor = cursor.downgrade();
        let cursor = cursor.add_index();
        assert_eq!(index, cursor.index());
    }

    // TODO: allocator tests
}
