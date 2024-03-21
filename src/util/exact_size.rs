use std::{
    fmt::{self, Debug},
    marker::PhantomData,
    mem::{self, ManuallyDrop},
    ptr::NonNull,
};

use crate::base::{self as base, IterPtr, Node};

pub struct LinkedList<T: ?Sized> {
    list: base::LinkedList<T>,
    len: usize,
}

impl<T> LinkedList<T> {
    pub fn push_front(&mut self, value: T) {
        self.len += 1;
        self.list.push_front(value);
    }

    pub fn push_back(&mut self, value: T) {
        self.len += 1;
        self.list.push_back(value);
    }

    pub fn pop_front(&mut self) -> Option<T> {
        self.len -= 1;
        self.list.pop_front()
    }

    pub fn pop_back(&mut self) -> Option<T> {
        self.len -= 1;
        self.list.pop_back()
    }
}

impl<T: ?Sized> LinkedList<T> {
    pub const fn new() -> Self {
        Self {
            list: base::LinkedList::new(),
            len: 0,
        }
    }

    pub const fn is_empty(&self) -> bool {
        self.list.is_empty()
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

    pub fn cursor_front_mut(&mut self) -> CursorMut<'_, T> {
        CursorMut {
            cursor: CursorMutWithoutIndex {
                inner: self.list.cursor_front_mut(),
            },
            index: 0,
        }
    }

    pub fn cursor_back_mut(&mut self) -> CursorMut<'_, T> {
        CursorMut {
            cursor: CursorMutWithoutIndex {
                inner: self.list.cursor_back_mut(),
            },
            index: self.len.checked_sub(1).unwrap_or(0),
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
        *self = Self::new();
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
        self.len -= 1;
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
        self.len -= 1;
        self.iter.next_back()
    }
}

impl<T: ?Sized> ExactSizeIterator for IterPtrWithLen<T> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<I> FromIterator<I> for LinkedList<I> {
    fn from_iter<T: IntoIterator<Item = I>>(iter: T) -> Self {
        let mut list = Self::new();
        for item in iter {
            list.push_back(item);
        }
        list
    }
}

impl<T> IntoIterator for LinkedList<T> {
    type IntoIter = IntoIter<T>;
    type Item = T;

    fn into_iter(self) -> Self::IntoIter {
        let slf = ManuallyDrop::new(self);
        IntoIter {
            iter_ptr: slf.iter_ptr(),
            _marker: PhantomData,
        }
    }
}

impl<'a, T: ?Sized> IntoIterator for &'a LinkedList<T> {
    type IntoIter = Iter<'a, T>;
    type Item = &'a T;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T: ?Sized> IntoIterator for &'a mut LinkedList<T> {
    type IntoIter = IterMut<'a, T>;
    type Item = &'a mut T;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

pub struct IntoIter<T> {
    iter_ptr: IterPtrWithLen<T>,
    _marker: PhantomData<LinkedList<T>>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_ptr
            .next()
            .map(|ptr| unsafe { Box::from_raw(ptr.as_ptr()).into_value() })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter_ptr.size_hint()
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter_ptr
            .next_back()
            .map(|ptr| unsafe { Box::from_raw(ptr.as_ptr()).into_value() })
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {
    fn len(&self) -> usize {
        self.iter_ptr.len()
    }
}

impl<T> Drop for IntoIter<T> {
    fn drop(&mut self) {
        unsafe {
            // lenの変更を避けてdrop
            drop(base::IntoIter::from_iter_ptr(self.iter_ptr.iter.clone()))
        }
    }
}

pub struct Iter<'a, T: ?Sized> {
    iter_ptr: IterPtrWithLen<T>,
    _marker: PhantomData<&'a LinkedList<T>>,
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
    _marker: PhantomData<&'a mut LinkedList<T>>,
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

impl<T: Debug + ?Sized> Debug for LinkedList<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.list.fmt(f)
    }
}

impl<T: ?Sized> Default for LinkedList<T> {
    fn default() -> Self {
        Self::new()
    }
}

// TODO: impl PartialEq for LinkedList
// TODO: impl Eq for LinkedList
// TODO: impl PartialOrd for LinkedList
// TODO: impl Ord for LinkedList

pub struct Pointer<T: ?Sized> {
    inner: base::Pointer<T>,
}

impl<T: ?Sized> From<base::Pointer<T>> for Pointer<T> {
    fn from(value: base::Pointer<T>) -> Self {
        Self { inner: value }
    }
}
impl<T: ?Sized> Clone for Pointer<T> {
    fn clone(&self) -> Self {
        Self { inner: self.inner }
    }
}

impl<T: ?Sized> Copy for Pointer<T> {}

impl<T: ?Sized> Pointer<T> {
    pub unsafe fn next(self) -> Option<Self> {
        self.inner.next().map(Self::from)
    }

    pub unsafe fn prev(self) -> Option<Self> {
        self.inner.prev().map(Self::from)
    }
}

impl<T: ?Sized> LinkedList<T> {
    pub unsafe fn remove(&mut self, pointer: Pointer<T>) {
        self.len -= 1;
        self.list.remove(pointer.inner);
    }

    pub unsafe fn get(&self, pointer: Pointer<T>) -> &T {
        self.list.get(pointer.inner)
    }

    pub unsafe fn get_mut(&mut self, pointer: Pointer<T>) -> &mut T {
        self.list.get_mut(pointer.inner)
    }

    pub unsafe fn get_cursor(&self, pointer: Pointer<T>) -> Cursor<'_, T> {
        self.list.get_cursor(pointer.inner)
    }
}

pub type Cursor<'a, T> = base::Cursor<'a, T>;

impl<'a, T: ?Sized> Cursor<'a, T> {}
pub struct CursorMutWithoutIndex<'a, T: ?Sized> {
    inner: base::CursorMut<'a, T>,
}

impl<'a, T: ?Sized> CursorMutWithoutIndex<'a, T> {
    pub fn move_next(&mut self) {
        self.inner.move_next()
    }

    pub fn move_prev(&mut self) {
        self.inner.move_prev()
    }

    // TODO: add functions
}
pub struct CursorMut<'a, T: ?Sized> {
    cursor: CursorMutWithoutIndex<'a, T>,
    index: usize,
}
