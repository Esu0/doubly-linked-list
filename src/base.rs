use std::{
    fmt::{self, Debug},
    marker::PhantomData,
    mem::{self, ManuallyDrop},
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

pub struct LinkedList<T: ?Sized> {
    head: Link<T>,
    tail: Link<T>,
}

unsafe impl<T: Send> Send for LinkedList<T> {}
unsafe impl<T: Sync> Sync for LinkedList<T> {}

type Link<T> = Option<NonNull<Node<T>>>;

#[derive(Debug)]
pub(crate) struct Node<T: ?Sized> {
    prev: Link<T>,
    next: Link<T>,
    value: T,
}

impl<T> LinkedList<T> {
    fn new_node_ptr(node: Node<T>) -> NonNull<Node<T>> {
        Box::leak(Box::new(node)).into()
    }

    pub fn push_front(&mut self, value: T) {
        let new_node = Self::new_node_ptr(Node {
            prev: None,
            next: self.head,
            value,
        });
        if let Some(mut head) = self.head {
            unsafe {
                head.as_mut().prev = Some(new_node);
            }
        } else {
            self.tail = Some(new_node);
        }
        self.head = Some(new_node);
    }

    pub fn push_back(&mut self, value: T) {
        let new_node = Self::new_node_ptr(Node {
            prev: self.tail,
            next: None,
            value,
        });

        if let Some(mut tail) = self.tail {
            unsafe {
                tail.as_mut().next = Some(new_node);
            }
        } else {
            self.head = Some(new_node);
        }
        self.tail = Some(new_node);
    }

    pub fn pop_front(&mut self) -> Option<T> {
        self.pop_node_front().map(|node| node.value)
    }

    pub fn pop_back(&mut self) -> Option<T> {
        self.pop_node_back().map(|node| node.value)
    }

    fn pop_node_front(&mut self) -> Option<Node<T>> {
        self.head.map(|head| {
            unsafe {
                self.head = head.as_ref().next;
            }
            if self.tail == Some(head) {
                self.tail = None;
            } else {
                unsafe {
                    self.head.unwrap_unchecked().as_mut().prev = None;
                }
            }
            unsafe { *Box::from_raw(head.as_ptr()) }
        })
    }

    fn pop_node_back(&mut self) -> Option<Node<T>> {
        self.tail.map(|tail| {
            unsafe {
                self.tail = tail.as_ref().prev;
            }
            if self.head == Some(tail) {
                self.head = None;
            } else {
                unsafe {
                    self.tail.unwrap_unchecked().as_mut().next = None;
                }
            }
            unsafe { *Box::from_raw(tail.as_ptr()) }
        })
    }
}

impl<T: ?Sized> LinkedList<T> {
    pub const fn new() -> Self {
        Self {
            head: None,
            tail: None,
        }
    }

    pub const fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    pub(crate) unsafe fn iter_ptr(&self) -> IterPtr<T> {
        IterPtr {
            head: self.head,
            tail: self.tail,
        }
    }

    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            iter_ptr: unsafe { self.iter_ptr() },
            _marker: PhantomData,
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            iter_ptr: unsafe { self.iter_ptr() },
            _marker: PhantomData,
        }
    }

    pub fn front(&self) -> Option<&T> {
        self.head.map(|head| unsafe { &(*head.as_ptr()).value })
    }

    pub fn back(&self) -> Option<&T> {
        self.tail.map(|tail| unsafe { &(*tail.as_ptr()).value })
    }

    pub fn front_mut(&mut self) -> Option<&mut T> {
        self.head.map(|head| unsafe { &mut (*head.as_ptr()).value })
    }

    pub fn back_mut(&mut self) -> Option<&mut T> {
        self.tail.map(|tail| unsafe { &mut (*tail.as_ptr()).value })
    }

    pub fn cursor_front(&self) -> Option<Cursor<'_, T>> {
        self.head.map(|head| Cursor(head, PhantomData))
    }

    pub fn cursor_back(&self) -> Option<Cursor<'_, T>> {
        self.tail.map(|tail| Cursor(tail, PhantomData))
    }

    pub fn indexer_front(&self) -> Option<Indexer<T>> {
        self.head.map(|head| Indexer(head))
    }

    pub fn indexer_back(&self) -> Option<Indexer<T>> {
        self.tail.map(|tail| Indexer(tail))
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
            iter_ptr: unsafe { slf.iter_ptr() },
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
    iter_ptr: IterPtr<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_ptr
            .next()
            .map(|ptr| unsafe { Box::from_raw(ptr.as_ptr()).value })
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter_ptr
            .next_back()
            .map(|ptr| unsafe { Box::from_raw(ptr.as_ptr()).value })
    }
}
pub struct Iter<'a, T: ?Sized> {
    iter_ptr: IterPtr<T>,
    _marker: PhantomData<&'a LinkedList<T>>,
}

impl<'a, T: ?Sized> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_ptr
            .next()
            .map(|ptr| unsafe { &(*ptr.as_ptr()).value })
    }
}

impl<'a, T: ?Sized> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter_ptr
            .next_back()
            .map(|ptr| unsafe { &(*ptr.as_ptr()).value })
    }
}

pub struct IterMut<'a, T: ?Sized> {
    iter_ptr: IterPtr<T>,
    _marker: PhantomData<&'a mut LinkedList<T>>,
}

impl<'a, T: ?Sized> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_ptr
            .next()
            .map(|ptr| unsafe { &mut (*ptr.as_ptr()).value })
    }
}

impl<'a, T: ?Sized> DoubleEndedIterator for IterMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter_ptr
            .next_back()
            .map(|ptr| unsafe { &mut (*ptr.as_ptr()).value })
    }
}

pub(crate) struct IterPtr<T: ?Sized> {
    head: Link<T>,
    tail: Link<T>,
}

impl<T: ?Sized> Iterator for IterPtr<T> {
    type Item = NonNull<Node<T>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.head.map(|head| {
            if self.head == self.tail {
                self.tail = None;
                self.head = None;
            } else {
                self.head = unsafe { head.as_ref().next };
            }
            head
        })
    }
}

impl<T: ?Sized> DoubleEndedIterator for IterPtr<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.tail.map(|tail| {
            if self.head == self.tail {
                self.tail = None;
                self.head = None;
            } else {
                self.tail = unsafe { tail.as_ref().prev };
            }
            tail
        })
    }
}

impl<T: ?Sized> Drop for LinkedList<T> {
    fn drop(&mut self) {
        unsafe {
            self.iter_ptr()
                .for_each(|ptr| drop(Box::from_raw(ptr.as_ptr())));
        }
    }
}

impl<T: Debug + ?Sized> Debug for LinkedList<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut iter = self.iter();
        write!(f, "[")?;
        if let Some(val) = iter.next() {
            write!(f, "{val:?}")?;
            for val in iter {
                write!(f, ", {val:?}")?;
            }
        }
        writeln!(f, "]")
    }
}

impl<T: ?Sized> Default for LinkedList<T> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct Indexer<T: ?Sized>(NonNull<Node<T>>);
pub struct Cursor<'a, T: ?Sized>(NonNull<Node<T>>, PhantomData<&'a LinkedList<T>>);

impl<T: ?Sized> Clone for Cursor<'_, T> {
    fn clone(&self) -> Self {
        Self(self.0, PhantomData)
    }
}

impl<T: ?Sized> Copy for Cursor<'_, T> {}

impl<T: ?Sized> Deref for Cursor<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &self.0.as_ref().value }
    }
}

impl<'a, T: ?Sized> Cursor<'a, T> {
    pub fn move_next(&mut self) -> bool {
        if let Some(next) = unsafe { self.0.as_ref().next } {
            self.0 = next;
            true
        } else {
            false
        }
    }

    pub fn move_prev(&mut self) -> bool {
        if let Some(prev) = unsafe { self.0.as_ref().prev } {
            self.0 = prev;
            true
        } else {
            false
        }
    }
}

pub struct CursorMut<'a, T: ?Sized> {
    ptr: NonNull<Node<T>>,
    list: &'a mut LinkedList<T>,
}

impl<T: ?Sized> Deref for CursorMut<'_, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        unsafe { &self.ptr.as_ref().value }
    }
}

impl<T: ?Sized> DerefMut for CursorMut<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut self.ptr.as_mut().value }
    }
}

impl<'a, T: ?Sized> CursorMut<'a, T> {
    // 次の要素に移動
    pub fn move_next(&mut self) -> bool {
        if let Some(next) = unsafe { self.ptr.as_ref().next } {
            self.ptr = next;
            true
        } else {
            false
        }
    }

    pub fn move_prev(&mut self) -> bool {
        if let Some(prev) = unsafe { self.ptr.as_ref().prev } {
            self.ptr = prev;
            true
        } else {
            false
        }
    }

    pub fn remove_current(&mut self) {
        drop(self.cut_node_current());
    }

    fn node(&mut self) -> &Node<T> {
        unsafe { self.ptr.as_ref() }
    }

    fn node_mut(&mut self) -> &mut Node<T> {
        unsafe { self.ptr.as_mut() }
    }

    fn cut_node_current(&mut self) -> Box<Node<T>> {
        let node = self.node();
        let prev = node.prev;
        let next = node.next;
        if let Some(mut prev) = prev {
            unsafe { prev.as_mut().next = next; }
        } else {
            self.list.head = next;
        }

        if let Some(mut next) = next {
            unsafe { next.as_mut().prev = prev; }
        } else {
            self.list.tail = prev;
        }
        // TODO: リストが空になる場合にどうするか
        unsafe { Box::from_raw(mem::replace(&mut self.ptr, next.unwrap()).as_ptr()) }
    }
}

impl<'a, T> CursorMut<'a, T> {
    pub fn cut_current(&mut self) -> T {
        self.cut_node_current().value
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

        assert_eq!(list.pop_back().unwrap().as_str(), "abc");
        assert_eq!(list.pop_back().unwrap().as_str(), "def");
        assert_eq!(list.pop_back().unwrap().as_str(), "ghij");
        assert_eq!(list.pop_back(), None);
    }

    #[test]
    fn test2() {
        let mut list = LinkedList::new();
        list.push_back(100i32);
        list.push_back(88);
        list.push_front(105);
        list.push_front(110);

        assert_eq!(list.pop_back().unwrap(), 88);
        assert_eq!(list.pop_front().unwrap(), 110);
        assert_eq!(list.pop_back().unwrap(), 100);
        assert_eq!(list.pop_front().unwrap(), 105);
        assert_eq!(list.pop_front(), None);
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
        for (i, elem) in list.iter_mut().rev().enumerate() {
            *elem *= (i + 1) as i32;
        }
        println!("{list:?}");
        println!("{:?}", [1, 2, 3, 4, 5]);
    }
}
