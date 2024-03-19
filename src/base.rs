use std::{
    fmt::{self, Debug},
    marker::PhantomData,
    mem::ManuallyDrop,
    ops::Deref,
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
        self.indexer_front()
            .map(|indexer| Cursor(indexer, PhantomData))
    }

    pub fn cursor_back(&self) -> Option<Cursor<'_, T>> {
        self.indexer_back()
            .map(|indexer| Cursor(indexer, PhantomData))
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

impl<T: ?Sized> Clone for Indexer<T> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}

impl<T: ?Sized> Copy for Indexer<T> {}

impl<T: ?Sized> Indexer<T> {
    unsafe fn into_boxed_node(self) -> Box<Node<T>> {
        Box::from_raw(self.0.as_ptr())
    }

    unsafe fn get<'a>(self) -> &'a Node<T> {
        &*self.0.as_ptr()
    }

    unsafe fn get_mut<'a>(self) -> &'a mut Node<T> {
        &mut *self.0.as_ptr()
    }

    /// # Safety
    /// * `self`の差すノードが有効である
    pub unsafe fn next(self) -> Option<Self> {
        self.0.as_ref().next.map(Self)
    }

    /// # Safety
    /// * `self`の差すノードが有効である
    pub unsafe fn prev(self) -> Option<Self> {
        self.0.as_ref().prev.map(Self)
    }
}

impl<T: ?Sized> LinkedList<T> {
    /// # Safety
    /// * `index`の指すノードがリスト`self`が所有する有効なノードである
    pub unsafe fn remove(&mut self, index: Indexer<T>) {
        drop(self.cut_node(index));
    }

    unsafe fn cut_node(&mut self, index: Indexer<T>) -> Box<Node<T>> {
        let (prev, next) = {
            let node = index.0.as_ref();
            (node.prev, node.next)
        };

        if let Some(mut prev) = prev {
            prev.as_mut().next = next;
        } else {
            self.head = next;
        }

        if let Some(mut next) = next {
            next.as_mut().prev = prev;
        } else {
            self.tail = prev;
        }

        index.into_boxed_node()
    }

    /// # Safety
    /// * `index`の指すノードがリスト`self`が所有する有効なノードである
    pub unsafe fn get(&self, index: Indexer<T>) -> &T {
        &(*index.0.as_ptr()).value
    }

    /// # Safety
    /// * `index`の指すノードがリスト`self`が所有する有効なノードである
    pub unsafe fn get_mut(&mut self, index: Indexer<T>) -> &mut T {
        &mut (*index.0.as_ptr()).value
    }

    /// # Safety
    /// * `index`の指すノードがリスト`self`が所有する有効なノードである
    pub unsafe fn get_cursor(&self, index: Indexer<T>) -> Cursor<'_, T> {
        Cursor(index, PhantomData)
    }
}

pub struct Cursor<'a, T: ?Sized>(Indexer<T>, PhantomData<&'a LinkedList<T>>);

impl<T: ?Sized> Clone for Cursor<'_, T> {
    fn clone(&self) -> Self {
        Self(self.0, PhantomData)
    }
}

impl<T: ?Sized> Copy for Cursor<'_, T> {}

impl<T: ?Sized> Deref for Cursor<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &self.0.get().value }
    }
}

impl<'a, T: ?Sized> Cursor<'a, T> {
    /// 一つ次のノードを指すカーソルを返す。一つ次のノードが存在しない場合は`None`を返す。
    pub fn next(self) -> Option<Self> {
        unsafe { self.0.next().map(|next| Self(next, PhantomData)) }
    }

    /// 一つ前のノードを指すカーソルを返す。一つ前のノードが存在しない場合は`None`を返す。
    pub fn prev(self) -> Option<Self> {
        unsafe { self.0.prev().map(|prev| Self(prev, PhantomData)) }
    }
}

pub struct CursorMut<'a, T: ?Sized> {
    index: Option<Indexer<T>>,
    list: &'a mut LinkedList<T>,
}

impl<'a, T: ?Sized> CursorMut<'a, T> {
    /// カーソルを一つ次のノードに移動する。一つ次のノードが存在しない場合はダミーノードを指すように変更される。
    pub fn move_next(&mut self) {
        if let Some(index) = self.index {
            self.index = unsafe { index.next() };
        }
    }

    /// カーソルを一つ前のノードに移動する。一つ前のノードが存在しない場合はダミーノードを指すように変更される。
    pub fn move_prev(&mut self) {
        if let Some(index) = self.index {
            self.index = unsafe { index.prev() };
        }
    }

    /// 現在指しているノードをリストから削除する。このとき、カーソルを次のノードに移動する。
    /// 現在指しているノードがダミーノードなら何もしない。
    pub fn remove_current(&mut self) {
        drop(self.cut_node_current());
    }

    /// 現在指しているノードの値の共有参照を取得する。ダミーノードを指している場合は`None`を返す。
    pub fn get(&self) -> Option<&T> {
        self.node().map(|node| &node.value)
    }

    /// 現在指しているノードの値の排他参照を取得する。ダミーノードを指している場合は`None`を返す。
    pub fn get_mut(&mut self) -> Option<&mut T> {
        self.node_mut().map(|node| &mut node.value)
    }

    /// ダミーノードを指している場合に`true`を返し、それ以外のときに`false`を返す
    pub const fn is_dummy(&self) -> bool {
        self.index.is_none()
    }

    fn node(&self) -> Option<&Node<T>> {
        unsafe { self.index.map(|index| index.get()) }
    }

    fn node_mut(&mut self) -> Option<&mut Node<T>> {
        unsafe { self.index.map(|index| index.get_mut()) }
    }

    fn cut_node_current(&mut self) -> Option<Box<Node<T>>> {
        self.index.map(|index| unsafe {
            self.index = index.next();
            self.list.cut_node(index)
        })
    }
}

impl<'a, T> CursorMut<'a, T> {
    /// 現在指しているノードをリストから削除して値を返す。このとき、カーソルを次のノードに移動する。
    /// 現在指しているノードがダミーノードなら何もしない。
    pub fn cut_current(&mut self) -> Option<T> {
        self.cut_node_current().map(|node| node.value)
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
