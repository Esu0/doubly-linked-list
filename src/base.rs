use std::{
    fmt::{self, Debug},
    marker::PhantomData,
    mem::{self, ManuallyDrop},
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

    pub fn cursor_front_mut(&mut self) -> CursorMut<'_, T> {
        CursorMut {
            indexer: self.indexer_front(),
            list: self,
        }
    }

    pub fn cursor_back_mut(&mut self) -> CursorMut<'_, T> {
        CursorMut {
            indexer: self.indexer_back(),
            list: self,
        }
    }

    pub fn indexer_front(&self) -> Option<Indexer<T>> {
        self.head.map(|head| Indexer(head))
    }

    pub fn indexer_back(&self) -> Option<Indexer<T>> {
        self.tail.map(|tail| Indexer(tail))
    }

    pub fn append(&mut self, other: &mut Self) {
        let Some(mut other_head) = other.head else {
            // otherが空なので何もしない
            return;
        };
        debug_assert!(other.tail.is_some());

        if let Some(tail) = &mut self.tail {
            // いずれも空でない
            let new_tail = unsafe { other.tail.unwrap_unchecked() };
            unsafe {
                tail.as_mut().next = Some(other_head);
                other_head.as_mut().prev = Some(*tail);
            }
            *tail = new_tail;
        } else {
            // selfが空
            self.head = Some(other_head);
            self.tail = other.tail;
        }
        other.head = None;
        other.tail = None;
    }

    pub fn clear(&mut self) {
        *self = Self::new();
    }

    fn get_head_tail(&self) -> Option<(NonNull<Node<T>>, NonNull<Node<T>>)> {
        self.head
            .map(|head| (head, unsafe { self.tail.unwrap_unchecked() }))
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

impl<T: PartialEq> PartialEq for LinkedList<T> {
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other.iter())
    }

    fn ne(&self, other: &Self) -> bool {
        self.iter().ne(other.iter())
    }
}

impl<T: Eq> Eq for LinkedList<T> {}

impl<T: PartialOrd> PartialOrd for LinkedList<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.iter().partial_cmp(other.iter())
    }

    fn ge(&self, other: &Self) -> bool {
        self.iter().ge(other.iter())
    }

    fn gt(&self, other: &Self) -> bool {
        self.iter().gt(other.iter())
    }

    fn le(&self, other: &Self) -> bool {
        self.iter().le(other.iter())
    }

    fn lt(&self, other: &Self) -> bool {
        self.iter().lt(other.iter())
    }
}

impl<T: Ord> Ord for LinkedList<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.iter().cmp(other.iter())
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
    indexer: Option<Indexer<T>>,
    list: &'a mut LinkedList<T>,
}

impl<'a, T: ?Sized> CursorMut<'a, T> {
    /// カーソルを一つ次のノードに移動する。一つ次のノードが存在しない場合はダミーノードを指すように変更される。
    /// ダミーノードを指している場合はリストの先頭に移動する。
    pub fn move_next(&mut self) {
        if let Some(index) = self.indexer {
            self.indexer = unsafe { index.next() };
        } else {
            self.indexer = self.list.indexer_front();
        }
    }

    /// カーソルを一つ前のノードに移動する。一つ前のノードが存在しない場合はダミーノードを指すように変更される。
    /// ダミーノードを指している場合はリストの末尾に移動する。
    pub fn move_prev(&mut self) {
        if let Some(index) = self.indexer {
            self.indexer = unsafe { index.prev() };
        } else {
            self.indexer = self.list.indexer_back();
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
        self.indexer.is_none()
    }

    fn node(&self) -> Option<&Node<T>> {
        unsafe { self.indexer.map(|index| index.get()) }
    }

    fn node_mut(&mut self) -> Option<&mut Node<T>> {
        unsafe { self.indexer.map(|index| index.get_mut()) }
    }

    fn cut_node_current(&mut self) -> Option<Box<Node<T>>> {
        self.indexer.map(|index| unsafe {
            self.indexer = index.next();
            self.list.cut_node(index)
        })
    }

    /// # Safety
    /// * `indexer`が指すノードとカーソルが指すノードが同じリストに属する。カーソルがダミーノードを指している場合もこれを満たす必要がある。
    pub unsafe fn set_index(&mut self, indexer: Indexer<T>) {
        self.indexer = Some(indexer);
    }

    pub fn list(&mut self) -> &mut LinkedList<T> {
        self.list
    }

    pub fn splice_after(&mut self, list: LinkedList<T>) {
        let Some((mut list_head, mut list_tail)) = list.get_head_tail() else {
            // リストは空なので何もしない
            return;
        };
        // `LinkedList::drop()`を呼ばないようにする
        mem::forget(list);
        unsafe {
            // `list`の末尾とリンクすべきノード
            let next = if let Some(indexer) = self.indexer {
                // ダミーノードを指していない => 先頭ノードの変更はなし
                list_head.as_mut().prev = Some(indexer.0);
                indexer.get_mut().next.replace(list_head)

                // `indexer.get_mut().next`が`None`のときは末尾に挿入することになる
                // よって、`list`の末尾とリンクすべきノードは存在しない
            } else {
                debug_assert!(list_head.as_ref().prev.is_none());
                // ダミーノードを指している => 先頭ノードを変更
                // `(*list_head).prev`は`None`であることが保証されているため
                // 変更しなくてよい
                self.list.head.replace(list_head)

                // `self.list.head`が`None`のときはリストが空であるから、
                //　`list`の末尾とリンクすべきノードは存在しない
            };

            if let Some(mut next) = next {
                next.as_mut().prev = Some(list_tail);
                list_tail.as_mut().next = Some(next);
            } else {
                debug_assert!(list_tail.as_ref().next.is_none());
                // `next`が`None`のときは末尾ノードを変更する必要がある
                self.list.tail = Some(list_tail);
            }
        }
    }

    pub fn splice_before(&mut self, list: LinkedList<T>) {
        let Some((mut list_head, mut list_tail)) = list.get_head_tail() else {
            return;
        };
        mem::forget(list);
        unsafe {
            let prev = if let Some(indexer) = self.indexer {
                list_tail.as_mut().next = Some(indexer.0);
                indexer.get_mut().prev.replace(list_tail)
            } else {
                debug_assert!(list_tail.as_ref().next.is_none());
                self.list.tail.replace(list_tail)
            };

            if let Some(mut prev) = prev {
                prev.as_mut().next = Some(list_head);
                list_head.as_mut().prev = Some(prev);
            } else {
                debug_assert!(list_head.as_ref().prev.is_none());
                self.list.head = Some(list_head);
            }
        }
    }

    pub fn split_after(&mut self) -> LinkedList<T> {
        unsafe {
            if let Some(indexer) = self.indexer {
                let head = indexer.get_mut().next.take();
                if let Some(mut head) = head {
                    let tail = self.list.tail.replace(indexer.0);
                    head.as_mut().prev = None;
                    LinkedList {
                        head: Some(head),
                        tail,
                    }
                } else {
                    LinkedList::new()
                }
            } else {
                LinkedList {
                    head: self.list.head.take(),
                    tail: self.list.tail.take(),
                }
            }
        }
    }

    pub fn split_before(&mut self) -> LinkedList<T> {
        unsafe {
            if let Some(indexer) = self.indexer {
                let tail = indexer.get_mut().prev.take();
                if let Some(mut tail) = tail {
                    let head = self.list.head.replace(indexer.0);
                    tail.as_mut().next = None;
                    LinkedList {
                        head,
                        tail: Some(tail),
                    }
                } else {
                    LinkedList::new()
                }
            } else {
                LinkedList {
                    head: self.list.head.take(),
                    tail: self.list.tail.take(),
                }
            }
        }
    }
}

impl<'a, T> CursorMut<'a, T> {
    /// 現在指しているノードをリストから削除して値を返す。このとき、カーソルを次のノードに移動する。
    /// 現在指しているノードがダミーノードなら何もしない。
    pub fn cut_current(&mut self) -> Option<T> {
        self.cut_node_current().map(|node| node.value)
    }

    pub fn insert_after(&mut self, value: T) {
        if let Some(indexer) = self.indexer {
            // ダミーノードでない = 挿入位置は先頭でない
            let next = unsafe { &mut indexer.get_mut().next };
            let new_node = LinkedList::new_node_ptr(Node {
                prev: Some(indexer.0),
                next: *next,
                value,
            });
            if let Some(mut next) = next.replace(new_node) {
                // 次のノードが存在する
                unsafe {
                    next.as_mut().prev = Some(new_node);
                }
            } else {
                // 次のノードが存在しない = 現在位置は末尾
                self.list.tail = Some(new_node);
            }
        } else {
            // ダミーノードを指しているので先頭に挿入
            self.list.push_front(value);
        }
    }

    pub fn insert_before(&mut self, value: T) {
        if let Some(indexer) = self.indexer {
            let prev = unsafe { &mut indexer.get_mut().next };
            let new_node = LinkedList::new_node_ptr(Node {
                prev: *prev,
                next: Some(indexer.0),
                value,
            });
            if let Some(mut prev) = prev.replace(new_node) {
                unsafe {
                    prev.as_mut().next = Some(new_node);
                }
            } else {
                self.list.head = Some(new_node);
            }
        } else {
            self.list.push_back(value);
        }
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

    #[test]
    fn append_test() {
        let mut list = (1i32..=10).collect::<LinkedList<_>>();
        let mut list2 = (11i32..=20).collect::<LinkedList<_>>();
        list.append(&mut list2);
        assert!(list.into_iter().eq(1..=20));
    }

    #[test]
    fn cursor_test() {
        let mut list = [2, 4, 5, 6, 8].into_iter().collect::<LinkedList<_>>();
        let mut cursor = list.cursor_front_mut();
        assert!(!cursor.is_dummy());
        cursor.move_next();
        assert!(!cursor.is_dummy());
        assert_eq!(*cursor.get().unwrap(), 4);
        cursor.move_next();
        assert_eq!(*cursor.get().unwrap(), 5);
        assert_eq!(cursor.cut_current().unwrap(), 5);
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
        assert!(cursor.is_dummy());
        cursor.move_next();
        assert!(cursor.is_dummy());

        cursor.insert_after(30);
        cursor.insert_after(25);
        cursor.move_next();
        cursor.insert_after(28);
        cursor.move_next();
        cursor.insert_after(29);
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
        let tail_old = cursor.list().indexer_back().unwrap();
        cursor.list().append(&mut [9, 10, 11].into_iter().collect());
        unsafe { cursor.set_index(tail_old) };
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
}
