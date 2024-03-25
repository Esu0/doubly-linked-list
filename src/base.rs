use std::{
    alloc::{Allocator, Global},
    fmt::{self, Debug},
    marker::PhantomData,
    mem::{self, ManuallyDrop},
    ops::Deref,
    ptr::NonNull,
};

pub struct LinkedList<T: ?Sized, A: Allocator + Clone = Global> {
    head: Link<T>,
    tail: Link<T>,
    alloc: A,
    _marker: PhantomData<Box<Node<T>, A>>,
}

unsafe impl<T: Send, A: Send + Allocator + Clone> Send for LinkedList<T, A> {}
unsafe impl<T: Sync, A: Sync + Allocator + Clone> Sync for LinkedList<T, A> {}

type Link<T> = Option<NonNull<Node<T>>>;

#[derive(Debug)]
pub(crate) struct Node<T: ?Sized> {
    prev: Link<T>,
    next: Link<T>,
    value: T,
}

impl<T> Node<T> {
    pub(crate) fn into_value(self) -> T {
        self.value
    }
}

impl<T: ?Sized> Node<T> {
    pub(crate) fn value(&self) -> &T {
        &self.value
    }

    pub(crate) fn value_mut(&mut self) -> &mut T {
        &mut self.value
    }
}

impl<T, A: Allocator + Clone> LinkedList<T, A> {
    fn new_node_ptr(node: Node<T>, alloc: A) -> NonNull<Node<T>> {
        Box::<_, A>::leak(Box::<_, A>::new_in(node, alloc)).into()
    }

    pub fn push_front(&mut self, value: T) {
        self.push_front_pointer(value);
    }

    pub fn push_back(&mut self, value: T) {
        self.push_back_pointer(value);
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
            unsafe { *Box::from_raw_in(head.as_ptr(), self.alloc.clone()) }
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
            unsafe { *Box::from_raw_in(tail.as_ptr(), self.alloc.clone()) }
        })
    }
}

impl<T: ?Sized> LinkedList<T, Global> {
    pub const fn new() -> Self {
        Self {
            head: None,
            tail: None,
            alloc: Global,
            _marker: PhantomData,
        }
    }
}

impl<T: ?Sized, A: Allocator + Clone> LinkedList<T, A> {
    pub const fn new_in(alloc: A) -> Self {
        Self {
            head: None,
            tail: None,
            alloc,
            _marker: PhantomData,
        }
    }

    pub(crate) const unsafe fn from_raw_parts_in(
        head: Option<NonNull<Node<T>>>,
        tail: Option<NonNull<Node<T>>>,
        alloc: A,
    ) -> Self {
        Self {
            head,
            tail,
            alloc,
            _marker: PhantomData,
        }
    }

    pub const fn alloc(&self) -> &A {
        &self.alloc
    }

    pub const fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    pub(crate) fn iter_ptr(&self) -> IterPtr<T> {
        IterPtr {
            head: self.head,
            tail: self.tail,
        }
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
        self.pointer_front()
            .map(|pointer| Cursor(pointer, PhantomData))
    }

    pub fn cursor_back(&self) -> Option<Cursor<'_, T>> {
        self.pointer_back()
            .map(|pointer| Cursor(pointer, PhantomData))
    }

    pub fn cursor_front_mut(&mut self) -> CursorMut<'_, T, A> {
        CursorMut {
            pointer: self.pointer_front(),
            list: self,
        }
    }

    pub fn cursor_back_mut(&mut self) -> CursorMut<'_, T, A> {
        CursorMut {
            pointer: self.pointer_back(),
            list: self,
        }
    }

    pub fn pointer_front(&self) -> Option<Pointer<T>> {
        self.head.map(|head| Pointer(head))
    }

    pub fn pointer_back(&self) -> Option<Pointer<T>> {
        self.tail.map(|tail| Pointer(tail))
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
        *self = Self::new_in(self.alloc.clone());
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

impl<T, A: Allocator + Clone> IntoIterator for LinkedList<T, A> {
    type IntoIter = IntoIter<T, A>;
    type Item = T;

    fn into_iter(self) -> Self::IntoIter {
        let slf = ManuallyDrop::new(self);
        IntoIter {
            iter_ptr: slf.iter_ptr(),
            alloc: slf.alloc.clone(),
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
    iter_ptr: IterPtr<T>,
    alloc: A,
    _marker: PhantomData<LinkedList<T, A>>,
}

impl<T, A: Allocator + Clone> IntoIter<T, A> {
    pub(crate) const unsafe fn from_iter_ptr(iter_ptr: IterPtr<T>, alloc: A) -> Self {
        Self {
            iter_ptr,
            alloc,
            _marker: PhantomData,
        }
    }
}

impl<T, A: Allocator + Clone> Iterator for IntoIter<T, A> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_ptr
            .next()
            .map(|ptr| unsafe { Box::from_raw_in(ptr.as_ptr(), self.alloc.clone()).value })
    }
}

impl<T, A: Allocator + Clone> DoubleEndedIterator for IntoIter<T, A> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter_ptr
            .next_back()
            .map(|ptr| unsafe { Box::from_raw_in(ptr.as_ptr(), self.alloc.clone()).value })
    }
}

impl<T, A: Allocator + Clone> Drop for IntoIter<T, A> {
    fn drop(&mut self) {
        self.for_each(|val| drop(val))
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

unsafe impl<T: ?Sized> Send for IterPtr<T> {}
unsafe impl<T: ?Sized> Sync for IterPtr<T> {}

impl<T: ?Sized> Clone for IterPtr<T> {
    fn clone(&self) -> Self {
        Self {
            head: self.head,
            tail: self.tail,
        }
    }
}

impl<T: ?Sized> Iterator for IterPtr<T> {
    type Item = NonNull<Node<T>>;

    /// don't panic
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

    fn last(self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.tail
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

impl<T: ?Sized, A: Allocator + Clone> Drop for LinkedList<T, A> {
    fn drop(&mut self) {
        unsafe {
            self.iter_ptr()
                .for_each(|ptr| drop(Box::from_raw_in(ptr.as_ptr(), self.alloc.clone())));
        }
    }
}

impl<T: Debug + ?Sized, A: Allocator + Clone> Debug for LinkedList<T, A> {
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

impl<T, A1, A2> PartialEq<LinkedList<T, A2>> for LinkedList<T, A1>
where
    T: PartialEq,
    A1: Allocator + Clone,
    A2: Allocator + Clone,
{
    fn eq(&self, other: &LinkedList<T, A2>) -> bool {
        self.iter().eq(other.iter())
    }

    fn ne(&self, other: &LinkedList<T, A2>) -> bool {
        self.iter().ne(other.iter())
    }
}

impl<T: Eq, A: Allocator + Clone> Eq for LinkedList<T, A> {}

impl<T, A1, A2> PartialOrd<LinkedList<T, A2>> for LinkedList<T, A1>
where
    T: PartialOrd,
    A1: Allocator + Clone,
    A2: Allocator + Clone,
{
    fn partial_cmp(&self, other: &LinkedList<T, A2>) -> Option<std::cmp::Ordering> {
        self.iter().partial_cmp(other.iter())
    }

    fn ge(&self, other: &LinkedList<T, A2>) -> bool {
        self.iter().ge(other.iter())
    }

    fn gt(&self, other: &LinkedList<T, A2>) -> bool {
        self.iter().gt(other.iter())
    }

    fn le(&self, other: &LinkedList<T, A2>) -> bool {
        self.iter().le(other.iter())
    }

    fn lt(&self, other: &LinkedList<T, A2>) -> bool {
        self.iter().lt(other.iter())
    }
}

impl<T: Ord, A: Allocator + Clone> Ord for LinkedList<T, A> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.iter().cmp(other.iter())
    }
}

pub struct Pointer<T: ?Sized>(NonNull<Node<T>>);

unsafe impl<T: ?Sized> Send for Pointer<T> {}
unsafe impl<T: ?Sized> Sync for Pointer<T> {}

impl<T: ?Sized> Clone for Pointer<T> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}

impl<T: ?Sized> Copy for Pointer<T> {}

impl<T: ?Sized> PartialEq for Pointer<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }

    fn ne(&self, other: &Self) -> bool {
        self.0.ne(&other.0)
    }
}

impl<T: ?Sized> Eq for Pointer<T> {}

impl<T: ?Sized> Pointer<T> {
    unsafe fn into_boxed_node<A: Allocator + Clone>(self, alloc: A) -> Box<Node<T>, A> {
        Box::from_raw_in(self.0.as_ptr(), alloc)
    }

    pub(crate) unsafe fn get<'a>(self) -> &'a Node<T> {
        &*self.0.as_ptr()
    }

    pub(crate) unsafe fn get_mut<'a>(self) -> &'a mut Node<T> {
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

    pub(crate) fn as_ptr_node(self) -> NonNull<Node<T>> {
        self.0
    }
}

impl<T: ?Sized, A: Allocator + Clone> LinkedList<T, A> {
    /// # Safety
    /// * `pointer`の指すノードがリスト`self`が所有する有効なノードである
    pub unsafe fn remove(&mut self, pointer: Pointer<T>) {
        drop(self.cut_node(pointer));
    }

    pub(crate) unsafe fn cut_node(&mut self, pointer: Pointer<T>) -> Box<Node<T>, A> {
        let (prev, next) = {
            let node = pointer.0.as_ref();
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

        pointer.into_boxed_node(self.alloc.clone())
    }

    /// # Safety
    /// * `pointer`の指すノードがリスト`self`が所有する有効なノードである
    pub unsafe fn get(&self, pointer: Pointer<T>) -> &T {
        &(*pointer.0.as_ptr()).value
    }

    /// # Safety
    /// * `pointer`の指すノードがリスト`self`が所有する有効なノードである
    pub unsafe fn get_mut(&mut self, pointer: Pointer<T>) -> &mut T {
        &mut (*pointer.0.as_ptr()).value
    }

    /// # Safety
    /// * `pointer`の指すノードがリスト`self`が所有する有効なノードである
    pub unsafe fn get_cursor(&self, pointer: Pointer<T>) -> Cursor<'_, T> {
        Cursor(pointer, PhantomData)
    }

    /// # Safety
    /// * `pointer`の指すノードがリスト`self`が所有する有効なノードである
    pub unsafe fn get_cursor_mut(&mut self, pointer: Pointer<T>) -> CursorMut<'_, T, A> {
        CursorMut {
            pointer: Some(pointer),
            list: self,
        }
    }

    pub unsafe fn next_pointer(&self, pointer: Option<Pointer<T>>) -> Option<Pointer<T>> {
        if let Some(pointer) = pointer {
            pointer.next()
        } else {
            self.pointer_front()
        }
    }

    pub unsafe fn prev_pointer(&self, pointer: Option<Pointer<T>>) -> Option<Pointer<T>> {
        if let Some(pointer) = pointer {
            pointer.prev()
        } else {
            self.pointer_back()
        }
    }

    pub unsafe fn splice_after_pointer(&mut self, pointer: Option<Pointer<T>>, list: Self) {
        let Some((mut list_head, mut list_tail)) = list.get_head_tail() else {
            // リストは空なので何もしない
            return;
        };
        // `LinkedList::drop()`を呼ばないようにする
        mem::forget(list);

        // `list`の末尾とリンクすべきノード
        let next = if let Some(pointer) = pointer {
            // ダミーノードを指していない => 先頭ノードの変更はなし
            list_head.as_mut().prev = Some(pointer.0);
            pointer.get_mut().next.replace(list_head)

            // `pointer.get_mut().next`が`None`のときは末尾に挿入することになる
            // よって、`list`の末尾とリンクすべきノードは存在しない
        } else {
            debug_assert!(list_head.as_ref().prev.is_none());
            // ダミーノードを指している => 先頭ノードを変更
            // `(*list_head).prev`は`None`であることが保証されているため
            // 変更しなくてよい
            self.head.replace(list_head)

            // `self.list.head`が`None`のときはリストが空であるから、
            // `list`の末尾とリンクすべきノードは存在しない
        };

        if let Some(mut next) = next {
            next.as_mut().prev = Some(list_tail);
            list_tail.as_mut().next = Some(next);
        } else {
            debug_assert!(list_tail.as_ref().next.is_none());
            // `next`が`None`のときは末尾ノードを変更する必要がある
            self.tail = Some(list_tail);
        }
    }

    pub unsafe fn splice_before_pointer(&mut self, pointer: Option<Pointer<T>>, list: Self) {
        let Some((mut list_head, mut list_tail)) = list.get_head_tail() else {
            return;
        };
        mem::forget(list);
        unsafe {
            let prev = if let Some(pointer) = pointer {
                list_tail.as_mut().next = Some(pointer.0);
                pointer.get_mut().prev.replace(list_tail)
            } else {
                debug_assert!(list_tail.as_ref().next.is_none());
                self.tail.replace(list_tail)
            };

            if let Some(mut prev) = prev {
                prev.as_mut().next = Some(list_head);
                list_head.as_mut().prev = Some(prev);
            } else {
                debug_assert!(list_head.as_ref().prev.is_none());
                self.head = Some(list_head);
            }
        }
    }

    pub unsafe fn split_after_pointer(&mut self, pointer: Option<Pointer<T>>) -> Self {
        let alloc = self.alloc.clone();
        if let Some(pointer) = pointer {
            let head = pointer.get_mut().next.take();
            if let Some(mut head) = head {
                let tail = self.tail.replace(pointer.0);
                head.as_mut().prev = None;
                LinkedList::from_raw_parts_in(Some(head), tail, alloc)
            } else {
                LinkedList::new_in(alloc)
            }
        } else {
            LinkedList::from_raw_parts_in(self.head.take(), self.tail.take(), alloc)
        }
    }

    pub unsafe fn split_before_pointer(&mut self, pointer: Option<Pointer<T>>) -> Self {
        let alloc = self.alloc.clone();
        if let Some(pointer) = pointer {
            let tail = pointer.get_mut().prev.take();
            if let Some(mut tail) = tail {
                let head = self.head.replace(pointer.0);
                tail.as_mut().next = None;
                LinkedList::from_raw_parts_in(head, Some(tail), alloc)
            } else {
                LinkedList::new_in(alloc)
            }
        } else {
            LinkedList::from_raw_parts_in(self.head.take(), self.tail.take(), alloc)
        }
    }
}

impl<T, A: Allocator + Clone> LinkedList<T, A> {
    fn push_front_pointer(&mut self, value: T) -> Pointer<T> {
        let new_node = Self::new_node_ptr(
            Node {
                prev: None,
                next: self.head,
                value,
            },
            self.alloc.clone(),
        );
        if let Some(mut head) = self.head {
            unsafe {
                head.as_mut().prev = Some(new_node);
            }
        } else {
            self.tail = Some(new_node);
        }
        self.head = Some(new_node);
        Pointer(new_node)
    }

    fn push_back_pointer(&mut self, value: T) -> Pointer<T> {
        let new_node = Self::new_node_ptr(
            Node {
                prev: self.tail,
                next: None,
                value,
            },
            self.alloc.clone(),
        );

        if let Some(mut tail) = self.tail {
            unsafe {
                tail.as_mut().next = Some(new_node);
            }
        } else {
            self.head = Some(new_node);
        }
        self.tail = Some(new_node);
        Pointer(new_node)
    }

    pub unsafe fn insert_after_pointer(
        &mut self,
        pointer: Option<Pointer<T>>,
        value: T,
    ) -> Pointer<T> {
        if let Some(pointer) = pointer {
            // ダミーノードでない = 挿入位置は先頭でない
            let next = unsafe { &mut pointer.get_mut().next };
            let new_node = LinkedList::new_node_ptr(
                Node {
                    prev: Some(pointer.0),
                    next: *next,
                    value,
                },
                self.alloc.clone(),
            );
            if let Some(mut next) = next.replace(new_node) {
                // 次のノードが存在する
                unsafe {
                    next.as_mut().prev = Some(new_node);
                }
            } else {
                // 次のノードが存在しない = 現在位置は末尾
                self.tail = Some(new_node);
            }
            Pointer(new_node)
        } else {
            // ダミーノードを指しているので先頭に挿入
            self.push_front_pointer(value)
        }
    }

    pub unsafe fn insert_before_pointer(
        &mut self,
        pointer: Option<Pointer<T>>,
        value: T,
    ) -> Pointer<T> {
        if let Some(pointer) = pointer {
            let prev = unsafe { &mut pointer.get_mut().next };
            let new_node = LinkedList::new_node_ptr(
                Node {
                    prev: *prev,
                    next: Some(pointer.0),
                    value,
                },
                self.alloc.clone(),
            );
            if let Some(mut prev) = prev.replace(new_node) {
                unsafe {
                    prev.as_mut().next = Some(new_node);
                }
            } else {
                self.head = Some(new_node);
            }
            Pointer(new_node)
        } else {
            self.push_back_pointer(value)
        }
    }
}

// `LinkedList`の共有参照と同等のはたらきをもつ
pub struct Cursor<'a, T: ?Sized>(Pointer<T>, PhantomData<&'a LinkedList<T>>);

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

pub struct CursorMut<'a, T: ?Sized, A: Allocator + Clone> {
    pointer: Option<Pointer<T>>,
    list: &'a mut LinkedList<T, A>,
}

impl<'a, T: ?Sized, A: Allocator + Clone> CursorMut<'a, T, A> {
    /// カーソルを一つ次のノードに移動する。一つ次のノードが存在しない場合はダミーノードを指すように変更される。
    /// ダミーノードを指している場合はリストの先頭に移動する。
    pub fn move_next(&mut self) {
        self.pointer = unsafe { self.list.next_pointer(self.pointer) };
    }

    /// カーソルを一つ前のノードに移動する。一つ前のノードが存在しない場合はダミーノードを指すように変更される。
    /// ダミーノードを指している場合はリストの末尾に移動する。
    pub fn move_prev(&mut self) {
        self.pointer = unsafe { self.list.prev_pointer(self.pointer) };
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
        self.pointer.is_none()
    }

    fn node(&self) -> Option<&Node<T>> {
        unsafe { self.pointer.map(|pointer| pointer.get()) }
    }

    fn node_mut(&mut self) -> Option<&mut Node<T>> {
        unsafe { self.pointer.map(|pointer| pointer.get_mut()) }
    }

    fn cut_node_current(&mut self) -> Option<Box<Node<T>, A>> {
        self.pointer.map(|pointer| unsafe {
            self.pointer = pointer.next();
            self.list.cut_node(pointer)
        })
    }

    /// # Safety
    /// * `pointer`が指すノードとカーソルが指すノードが同じリストに属する。カーソルがダミーノードを指している場合もこれを満たす必要がある。
    pub unsafe fn set_from_pointer(&mut self, pointer: Pointer<T>) {
        self.pointer = Some(pointer);
    }

    pub fn list(&mut self) -> &mut LinkedList<T, A> {
        self.list
    }

    pub fn splice_after(&mut self, list: LinkedList<T, A>) {
        unsafe {
            self.list.splice_after_pointer(self.pointer, list);
        }
    }

    pub fn splice_before(&mut self, list: LinkedList<T, A>) {
        unsafe {
            self.list.splice_before_pointer(self.pointer, list);
        }
    }

    pub fn split_after(&mut self) -> LinkedList<T, A> {
        unsafe { self.list.split_after_pointer(self.pointer) }
    }

    pub fn split_before(&mut self) -> LinkedList<T, A> {
        unsafe { self.list.split_before_pointer(self.pointer) }
    }
}

impl<'a, T, A: Allocator + Clone> CursorMut<'a, T, A> {
    /// 現在指しているノードをリストから削除して値を返す。このとき、カーソルを次のノードに移動する。
    /// 現在指しているノードがダミーノードなら何もしない。
    pub fn cut_current(&mut self) -> Option<T> {
        self.cut_node_current().map(|node| node.value)
    }

    pub fn insert_after(&mut self, value: T) {
        unsafe {
            self.list.insert_after_pointer(self.pointer, value);
        }
    }

    pub fn insert_before(&mut self, value: T) {
        unsafe {
            self.list.insert_before_pointer(self.pointer, value);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::alloc::Layout;

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

    use debug_allocator::{Action, DebugAlloc};
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
        let tail_old = cursor.list().pointer_back().unwrap();
        cursor.list().append(&mut [9, 10, 11].into_iter().collect());
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
    fn alloc_test() {
        let alloc = DebugAlloc::new(Global);
        let mut list = LinkedList::new_in(alloc.clone());
        list.push_back(10i32);
        let action = alloc.history().front().unwrap().clone();
        assert_eq!(
            action,
            Action {
                addr: list.head.map(|ptr| ptr.cast()),
                layout: Layout::new::<Node<i32>>(),
                kind: debug_allocator::Kind::Allocate,
            }
        );
    }
}
