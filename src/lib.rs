use core::borrow::Borrow;
use core::cmp::Ordering;
use core::marker::PhantomData;
use core::ops::Index;
use core::ptr::NonNull;

#[derive(Clone, Copy, Eq, PartialEq)]
enum Color {
    Red,
    Black,
}

struct Node<K, V> {
    parent: Option<NonNull<Node<K, V>>>,
    left: Option<NonNull<Node<K, V>>>,
    right: Option<NonNull<Node<K, V>>>,
    key: K,
    val: V,
    color: Color,
}

pub struct RBTreeMap<K, V> {
    root: Option<NonNull<Node<K, V>>>,
    len: usize,
    _marker: PhantomData<(K, V)>,
}

enum SearchResult<K, V> {
    Found(NonNull<Node<K, V>>),
    // option because insertion could be in an empty tree
    PotentialParentForInsertion(Option<NonNull<Node<K, V>>>),
}

use SearchResult::*;

impl<K, V> RBTreeMap<K, V> {
    /// Makes a new, empty `RBTreeMap`.
    ///
    /// Does not allocate anything on its own.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map = RBTreeMap::new();
    ///
    /// // entries can now be inserted into the empty map
    /// map.insert(1, "a");
    /// ```
    pub fn new() -> RBTreeMap<K, V> {
        Self {
            root: None,
            len: 0,
            _marker: PhantomData,
        }
    }

    /// Clears the map, removing all elements.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut a = RBTreeMap::new();
    /// a.insert(1, "a");
    /// a.clear();
    /// assert!(a.is_empty());
    /// ```
    pub fn clear(&mut self) {
        unimplemented!()
    }

    fn search_tree<Q>(&self, key: &Q) -> SearchResult<K, V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        let mut x = self.root;
        let mut y = None;

        while let Some(boxed_x) = x {
            y = x;
            unsafe {
                match (*boxed_x.as_ptr()).key.borrow().cmp(key) {
                    Ordering::Equal => return Found(boxed_x),
                    Ordering::Greater => x = (*boxed_x.as_ptr()).left,
                    Ordering::Less => x = (*boxed_x.as_ptr()).right,
                }
            }
        }

        PotentialParentForInsertion(y)
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map = RBTreeMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        match self.search_tree(key) {
            Found(node) => Some(unsafe { &(*node.as_ptr()).val }),
            PotentialParentForInsertion(_) => None,
        }
    }

    /// Returns the key-value pair corresponding to the supplied key.
    ///
    /// The supplied key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map = RBTreeMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get_key_value(&1), Some((&1, &"a")));
    /// assert_eq!(map.get_key_value(&2), None);
    /// ```
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        match self.search_tree(key) {
            Found(node) => Some(unsafe { (&(*node.as_ptr()).key, &(*node.as_ptr()).val) }),
            PotentialParentForInsertion(_) => None,
        }
    }

    fn minimum(tree_root: NonNull<Node<K, V>>) -> NonNull<Node<K, V>> {
        let mut x = Some(tree_root);
        let mut y = tree_root;
        while let Some(boxed_x) = x {
            y = boxed_x;
            x = unsafe { (*boxed_x.as_ptr()).left };
        }
        y
    }

    /// Returns the first key-value pair in the map.
    /// The key in this pair is the minimum key in the map.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map = RBTreeMap::new();
    /// assert_eq!(map.first_key_value(), None);
    /// map.insert(1, "b");
    /// map.insert(2, "a");
    /// assert_eq!(map.first_key_value(), Some((&1, &"b")));
    /// ```
    pub fn first_key_value(&self) -> Option<(&K, &V)>
    where
        K: Ord,
    {
        self.root.map(|root| {
            let ptr = Self::minimum(root);
            unsafe { (&(*ptr.as_ptr()).key, &(*ptr.as_ptr()).val) }
        })
    }

    /// Returns the last key-value pair in the map.
    /// The key in this pair is the maximum key in the map.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map = RBTreeMap::new();
    /// map.insert(1, "b");
    /// map.insert(2, "a");
    /// assert_eq!(map.last_key_value(), Some((&2, &"a")));
    /// ```
    pub fn last_key_value(&self) -> Option<(&K, &V)>
    where
        K: Ord,
    {
        let mut x = self.root;
        let mut y = None;
        while let Some(boxed_x) = x {
            y = x;
            x = unsafe { (*boxed_x.as_ptr()).right };
        }
        y.map(|ptr| unsafe { (&(*ptr.as_ptr()).key, &(*ptr.as_ptr()).val) })
    }

    /// Returns `true` if the map contains a value for the specified key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map = RBTreeMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self.get(key).is_some()
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map = RBTreeMap::new();
    /// map.insert(1, "a");
    /// if let Some(x) = map.get_mut(&1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map[&1], "b");
    /// ```
    // See `get` for implementation notes, this is basically a copy-paste with mut's added
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        match self.search_tree(key) {
            Found(node) => Some(unsafe { &mut (*node.as_ptr()).val }),
            PotentialParentForInsertion(_) => None,
        }
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned. The key is not updated, though; this matters for
    /// types that can be `==` without being identical. See the [std::collections
    /// module documentation](https://doc.rust-lang.org/std/collections/index.html#insert-and-complex-keys) for more.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map = RBTreeMap::new();
    /// assert_eq!(map.insert(37, "a"), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, "b");
    /// assert_eq!(map.insert(37, "c"), Some("b"));
    /// assert_eq!(map[&37], "c");
    /// ```
    pub fn insert(&mut self, key: K, val: V) -> Option<V>
    where
        K: Ord,
    {
        match self.search_tree(&key) {
            Found(node) => Some(core::mem::replace(
                unsafe { &mut (*node.as_ptr()).val },
                val,
            )),
            PotentialParentForInsertion(parent_option) => {
                let new_node = unsafe {
                    NonNull::new_unchecked(Box::into_raw(Box::new(Node {
                        parent: parent_option,
                        left: None,
                        right: None,
                        key,
                        val,
                        color: Color::Red,
                    })))
                };

                match parent_option {
                    Some(parent) => unsafe {
                        if (*new_node.as_ptr()).key < (*parent.as_ptr()).key {
                            (*parent.as_ptr()).left = Some(new_node);
                        } else {
                            (*parent.as_ptr()).right = Some(new_node);
                        }
                    },
                    None => self.root = Some(new_node), // tree was empty
                }

                unsafe {
                    self.insert_fixup(new_node);
                }

                self.len += 1;

                None
            }
        }
    }

    unsafe fn left_rotate(&mut self, node: NonNull<Node<K, V>>) {
        // rotation is not possible if right child is empty
        if let Some(right_child) = (*node.as_ptr()).right {
            (*node.as_ptr()).right = (*right_child.as_ptr()).left;
            if let Some(right_left_child) = (*right_child.as_ptr()).left {
                (*right_left_child.as_ptr()).parent = Some(node);
            }

            // right child's parent becomes node's parent
            (*right_child.as_ptr()).parent = (*node.as_ptr()).parent;

            match (*node.as_ptr()).parent {
                Some(parent) => {
                    if Some(node) == (*parent.as_ptr()).left {
                        (*parent.as_ptr()).left = Some(right_child);
                    } else {
                        (*parent.as_ptr()).right = Some(right_child);
                    }
                }
                // if node was root
                None => self.root = Some(right_child),
            }

            (*right_child.as_ptr()).left = Some(node);
            (*node.as_ptr()).parent = Some(right_child);
        }
    }

    unsafe fn right_rotate(&mut self, node: NonNull<Node<K, V>>) {
        // rotation is not possible if left child is empty
        if let Some(left_child) = (*node.as_ptr()).left {
            (*node.as_ptr()).left = (*left_child.as_ptr()).right;
            if let Some(left_right_child) = (*left_child.as_ptr()).right {
                (*left_right_child.as_ptr()).parent = Some(node);
            }

            // left child's parent becomes node's parent
            (*left_child.as_ptr()).parent = (*node.as_ptr()).parent;

            match (*node.as_ptr()).parent {
                Some(parent) => {
                    if Some(node) == (*parent.as_ptr()).left {
                        (*parent.as_ptr()).left = Some(left_child);
                    } else {
                        (*parent.as_ptr()).right = Some(left_child);
                    }
                }
                // if node was root
                None => self.root = Some(left_child),
            }

            (*left_child.as_ptr()).right = Some(node);
            (*node.as_ptr()).parent = Some(left_child);
        }
    }

    unsafe fn insert_fixup(&mut self, mut node: NonNull<Node<K, V>>) {
        while let Some(mut parent) = (*node.as_ptr()).parent {
            if (*parent.as_ptr()).color == Color::Black {
                break;
            }

            // since parent is red and root is always black,
            // grandparent should exist
            let grandparent = (*parent.as_ptr())
                .parent
                .expect("where are you grandparent?");

            if Some(parent) == (*grandparent.as_ptr()).left {
                let uncle_option = (*grandparent.as_ptr()).right;
                match uncle_option {
                    // both parent and uncle are red
                    Some(uncle) if (*uncle.as_ptr()).color == Color::Red => {
                        // transfer grandparent's blackness one level down
                        (*parent.as_ptr()).color = Color::Black;
                        (*uncle.as_ptr()).color = Color::Black;
                        (*grandparent.as_ptr()).color = Color::Red;
                        node = grandparent;
                    }
                    _ => {
                        if Some(node) == (*parent.as_ptr()).right {
                            core::mem::swap(&mut node, &mut parent);
                            self.left_rotate(node);
                        }

                        (*parent.as_ptr()).color = Color::Black;
                        (*grandparent.as_ptr()).color = Color::Red;
                        self.right_rotate(grandparent);
                    }
                }
            } else {
                // same as if case but with "right" and "left" exchanged
                let uncle_option = (*grandparent.as_ptr()).left;
                match uncle_option {
                    // both parent and uncle are red
                    Some(uncle) if (*uncle.as_ptr()).color == Color::Red => {
                        // transfer grandparent's blackness one level down
                        (*parent.as_ptr()).color = Color::Black;
                        (*uncle.as_ptr()).color = Color::Black;
                        (*grandparent.as_ptr()).color = Color::Red;
                        node = grandparent;
                    }
                    _ => {
                        if Some(node) == (*parent.as_ptr()).left {
                            core::mem::swap(&mut node, &mut parent);
                            self.right_rotate(node);
                        }

                        (*parent.as_ptr()).color = Color::Black;
                        (*grandparent.as_ptr()).color = Color::Red;
                        self.left_rotate(grandparent);
                    }
                }
            }
        }

        // SAFETY: since we came here from insert, the tree is not empty
        (*self.root.expect("tree empty after insertion!").as_ptr()).color = Color::Black;
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map = RBTreeMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove(&1), Some("a"));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        unsafe {
            if let Found(z) = self.search_tree(&key) {
                let mut y = z;
                let mut y_original_color = (*y.as_ptr()).color;

                let x;
                match ((*z.as_ptr()).left, (*z.as_ptr()).right) {
                    (None, right_child_option) => {
                        x = right_child_option;
                        self.transplant(z, right_child_option);
                    }
                    (left_child_option @ Some(_), None) => {
                        x = left_child_option;
                        self.transplant(z, left_child_option);
                    }
                    (
                        left_child_option @ Some(left_child),
                        right_child_option @ Some(right_child),
                    ) => {
                        y = Self::minimum(right_child);
                        y_original_color = (*y.as_ptr()).color;

                        x = (*y.as_ptr()).right;

                        // y is farther down the tree
                        if y != right_child {
                            self.transplant(y, (*y.as_ptr()).right);
                            (*y.as_ptr()).right = right_child_option;
                            (*right_child.as_ptr()).parent = Some(y);
                        } else {
                            // x.p = y; // why?
                        }

                        self.transplant(z, Some(y));

                        (*y.as_ptr()).left = left_child_option;
                        (*left_child.as_ptr()).parent = Some(y);

                        (*y.as_ptr()).color = (*z.as_ptr()).color;
                    }
                }

                if y_original_color == Color::Black {
                    self.remove_fixup(x);
                }

                self.len -= 1;

                let boxed_node = Box::from_raw(z.as_ptr());
                Some(boxed_node.val)
            } else {
                None
            }
        }
    }

    unsafe fn remove_fixup(&mut self, _x: Option<NonNull<Node<K, V>>>) {
        unimplemented!()
    }

    unsafe fn transplant(
        &mut self,
        to_replace: NonNull<Node<K, V>>,
        replacement_option: Option<NonNull<Node<K, V>>>,
    ) {
        match (*to_replace.as_ptr()).parent {
            Some(parent) => {
                if Some(to_replace) == (*parent.as_ptr()).left {
                    (*parent.as_ptr()).left = replacement_option;
                } else {
                    (*parent.as_ptr()).right = replacement_option;
                }
            }
            None => self.root = replacement_option,
        }

        if let Some(replacement_node) = replacement_option {
            (*replacement_node.as_ptr()).parent = (*to_replace.as_ptr()).parent;
        }
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut a = RBTreeMap::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1, "a");
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the map contains no elements.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut a = RBTreeMap::new();
    /// assert!(a.is_empty());
    /// a.insert(1, "a");
    /// assert!(!a.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<K, V> Default for RBTreeMap<K, V> {
    fn default() -> RBTreeMap<K, V> {
        Self::new()
    }
}

impl<K, Q, V> Index<&Q> for RBTreeMap<K, V>
where
    K: Borrow<Q> + Ord,
    Q: Ord + ?Sized,
{
    type Output = V;

    /// Returns a reference to the value corresponding to the supplied key.
    ///
    /// # Panics
    ///
    /// Panics if the key is not present in the `RBTreeMap`.
    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("no entry found for key")
    }
}
