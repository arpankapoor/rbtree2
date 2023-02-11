use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt::Debug;
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ops::Index;
use core::ptr::NonNull;

#[derive(Clone, Copy, Eq, PartialEq)]
enum Color {
    Red,
    Black,
}

struct Node<K, V> {
    // TODO: store color with parent like in linux kernel
    parent: Option<NonNull<Node<K, V>>>,
    left: Option<NonNull<Node<K, V>>>,
    right: Option<NonNull<Node<K, V>>>,
    key: K,
    val: V,
    color: Color,
}

impl<K, V> Node<K, V> {
    fn is_black(&self) -> bool {
        self.color == Color::Black
    }

    fn is_red(&self) -> bool {
        self.color == Color::Red
    }
}

/// An ordered map based on a [Red-Black Tree].
///
/// [Red-Black Tree]: https://en.wikipedia.org/wiki/Red-black_tree
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

/// A view into a vacant entry in a `RBTreeMap`.
/// It is part of the [`Entry`] enum.
pub struct VacantEntry<'a, K, V> {
    key: K,
    potential_parent: Option<NonNull<Node<K, V>>>,
    tree: &'a mut RBTreeMap<K, V>,
}

impl<'a, K, V> VacantEntry<'a, K, V>
where
    K: Ord,
{
    /// Gets a reference to the key that would be used when inserting a value
    /// through the VacantEntry.
    ///
    /// # Examples
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map: RBTreeMap<&str, usize> = RBTreeMap::new();
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Take ownership of the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use rbtreemap::{RBTreeMap, Entry};
    ///
    /// let mut map: RBTreeMap<&str, usize> = RBTreeMap::new();
    ///
    /// if let Entry::Vacant(v) = map.entry("poneyland") {
    ///     v.into_key();
    /// }
    /// ```
    pub fn into_key(self) -> K {
        self.key
    }

    /// Sets the value of the entry with the `VacantEntry`'s key,
    /// and returns a mutable reference to it.
    ///
    /// # Examples
    ///
    /// ```
    /// use rbtreemap::{RBTreeMap, Entry};
    ///
    /// let mut map: RBTreeMap<&str, u32> = RBTreeMap::new();
    ///
    /// if let Entry::Vacant(o) = map.entry("poneyland") {
    ///     o.insert(37);
    /// }
    /// assert_eq!(map["poneyland"], 37);
    /// ```
    pub fn insert(self, value: V) -> &'a mut V {
        let node = self
            .tree
            .insert_node(self.key, value, self.potential_parent);
        unsafe { &mut (*node.as_ptr()).val }
    }
}

impl<K: Debug + Ord, V> Debug for VacantEntry<'_, K, V> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("VacantEntry").field(self.key()).finish()
    }
}

/// A view into an occupied entry in a `RBTreeMap`.
/// It is part of the [`Entry`] enum.
pub struct OccupiedEntry<'a, K, V> {
    node: NonNull<Node<K, V>>,
    tree: &'a mut RBTreeMap<K, V>,
}

impl<'a, K, V> OccupiedEntry<'a, K, V>
where
    K: Ord,
{
    /// Gets a reference to the key in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map: RBTreeMap<&str, usize> = RBTreeMap::new();
    /// map.entry("poneyland").or_insert(12);
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```
    pub fn key(&self) -> &K {
        unsafe { &(*self.node.as_ptr()).key }
    }

    /// Take ownership of the key and value from the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use rbtreemap::{RBTreeMap, Entry};
    ///
    /// let mut map: RBTreeMap<&str, usize> = RBTreeMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     // We delete the entry from the map.
    ///     o.remove_entry();
    /// }
    ///
    /// // If now try to get the value, it will panic:
    /// // println!("{}", map["poneyland"]);
    /// ```
    pub fn remove_entry(self) -> (K, V) {
        unsafe { self.tree.remove_node(self.node) }
    }

    /// Gets a reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use rbtreemap::{RBTreeMap, Entry};
    ///
    /// let mut map: RBTreeMap<&str, usize> = RBTreeMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     assert_eq!(o.get(), &12);
    /// }
    /// ```
    pub fn get(&self) -> &V {
        unsafe { &(*self.node.as_ptr()).val }
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the `OccupiedEntry` that may outlive the
    /// destruction of the `Entry` value, see [`into_mut`].
    ///
    /// [`into_mut`]: OccupiedEntry::into_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use rbtreemap::{RBTreeMap, Entry};
    ///
    /// let mut map: RBTreeMap<&str, usize> = RBTreeMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// assert_eq!(map["poneyland"], 12);
    /// if let Entry::Occupied(mut o) = map.entry("poneyland") {
    ///     *o.get_mut() += 10;
    ///     assert_eq!(*o.get(), 22);
    ///
    ///     // We can use the same Entry multiple times.
    ///     *o.get_mut() += 2;
    /// }
    /// assert_eq!(map["poneyland"], 24);
    /// ```
    pub fn get_mut(&mut self) -> &mut V {
        unsafe { &mut (*self.node.as_ptr()).val }
    }

    /// Converts the entry into a mutable reference to its value.
    ///
    /// If you need multiple references to the `OccupiedEntry`, see [`get_mut`].
    ///
    /// [`get_mut`]: OccupiedEntry::get_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use rbtreemap::{RBTreeMap, Entry};
    ///
    /// let mut map: RBTreeMap<&str, usize> = RBTreeMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// assert_eq!(map["poneyland"], 12);
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     *o.into_mut() += 10;
    /// }
    /// assert_eq!(map["poneyland"], 22);
    /// ```
    pub fn into_mut(self) -> &'a mut V {
        unsafe { &mut (*self.node.as_ptr()).val }
    }

    /// Sets the value of the entry with the `OccupiedEntry`'s key,
    /// and returns the entry's old value.
    ///
    /// # Examples
    ///
    /// ```
    /// use rbtreemap::{RBTreeMap, Entry};
    ///
    /// let mut map: RBTreeMap<&str, usize> = RBTreeMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(mut o) = map.entry("poneyland") {
    ///     assert_eq!(o.insert(15), 12);
    /// }
    /// assert_eq!(map["poneyland"], 15);
    /// ```
    pub fn insert(&mut self, value: V) -> V {
        core::mem::replace(unsafe { &mut (*self.node.as_ptr()).val }, value)
    }

    /// Takes the value of the entry out of the map, and returns it.
    ///
    /// # Examples
    ///
    /// ```
    /// use rbtreemap::{RBTreeMap, Entry};
    ///
    /// let mut map: RBTreeMap<&str, usize> = RBTreeMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     assert_eq!(o.remove(), 12);
    /// }
    /// // If we try to get "poneyland"'s value, it'll panic:
    /// // println!("{}", map["poneyland"]);
    /// ```
    pub fn remove(self) -> V {
        self.remove_entry().1
    }
}

impl<K: Debug + Ord, V: Debug> Debug for OccupiedEntry<'_, K, V> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("OccupiedEntry")
            .field("key", self.key())
            .field("value", self.get())
            .finish()
    }
}

/// A view into a single entry in a map, which may either be vacant or occupied.
///
/// This `enum` is constructed from the [`entry`] method on [`RBTreeMap`].
///
/// [`entry`]: RBTreeMap::entry
pub enum Entry<'a, K, V>
where
    K: 'a,
    V: 'a,
{
    /// A vacant entry.
    Vacant(VacantEntry<'a, K, V>),

    /// An occupied entry.
    Occupied(OccupiedEntry<'a, K, V>),
}

impl<'a, K, V> Entry<'a, K, V>
where
    K: Ord,
{
    /// Ensures a value is in the entry by inserting the default if empty, and returns
    /// a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map: RBTreeMap<&str, usize> = RBTreeMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// assert_eq!(map["poneyland"], 12);
    /// ```
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map: RBTreeMap<&str, String> = RBTreeMap::new();
    /// let s = "hoho".to_string();
    ///
    /// map.entry("poneyland").or_insert_with(|| s);
    ///
    /// assert_eq!(map["poneyland"], "hoho".to_string());
    /// ```
    pub fn or_insert_with<F>(self, default: F) -> &'a mut V
    where
        F: FnOnce() -> V,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of the default function.
    /// This method allows for generating key-derived values for insertion by providing the default
    /// function a reference to the key that was moved during the `.entry(key)` method call.
    ///
    /// The reference to the moved key is provided so that cloning or copying the key is
    /// unnecessary, unlike with `.or_insert_with(|| ... )`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map: RBTreeMap<&str, usize> = RBTreeMap::new();
    ///
    /// map.entry("poneyland").or_insert_with_key(|key| key.chars().count());
    ///
    /// assert_eq!(map["poneyland"], 9);
    /// ```
    pub fn or_insert_with_key<F>(self, default: F) -> &'a mut V
    where
        F: FnOnce(&K) -> V,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                let value = default(entry.key());
                entry.insert(value)
            }
        }
    }

    /// Returns a reference to this entry's key.
    ///
    /// # Examples
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map: RBTreeMap<&str, usize> = RBTreeMap::new();
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```
    pub fn key(&self) -> &K {
        match *self {
            Entry::Occupied(ref entry) => entry.key(),
            Entry::Vacant(ref entry) => entry.key(),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map: RBTreeMap<&str, usize> = RBTreeMap::new();
    ///
    /// map.entry("poneyland")
    ///    .and_modify(|e| { *e += 1 })
    ///    .or_insert(42);
    /// assert_eq!(map["poneyland"], 42);
    ///
    /// map.entry("poneyland")
    ///    .and_modify(|e| { *e += 1 })
    ///    .or_insert(42);
    /// assert_eq!(map["poneyland"], 43);
    /// ```
    pub fn and_modify<F>(self, f: F) -> Entry<'a, K, V>
    where
        F: FnOnce(&mut V),
    {
        match self {
            Entry::Occupied(mut entry) => {
                f(entry.get_mut());
                Entry::Occupied(entry)
            }
            Entry::Vacant(entry) => Entry::Vacant(entry),
        }
    }
}

impl<'a, K, V> Entry<'a, K, V>
where
    K: Ord,
    V: Default,
{
    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map: RBTreeMap<&str, Option<usize>> = RBTreeMap::new();
    /// map.entry("poneyland").or_default();
    ///
    /// assert_eq!(map["poneyland"], None);
    /// ```
    pub fn or_default(self) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(Default::default()),
        }
    }
}

impl<K: Debug + Ord, V: Debug> Debug for Entry<'_, K, V> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            Entry::Vacant(ref v) => f.debug_tuple("Entry").field(v).finish(),
            Entry::Occupied(ref o) => f.debug_tuple("Entry").field(o).finish(),
        }
    }
}

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
        core::mem::drop(Self {
            root: core::mem::replace(&mut self.root, None),
            len: core::mem::replace(&mut self.len, 0),
            _marker: PhantomData,
        });
    }

    fn search_tree<Q>(&self, key: &Q) -> SearchResult<K, V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        let mut node_option = self.root;
        let mut parent_option = None;

        while let Some(node) = node_option {
            parent_option = node_option;
            unsafe {
                match (*node.as_ptr()).key.borrow().cmp(key) {
                    Ordering::Equal => return Found(node),
                    Ordering::Greater => node_option = (*node.as_ptr()).left,
                    Ordering::Less => node_option = (*node.as_ptr()).right,
                }
            }
        }

        PotentialParentForInsertion(parent_option)
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

    fn first(mut node: NonNull<Node<K, V>>) -> NonNull<Node<K, V>> {
        while let Some(left_node) = unsafe { (*node.as_ptr()).left } {
            node = left_node;
        }
        node
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
            let first_node = Self::first(root);
            unsafe { (&(*first_node.as_ptr()).key, &(*first_node.as_ptr()).val) }
        })
    }

    /// Returns the first entry in the map for in-place manipulation.
    /// The key of this entry is the minimum key in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map = RBTreeMap::new();
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    /// if let Some(mut entry) = map.first_entry() {
    ///     if *entry.key() > 0 {
    ///         entry.insert("first");
    ///     }
    /// }
    /// assert_eq!(*map.get(&1).unwrap(), "first");
    /// assert_eq!(*map.get(&2).unwrap(), "b");
    /// ```
    pub fn first_entry(&mut self) -> Option<OccupiedEntry<'_, K, V>>
    where
        K: Ord,
    {
        self.root.map(|root| OccupiedEntry {
            node: Self::first(root),
            tree: self,
        })
    }

    /// Removes and returns the first element in the map.
    /// The key of this element is the minimum key that was in the map.
    ///
    /// # Examples
    ///
    /// Draining elements in ascending order, while keeping a usable map each iteration.
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map = RBTreeMap::new();
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    /// while let Some((key, _val)) = map.pop_first() {
    ///     assert!(map.iter().all(|(k, _v)| *k > key));
    /// }
    /// assert!(map.is_empty());
    /// ```
    pub fn pop_first(&mut self) -> Option<(K, V)>
    where
        K: Ord,
    {
        self.first_entry().map(|entry| entry.remove_entry())
    }

    fn last(mut node: NonNull<Node<K, V>>) -> NonNull<Node<K, V>> {
        while let Some(right_node) = unsafe { (*node.as_ptr()).right } {
            node = right_node;
        }
        node
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
        self.root.map(|root| {
            let last_node = Self::last(root);
            unsafe { (&(*last_node.as_ptr()).key, &(*last_node.as_ptr()).val) }
        })
    }

    /// Returns the last entry in the map for in-place manipulation.
    /// The key of this entry is the maximum key in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map = RBTreeMap::new();
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    /// if let Some(mut entry) = map.last_entry() {
    ///     if *entry.key() > 0 {
    ///         entry.insert("last");
    ///     }
    /// }
    /// assert_eq!(*map.get(&1).unwrap(), "a");
    /// assert_eq!(*map.get(&2).unwrap(), "last");
    /// ```
    pub fn last_entry(&mut self) -> Option<OccupiedEntry<'_, K, V>>
    where
        K: Ord,
    {
        self.root.map(|root| OccupiedEntry {
            node: Self::last(root),
            tree: self,
        })
    }

    /// Removes and returns the last element in the map.
    /// The key of this element is the maximum key that was in the map.
    ///
    /// # Examples
    ///
    /// Draining elements in descending order, while keeping a usable map each iteration.
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map = RBTreeMap::new();
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    /// while let Some((key, _val)) = map.pop_last() {
    ///     assert!(map.iter().all(|(k, _v)| *k < key));
    /// }
    /// assert!(map.is_empty());
    /// ```
    pub fn pop_last(&mut self) -> Option<(K, V)>
    where
        K: Ord,
    {
        self.last_entry().map(|entry| entry.remove_entry())
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
        matches!(self.search_tree(key), Found(_))
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

    fn insert_node(
        &mut self,
        key: K,
        val: V,
        parent_option: Option<NonNull<Node<K, V>>>,
    ) -> NonNull<Node<K, V>>
    where
        K: Ord,
    {
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

        // update parent's left or right child to the new node
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

        new_node
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
                let _ = self.insert_node(key, val, parent_option);
                None
            }
        }
    }

    unsafe fn left_rotate(&mut self, node: NonNull<Node<K, V>>) {
        // rotation is not possible if right child is empty
        if let Some(right_child) = (*node.as_ptr()).right {
            //
            //     g                  g
            //     |                  |
            //     n         -->     rc
            //    / \                / \
            //   lc  rc             n   rrgc
            //      /  \           / \
            //   rlgc  rrgc       lc rlgc
            //
            (*node.as_ptr()).right = (*right_child.as_ptr()).left;
            if let Some(right_left_gchild) = (*right_child.as_ptr()).left {
                (*right_left_gchild.as_ptr()).parent = Some(node);
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
            //
            //         g                 g
            //         |                 |
            //         n       -->      lc
            //        / \               / \
            //       lc  rc          llgc  n
            //      /  \                  / \
            //   llgc  lrgc           lrgc   rc
            //
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
            // loop invariant: node is red

            // if parent is black, we are done
            if (*parent.as_ptr()).is_black() {
                break;
            }

            // since parent is red and root is always black, grandparent will exist
            let gparent = (*parent.as_ptr())
                .parent
                .expect("where are you grandparent?");

            if Some(parent) == (*gparent.as_ptr()).left {
                let uncle_option = (*gparent.as_ptr()).right;
                match uncle_option {
                    Some(uncle) if (*uncle.as_ptr()).is_red() => {
                        // case 1: node's uncle is red.
                        //
                        // action: flip colors
                        //
                        // indicate color with case: black is uppercase and red is lowercase
                        //
                        //       G            g
                        //      / \          / \
                        //     p   u  -->   P   U
                        //    /            /
                        //   n            n
                        //
                        // since g's parent might be red, need to recurse at g
                        (*parent.as_ptr()).color = Color::Black;
                        (*uncle.as_ptr()).color = Color::Black;
                        (*gparent.as_ptr()).color = Color::Red;
                        node = gparent;
                    }
                    _ => {
                        if Some(node) == (*parent.as_ptr()).right {
                            // case 2: uncle is black (remember NULLs are also considered black)
                            // and node is parent's right child
                            //
                            // action: left rotate at parent
                            //
                            //      G             G
                            //     / \           / \
                            //    p   U  -->    n   U
                            //     \           /
                            //      n         p
                            //
                            // fall through to caes 3 to fix red-property
                            self.left_rotate(parent);
                            parent = node;
                        }

                        // case 3: uncle is black and node is parent's left child
                        //
                        // action: right rotate at grandparent
                        //
                        //        G           P
                        //       / \         / \
                        //      p   U  -->  n   g
                        //     /                 \
                        //    n                   U
                        //
                        (*parent.as_ptr()).color = Color::Black;
                        (*gparent.as_ptr()).color = Color::Red;
                        self.right_rotate(gparent);
                        break;
                    }
                }
            } else {
                // same as if case but with "right" and "left" exchanged
                let uncle_option = (*gparent.as_ptr()).left;
                match uncle_option {
                    // both parent and uncle are red
                    Some(uncle) if (*uncle.as_ptr()).is_red() => {
                        // case 1
                        (*parent.as_ptr()).color = Color::Black;
                        (*uncle.as_ptr()).color = Color::Black;
                        (*gparent.as_ptr()).color = Color::Red;
                        node = gparent;
                    }
                    _ => {
                        if Some(node) == (*parent.as_ptr()).left {
                            // case 2
                            self.right_rotate(parent);
                            parent = node;
                        }

                        // case 3
                        (*parent.as_ptr()).color = Color::Black;
                        (*gparent.as_ptr()).color = Color::Red;
                        self.left_rotate(gparent);
                        break;
                    }
                }
            }
        }

        // SAFETY: since we came here from insert, the tree is not empty
        (*self.root.expect("tree empty after insertion!").as_ptr()).color = Color::Black;
    }

    unsafe fn remove_node<Q>(&mut self, node: NonNull<Node<K, V>>) -> (K, V)
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        let mut rebalance = None;

        match ((*node.as_ptr()).left, (*node.as_ptr()).right) {
            (None, right_child_option) => {
                // case 1a: node to erase has only 1 child
                //
                // child must be red due to the black-property and
                // node must be black due to the red-property
                self.transplant(node, right_child_option);
                match right_child_option {
                    Some(right_child) => {
                        (*right_child.as_ptr()).color = Color::Black;
                    }
                    None => {
                        // no children! need to rebalance only if the node is black
                        if (*node.as_ptr()).is_black() {
                            rebalance = (*node.as_ptr()).parent;
                        }
                    }
                }
            }
            (left_child_option @ Some(left_child), None) => {
                // case 1b: only 1 child, a left one
                self.transplant(node, left_child_option);
                (*left_child.as_ptr()).color = Color::Black;
            }
            (left_child_option @ Some(left_child), right_child_option @ Some(right_child)) => {
                let successor = Self::first(right_child);
                let successor_right_child_option = (*successor.as_ptr()).right;

                // new parent of successor's right child
                let successor_right_child_parent = if successor == right_child {
                    // case 2: node's successor is its right child
                    //
                    //     (n)          (s)
                    //     / \          / \
                    //   (x) (s)  ->  (x) (c)
                    //         \
                    //         (c)
                    //
                    Some(successor)
                } else {
                    // case 3: node's successor is leftmost under it's right child subtree
                    //
                    //     (n)          (s)
                    //     / \          / \
                    //   (x) (y)  ->  (x) (y)
                    //       /            /
                    //     (p)          (p)
                    //     /            /
                    //   (s)          (c)
                    //     \
                    //     (c)
                    //

                    // replace successor by its right child
                    self.transplant(successor, successor_right_child_option);

                    // node's right child becomes successor's right child
                    (*successor.as_ptr()).right = right_child_option;
                    (*right_child.as_ptr()).parent = Some(successor);

                    (*successor.as_ptr()).parent
                };

                // replace node by its successor
                self.transplant(node, Some(successor));

                // give node's left child to its successsor
                (*successor.as_ptr()).left = left_child_option;
                (*left_child.as_ptr()).parent = Some(successor);

                // give node's color to its successor
                (*successor.as_ptr()).color = (*node.as_ptr()).color;

                if let Some(successor_right_child) = successor_right_child_option {
                    // successor's right (and only) child must be red due to the black-property and
                    // successor must be black due to the red-property

                    // give successor's right child the color of the successor
                    (*successor_right_child.as_ptr()).color = Color::Black;
                } else if (*successor.as_ptr()).is_black() {
                    // need to rebalance only if successor has no child and is black
                    rebalance = successor_right_child_parent;
                }
            }
        }

        if let Some(rebalance_node) = rebalance {
            self.remove_fixup(rebalance_node);
        }

        self.len -= 1;

        let boxed_node = Box::from_raw(node.as_ptr());
        (boxed_node.key, boxed_node.val)
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
        self.remove_entry(key).map(|(_key, val)| val)
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

        if let Some(node) = replacement_option {
            (*node.as_ptr()).parent = (*to_replace.as_ptr()).parent;
        }
    }

    // only need to handle the no-childs case
    unsafe fn remove_fixup(&mut self, mut parent: NonNull<Node<K, V>>) {
        let mut node_option = None;
        while node_option != self.root
            && node_option.map_or(true, |node| (*node.as_ptr()).is_black())
        {
            if node_option == (*parent.as_ptr()).left {
                // SAFETY: sibling must exist since all leaf paths going through
                // parent and node have 1 less black node count
                let mut sibling = (*parent.as_ptr()).right.expect("missing sibling");
                if (*sibling.as_ptr()).is_red() {
                    // case 1: node's sibling is red
                    //
                    // action: left rotate at parent
                    //
                    //     P               S
                    //    / \             / \
                    //   N   s    -->    p   Sr
                    //      / \         / \
                    //     Sl  Sr      N   Sl
                    //
                    (*sibling.as_ptr()).color = Color::Black;
                    (*parent.as_ptr()).color = Color::Red;
                    self.left_rotate(parent);
                    // sibling must have black children, since the leaf paths through
                    // parent and sibling hasn't had an extra black till now
                    sibling = (*parent.as_ptr())
                        .right
                        .expect("red sibling must have black children");
                }

                let sibling_right_child_option = (*sibling.as_ptr()).right;
                if sibling_right_child_option.map_or(true, |node| (*node.as_ptr()).is_black()) {
                    let sibling_left_child_option = (*sibling.as_ptr()).left;
                    if sibling_left_child_option.map_or(true, |node| (*node.as_ptr()).is_black()) {
                        // case 2: sibling is black and both its children are black
                        //
                        // action: flip sibling's color
                        //
                        // (p could be either color here)
                        //
                        //    (p)           (p)
                        //    / \           / \
                        //   N   S    -->  N   s
                        //      / \           / \
                        //     Sl  Sr        Sl  Sr
                        //
                        // fix any black-property violation by flipping p to black
                        // if it was red or by recursing at p.
                        //
                        (*sibling.as_ptr()).color = Color::Red;
                        if (*parent.as_ptr()).is_red() {
                            (*parent.as_ptr()).color = Color::Black;
                        } else {
                            node_option = Some(parent);
                            if let Some(gparent) = (*parent.as_ptr()).parent {
                                parent = gparent;
                                continue;
                            }
                        }
                        break;
                    }

                    // case 3: sibling is black, sibling's left child is red and right is black
                    //
                    // action: color flips & right rotate at sibling
                    //
                    //
                    //    (p)           (p)
                    //    / \           / \
                    //   N   S    -->  N   Sl
                    //      / \             \
                    //     sl  Sr            s
                    //                        \
                    //                         Sr
                    //

                    // SAFETY: already checked sibling's left child for None and black
                    let sibling_left_child =
                        sibling_left_child_option.expect("sibling's left child empty!");
                    (*sibling_left_child.as_ptr()).color = Color::Black;
                    (*sibling.as_ptr()).color = Color::Red;
                    self.right_rotate(sibling);
                    // new sibling is original sibling's left child
                    sibling = sibling_left_child;
                }

                // case 4: sibling is black, sibling's right child is red
                //
                // action: color flips and left rotate at parent
                //
                //
                //     (p)             (s)
                //     / \             / \
                //    N   S     -->   P   Sr
                //       / \         / \
                //     (sl) sr      N  (sl)
                //

                // SAFETY: already checked sibling's right child for None and black
                let sibling_right_child =
                    sibling_right_child_option.expect("sibling's right child empty!");
                (*sibling.as_ptr()).color = (*parent.as_ptr()).color;
                (*parent.as_ptr()).color = Color::Black;
                (*sibling_right_child.as_ptr()).color = Color::Black;

                self.left_rotate(parent);
                break;
            } else {
                // same as if case but with "right" and "left" exchanged

                let mut sibling = (*parent.as_ptr()).left.expect("missing sibling");
                if (*sibling.as_ptr()).is_red() {
                    // case 1
                    (*sibling.as_ptr()).color = Color::Black;
                    (*parent.as_ptr()).color = Color::Red;
                    self.right_rotate(parent);
                    sibling = (*parent.as_ptr())
                        .left
                        .expect("red sibling must have black children");
                }

                let sibling_left_child_option = (*sibling.as_ptr()).left;
                if sibling_left_child_option.map_or(true, |node| (*node.as_ptr()).is_black()) {
                    let sibling_right_child_option = (*sibling.as_ptr()).right;
                    if sibling_right_child_option.map_or(true, |node| (*node.as_ptr()).is_black()) {
                        // case 2
                        (*sibling.as_ptr()).color = Color::Red;
                        if (*parent.as_ptr()).is_red() {
                            (*parent.as_ptr()).color = Color::Black;
                        } else {
                            node_option = Some(parent);
                            if let Some(gparent) = (*parent.as_ptr()).parent {
                                parent = gparent;
                                continue;
                            }
                        }
                        break;
                    }

                    // case 3
                    let sibling_right_child =
                        sibling_right_child_option.expect("sibling's right child empty!");
                    (*sibling_right_child.as_ptr()).color = Color::Black;
                    (*sibling.as_ptr()).color = Color::Red;
                    self.left_rotate(sibling);
                    sibling = sibling_right_child;
                }

                // case 4

                let sibling_left_child =
                    sibling_left_child_option.expect("sibling's left child empty!");
                (*sibling.as_ptr()).color = (*parent.as_ptr()).color;
                (*parent.as_ptr()).color = Color::Black;
                (*sibling_left_child.as_ptr()).color = Color::Black;

                self.right_rotate(parent);
                break;
            }
        }
    }

    /// Removes a key from the map, returning the stored key and value if the key
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
    /// assert_eq!(map.remove_entry(&1), Some((1, "a")));
    /// assert_eq!(map.remove_entry(&1), None);
    /// ```
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        match self.search_tree(key) {
            Found(node) => Some(unsafe { self.remove_node(node) }),
            PotentialParentForInsertion(_) => None,
        }
    }

    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut count: RBTreeMap<&str, usize> = RBTreeMap::new();
    ///
    /// // count the number of occurrences of letters in the vec
    /// for x in ["a", "b", "a", "c", "a", "b"] {
    ///     count.entry(x).and_modify(|curr| *curr += 1).or_insert(1);
    /// }
    ///
    /// assert_eq!(count["a"], 3);
    /// assert_eq!(count["b"], 2);
    /// assert_eq!(count["c"], 1);
    /// ```
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V>
    where
        K: Ord,
    {
        match self.search_tree(&key) {
            Found(node) => Entry::Occupied(OccupiedEntry { node, tree: self }),
            PotentialParentForInsertion(parent_option) => Entry::Vacant(VacantEntry {
                key,
                potential_parent: parent_option,
                tree: self,
            }),
        }
    }

    /// Gets an iterator over the entries of the map, sorted by key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map = RBTreeMap::new();
    /// map.insert(3, "c");
    /// map.insert(2, "b");
    /// map.insert(1, "a");
    ///
    /// for (key, value) in map.iter() {
    ///     println!("{key}: {value}");
    /// }
    ///
    /// let (first_key, first_value) = map.iter().next().unwrap();
    /// assert_eq!((*first_key, *first_value), (1, "a"));
    /// ```
    pub fn iter(&self) -> Iter<'_, K, V> {
        self.into_iter()
    }

    /// Gets a mutable iterator over the entries of the map, sorted by key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let mut map = RBTreeMap::from([
    ///    ("a", 1),
    ///    ("b", 2),
    ///    ("c", 3),
    /// ]);
    ///
    /// // add 10 to the value if the key isn't "a"
    /// for (key, value) in map.iter_mut() {
    ///     if key != &"a" {
    ///         *value += 10;
    ///     }
    /// }
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        self.into_iter()
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

impl<K, V> Drop for RBTreeMap<K, V> {
    fn drop(&mut self) {
        core::mem::drop(unsafe { core::ptr::read(self) }.into_iter())
    }
}

impl<K: Debug, V: Debug> Debug for RBTreeMap<K, V> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V> FromIterator<(K, V)> for RBTreeMap<K, V>
where
    K: Ord,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> RBTreeMap<K, V> {
        // TODO: collect, sort and create tree from sorted vec
        let mut tree = Self::new();
        for (key, val) in iter {
            tree.insert(key, val);
        }
        tree
    }
}

impl<K: Ord, V, const N: usize> From<[(K, V); N]> for RBTreeMap<K, V> {
    /// Converts a `[(K, V); N]` into a `RBTreeMap<(K, V)>`.
    ///
    /// ```
    /// use rbtreemap::RBTreeMap;
    ///
    /// let map1 = RBTreeMap::from([(1, 2), (3, 4)]);
    /// let map2: RBTreeMap<_, _> = [(1, 2), (3, 4)].into();
    /// assert_eq!(map1, map2);
    /// ```
    fn from(arr: [(K, V); N]) -> RBTreeMap<K, V> {
        Self::from_iter(arr)
    }
}

impl<'a, K, V> IntoIterator for &'a RBTreeMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Iter<'a, K, V> {
        let front = self.root.map(|root| RBTreeMap::first(root));
        let back = self.root.map(|root| RBTreeMap::last(root));
        Iter {
            front,
            back,
            len: self.len,
            _marker: PhantomData,
        }
    }
}

/// An iterator over the entries of a `RBTreeMap`.
///
/// This `struct` is created by the [`iter`] method on [`RBTreeMap`]. See its
/// documentation for more.
///
/// [`iter`]: RBTreeMap::iter
pub struct Iter<'a, K, V> {
    front: Option<NonNull<Node<K, V>>>,
    back: Option<NonNull<Node<K, V>>>,
    len: usize,
    _marker: PhantomData<(&'a K, &'a V)>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        if self.len == 0 {
            return None;
        }

        self.front.map(|node| {
            if let Some(right_child) = unsafe { (*node.as_ptr()).right } {
                self.front = Some(RBTreeMap::first(right_child));
            } else {
                self.front = None;
                let mut curr = node;
                while let Some(parent) = unsafe { (*curr.as_ptr()).parent } {
                    if unsafe { (*parent.as_ptr()).left } == Some(curr) {
                        self.front = Some(parent);
                        break;
                    }
                    curr = parent;
                }
            }

            self.len -= 1;
            unsafe { (&(*node.as_ptr()).key, &(*node.as_ptr()).val) }
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, K, V> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a V)> {
        if self.len == 0 {
            return None;
        }

        self.back.map(|node| {
            if let Some(left_child) = unsafe { (*node.as_ptr()).left } {
                self.back = Some(RBTreeMap::last(left_child));
            } else {
                self.back = None;
                let mut curr = node;
                while let Some(parent) = unsafe { (*curr.as_ptr()).parent } {
                    if unsafe { (*parent.as_ptr()).right } == Some(curr) {
                        self.back = Some(parent);
                        break;
                    }
                    curr = parent;
                }
            }
            self.len -= 1;
            unsafe { (&(*node.as_ptr()).key, &(*node.as_ptr()).val) }
        })
    }
}

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<'a, K, V> FusedIterator for Iter<'a, K, V> {}

impl<'a, K, V> IntoIterator for &'a mut RBTreeMap<K, V> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> IterMut<'a, K, V> {
        let front = self.root.map(|root| RBTreeMap::first(root));
        let back = self.root.map(|root| RBTreeMap::last(root));
        IterMut {
            front,
            back,
            len: self.len,
            _marker: PhantomData,
        }
    }
}

/// A mutable iterator over the entries of a `RBTreeMap`.
///
/// This `struct` is created by the [`iter_mut`] method on [`RBTreeMap`]. See its
/// documentation for more.
///
/// [`iter_mut`]: RBTreeMap::iter_mut
pub struct IterMut<'a, K, V> {
    front: Option<NonNull<Node<K, V>>>,
    back: Option<NonNull<Node<K, V>>>,
    len: usize,
    _marker: PhantomData<(&'a K, &'a V)>,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        if self.len == 0 {
            return None;
        }

        self.front.map(|node| {
            if let Some(right_child) = unsafe { (*node.as_ptr()).right } {
                self.front = Some(RBTreeMap::first(right_child));
            } else {
                self.front = None;
                let mut curr = node;
                while let Some(parent) = unsafe { (*curr.as_ptr()).parent } {
                    if unsafe { (*parent.as_ptr()).left } == Some(curr) {
                        self.front = Some(parent);
                        break;
                    }
                    curr = parent;
                }
            }

            self.len -= 1;
            unsafe { (&(*node.as_ptr()).key, &mut (*node.as_ptr()).val) }
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, K, V> DoubleEndedIterator for IterMut<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a mut V)> {
        if self.len == 0 {
            return None;
        }

        self.back.map(|node| {
            if let Some(left_child) = unsafe { (*node.as_ptr()).left } {
                self.back = Some(RBTreeMap::last(left_child));
            } else {
                self.back = None;
                let mut curr = node;
                while let Some(parent) = unsafe { (*curr.as_ptr()).parent } {
                    if unsafe { (*parent.as_ptr()).right } == Some(curr) {
                        self.back = Some(parent);
                        break;
                    }
                    curr = parent;
                }
            }
            self.len -= 1;
            unsafe { (&(*node.as_ptr()).key, &mut (*node.as_ptr()).val) }
        })
    }
}

impl<'a, K, V> ExactSizeIterator for IterMut<'a, K, V> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<'a, K, V> FusedIterator for IterMut<'a, K, V> {}

impl<K, V> IntoIterator for RBTreeMap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> IntoIter<K, V> {
        let me = ManuallyDrop::new(self);
        let front = me.root.map(|root| Self::first(root));
        let back = me.root.map(|root| Self::last(root));
        IntoIter {
            front,
            back,
            len: me.len,
        }
    }
}

/// An owning iterator over the entries of a `RBTreeMap`.
///
/// This `struct` is created by the [`into_iter`] method on [`RBTreeMap`]
/// (provided by the [`IntoIterator`] trait). See its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
/// [`IntoIterator`]: core::iter::IntoIterator
pub struct IntoIter<K, V> {
    front: Option<NonNull<Node<K, V>>>,
    back: Option<NonNull<Node<K, V>>>,
    len: usize,
}

impl<K, V> Drop for IntoIter<K, V> {
    fn drop(&mut self) {
        for _ in self.by_ref() {}
    }
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        if self.len == 0 {
            return None;
        }

        self.front.map(|node| {
            // if we have a right child, go down and take the leftmost child
            if let Some(right_child) = unsafe { (*node.as_ptr()).right } {
                self.front = Some(RBTreeMap::first(right_child));
                let parent_option = unsafe { (*node.as_ptr()).parent };
                unsafe {
                    (*right_child.as_ptr()).parent = parent_option;
                }
                if let Some(parent) = parent_option {
                    unsafe {
                        if Some(node) == (*parent.as_ptr()).left {
                            (*parent.as_ptr()).left = Some(right_child);
                        } else {
                            (*parent.as_ptr()).right = Some(right_child);
                        }
                    }
                }
            } else {
                self.front = None;
                let mut curr = node;
                while let Some(parent) = unsafe { (*curr.as_ptr()).parent } {
                    if unsafe { (*parent.as_ptr()).left } == Some(curr) {
                        self.front = Some(parent);
                        break;
                    }
                    curr = parent;
                }
            }
            self.len -= 1;
            let boxed_node = unsafe { Box::from_raw(node.as_ptr()) };
            (boxed_node.key, boxed_node.val)
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<K, V> DoubleEndedIterator for IntoIter<K, V> {
    fn next_back(&mut self) -> Option<(K, V)> {
        if self.len == 0 {
            return None;
        }

        self.back.map(|node| {
            if let Some(left_child) = unsafe { (*node.as_ptr()).left } {
                self.back = Some(RBTreeMap::last(left_child));
                let parent_option = unsafe { (*node.as_ptr()).parent };
                unsafe { (*left_child.as_ptr()).parent = parent_option };
                if let Some(parent) = parent_option {
                    unsafe {
                        if Some(node) == (*parent.as_ptr()).left {
                            (*parent.as_ptr()).left = Some(left_child);
                        } else {
                            (*parent.as_ptr()).right = Some(left_child);
                        }
                    }
                }
            } else {
                self.back = None;
                let mut curr = node;
                while let Some(parent) = unsafe { (*curr.as_ptr()).parent } {
                    if unsafe { (*parent.as_ptr()).right } == Some(curr) {
                        self.back = Some(parent);
                        break;
                    }
                    curr = parent;
                }
            }
            self.len -= 1;
            let boxed_node = unsafe { Box::from_raw(node.as_ptr()) };
            (boxed_node.key, boxed_node.val)
        })
    }
}

impl<K, V> ExactSizeIterator for IntoIter<K, V> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<K, V> FusedIterator for IntoIter<K, V> {}

#[cfg(test)]
mod test {
    use super::RBTreeMap;

    // from https://github.com/rust-lang/rust/blob/master/library/alloc/src/collections/btree/map/tests.rs
    #[test]
    fn test_iter() {
        // Miri is too slow
        let size = if cfg!(miri) { 200 } else { 10000 };
        let mut map = RBTreeMap::from_iter((0..size).map(|i| (i, i)));

        fn test<T>(size: usize, mut iter: T)
        where
            T: Iterator<Item = (usize, usize)>,
        {
            for i in 0..size {
                assert_eq!(iter.size_hint(), (size - i, Some(size - i)));
                assert_eq!(iter.next().unwrap(), (i, i));
            }
            assert_eq!(iter.size_hint(), (0, Some(0)));
            assert_eq!(iter.next(), None);
        }
        test(size, map.iter().map(|(&k, &v)| (k, v)));
        test(size, map.iter_mut().map(|(&k, &mut v)| (k, v)));
        test(size, map.into_iter());
    }

    #[test]
    fn test_iter_rev() {
        // Miri is too slow
        let size = if cfg!(miri) { 200 } else { 10000 };
        let mut map = RBTreeMap::from_iter((0..size).map(|i| (i, i)));

        fn test<T>(size: usize, mut iter: T)
        where
            T: Iterator<Item = (usize, usize)>,
        {
            for i in 0..size {
                assert_eq!(iter.size_hint(), (size - i, Some(size - i)));
                assert_eq!(iter.next().unwrap(), (size - i - 1, size - i - 1));
            }
            assert_eq!(iter.size_hint(), (0, Some(0)));
            assert_eq!(iter.next(), None);
        }
        test(size, map.iter().rev().map(|(&k, &v)| (k, v)));
        test(size, map.iter_mut().rev().map(|(&k, &mut v)| (k, v)));
        test(size, map.into_iter().rev());
    }
}
