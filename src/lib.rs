#![doc = include_str!("../README.md")]
#![cfg_attr(RUSTC_IS_NIGTHLY, feature(drain_filter))]
use cfg_if::cfg_if;
use core::borrow::Borrow;
use core::cmp::min;
use core::iter::FusedIterator;
use core::ops::ControlFlow;
use core::ops::{Deref, Index};
use core::option;
use derivative::Derivative;
use std::cmp::Ordering;
use std::slice::SliceIndex;
use std::{slice, vec};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// Action that the application must performed to undo
/// or redo
///
/// The type parameter `T` is the command type.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Action<T> {
    /// The client shall do the command refered by the inner parameter.
    Do(T),
    /// The client shall undo the command refered by the inner parameter.
    Undo(T),
}

/// The items stored in [Commands].
///
/// The list of `CommandItem` is accessible by dereferencing
/// the command list.
///
/// *NB*: The value inside the Undo variant is the number
/// of time the undo command is repeated minus 1.
///
/// # Example
///
/// ```
/// use undo_2::{Commands,CommandItem};
///
/// let mut commands = Commands::new();
///
/// #[derive(Debug,PartialEq)]
/// struct A;
///
/// commands.push(A);
/// commands.undo();
///
/// assert_eq!(*commands, [CommandItem::Command(A),CommandItem::Undo(0)]);
///
/// use CommandItem::Undo;
/// assert_eq!(*commands, [A.into(), Undo(0)]);
///
/// commands.push(A);
/// commands.undo();
/// commands.undo();
/// assert_eq!(*commands, [A.into(), Undo(0),A.into(),Undo(1)]);
/// ```
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum CommandItem<T> {
    // A command typically created by [Commands::push](Commands#method.push)
    Command(T),
    // Signify that `count+1` CommandItem previous to this item are undone.
    //
    // Where `count` refers to this variant field.
    Undo(usize),
}

/// Owns a slice of [commands](CommandItem) to undo and redo.
///
/// Commands are added by invoking [`push`](#method.push) method. [`undo`](#method.undo) and
/// [`redo`](#method.redo) return a list of [`Action<T>`] that the application must execute.
///
/// To see a full functional example, read [How to use it](index.html#how-to-use-it).
///
/// # Example
/// ```
/// use undo_2::{Action, Commands};
///
/// #[derive(Debug, Eq, PartialEq)]
/// enum Command {
///     A,
///     B,
/// }
/// use Command::*;
///
/// let mut commands = Commands::new();
///
/// commands.push(A);
/// commands.push(B);
///
/// let v: Vec<_> = commands.undo().collect();
/// assert_eq!(v, [Action::Undo(&B)]);
///
/// let v: Vec<_> = commands.undo().collect();
/// assert_eq!(v, [Action::Undo(&A)]);
///
/// commands.push(A);
///
/// let v: Vec<_> = commands.undo().collect();
/// assert_eq!(v, [Action::Undo(&A)]);
///
/// // undo the first 2 undos
/// let v: Vec<_> = commands.undo().collect();
/// assert_eq!(v, [Action::Do(&A), Action::Do(&B)]);
/// ```
///
/// # Representation
///
/// `Commands` owns a slice of [CommandItem] that is accesible
/// by dereferencing the command.
#[derive(Clone, Derivative)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derivative(Debug, PartialEq, Eq, Hash, Default(bound = ""))]
pub struct Commands<T> {
    commands: Vec<CommandItem<T>>,
    #[derivative(Debug = "ignore", PartialEq = "ignore", Hash = "ignore")]
    #[cfg_attr(feature = "serde", serde(skip))]
    undo_cache: Vec<Action<usize>>,
}

/// Specify a merge when calling [Commands::merge](Commands#method.merge)
///
/// The [`end`, `start`) bounds the slice of command that will
/// be removed during the merge. `end` and `start` are in reverse order
/// because [IterRealized] goes backward.
///
/// If `command` is `None` then the slice will be removed, otherwise if
/// the `command` is `Some(c)` the slice will be replace by `c`.
#[derive(Debug)]
pub struct Merge<'a, T> {
    pub start: IterRealized<'a, T>,
    pub end: IterRealized<'a, T>,
    pub command: Option<T>,
}

/// Specify a splice when calling [Commands::splice](Commands#method.splice)
///
/// The [`end`, `start`) bounds the slice of command that will
/// be removed during the merge. `end` and `start` are in reverse order
/// because [IterRealized] goes backward.
///
/// The removed slice is then replaced by the sequence (not reversed) of
/// commands denoted by `commands`.
#[derive(Debug)]
pub struct Splice<'a, T, I: IntoIterator<Item = T>> {
    pub start: IterRealized<'a, T>,
    pub end: IterRealized<'a, T>,
    pub commands: I,
}

#[derive(Derivative, Debug)]
#[derivative(Clone(bound = ""))]
/// Iterator of actions returned by [Commands::undo](Commands#method.undo) and
/// [Commands::redo](Commands#method.redo)
pub struct ActionIter<'a, T> {
    commands: &'a [CommandItem<T>],
    to_do: std::slice::Iter<'a, Action<usize>>,
}

#[derive(Derivative, Debug)]
#[derivative(Clone(bound = ""))]
/// The type of the iterator returned by [Commands::iter_realized](Commands#method.iter_realized).
pub struct IterRealized<'a, T> {
    commands: &'a [CommandItem<T>],
    current: usize,
}

impl<T> Commands<T> {
    /// Create a new empty command sequence of type `T`.
    pub fn new() -> Self {
        Self {
            commands: vec![],
            undo_cache: vec![],
        }
    }
    /// The capacity of the underlying storage
    pub fn capacity(&self) -> usize {
        self.commands.capacity()
    }
    /// Reserve space for new commands
    pub fn reserve(&mut self, additional: usize) {
        self.commands.reserve(additional)
    }
    /// Add the command `T`
    /// use undo_2::{Action, Commands};
    ///
    /// # Example
    /// ```
    /// use undo_2::Commands;
    ///
    /// #[derive(Debug, Eq, PartialEq)]
    /// enum Command {
    ///     A,
    ///     B,
    /// }
    /// use Command::*;
    ///
    /// let mut commands = Commands::new();
    ///
    /// commands.push(A);
    ///
    /// let v: Vec<_> = commands.iter_realized().collect();
    /// assert_eq!(v, [&A]);
    /// ```
    pub fn push(&mut self, command: T) {
        self.commands.push(CommandItem::Command(command));
    }

    /// Return an iterator over a sequence of actions to be performed by the client application to
    /// undo.
    ///
    /// # Example
    /// ```
    /// use undo_2::{Action,Commands};
    ///
    /// #[derive(Debug, Eq, PartialEq)]
    /// enum Command {
    ///     A,
    ///     B,
    ///     C
    /// }
    /// use Command::*;
    ///
    /// let mut commands = Commands::new();
    ///
    /// commands.push(A);
    /// commands.push(B);
    ///
    /// let v: Vec<_> = commands.undo().collect();
    /// assert_eq!(v, [Action::Undo(&B)]);
    ///
    /// commands.push(C);
    ///
    /// let v: Vec<_> = commands.undo().collect();
    /// assert_eq!(v, [Action::Undo(&C)]);
    ///
    /// let v: Vec<_> = commands.undo().collect();
    /// assert_eq!(v, [Action::Do(&B)]);
    ///
    /// let v: Vec<_> = commands.undo().collect();
    /// assert_eq!(v, [Action::Undo(&B)]);
    ///
    /// let v: Vec<_> = commands.undo().collect();
    /// assert_eq!(v, [Action::Undo(&A)]);
    ///
    /// let v: Vec<_> = commands.undo().collect();
    /// assert!(v.is_empty())
    /// ```
    #[must_use = "the returned actions should be realized"]
    pub fn undo(&mut self) -> ActionIter<'_, T> {
        self.undo_repeat(0)
    }
    /// Return an iterator over a sequence of actions to be performed by the client application to
    /// undo `repeat + 1` time.
    ///
    /// `undo_repeat(0)` is equivalent to `undo()`
    ///
    /// # Example
    /// ```
    /// use undo_2::{Action,Commands};
    ///
    /// #[derive(Debug, Eq, PartialEq)]
    /// enum Command {
    ///     A,
    ///     B,
    ///     C
    /// }
    /// use Command::*;
    ///
    /// let mut commands = Commands::new();
    ///
    /// commands.push(A);
    /// commands.push(B);
    ///
    /// let v: Vec<_> = commands.undo().collect();
    /// assert_eq!(v, [Action::Undo(&B)]);
    ///
    /// commands.push(C);
    ///
    /// let v: Vec<_> = commands.undo_repeat(3).collect();
    /// assert_eq!(v, [Action::Undo(&C), Action::Undo(&A)]);
    /// ```
    #[must_use = "the returned actions should be realized"]
    pub fn undo_repeat(&mut self, repeat: usize) -> ActionIter<'_, T> {
        let l = self.len();
        match self.commands.last_mut() {
            Some(CommandItem::Command(_)) => {
                let count = min(repeat, l - 1);
                self.commands.push(CommandItem::Undo(count));
                ActionIter::undo_at_count(
                    &self.commands,
                    &mut self.undo_cache,
                    l - 1 - count,
                    count,
                )
            }
            Some(CommandItem::Undo(i)) => {
                if *i + 2 < l {
                    let count = min(l - *i - 3, repeat);
                    *i = *i + 1 + count;
                    let t = l - *i - 2;
                    ActionIter::undo_at_count(&self.commands, &mut self.undo_cache, t, count)
                } else {
                    ActionIter::new()
                }
            }
            None => ActionIter::new(),
        }
    }
    /// An undo that skip undo branches.
    ///
    /// It returns the command that must be undone.
    ///
    /// It is equivalent to multiple successive call to `undo`. It behaves
    /// as a classical undo.
    ///
    /// # Example
    /// ```
    /// use undo_2::Commands;
    ///
    /// #[derive(Debug, Eq, PartialEq)]
    /// enum Command {
    ///     A,
    ///     B,
    ///     C,
    /// }
    /// use Command::*;
    ///
    /// let mut commands = Commands::new();
    ///
    /// commands.push(A);
    /// commands.push(B);
    /// commands.undo();
    /// commands.push(C);
    ///
    /// let c = commands.unbuild();
    /// assert_eq!(c, Some(&C));
    ///
    /// let c = commands.unbuild();
    /// assert_eq!(c, Some(&A));
    ///
    /// assert!(commands.unbuild().is_none());
    /// ```
    #[must_use = "the returned command should be undone"]
    pub fn unbuild(&mut self) -> Option<&'_ T> {
        let mut it = self.iter_realized();
        it.next()?;
        let start = it.current;
        let count = match it.next() {
            Some(_) => start - it.current,
            None => start + 1,
        };
        match self.commands.last_mut() {
            Some(CommandItem::Command(_)) => {
                self.commands.push(CommandItem::Undo(count - 1));
            }
            Some(CommandItem::Undo(i)) => *i += count,
            None => unreachable!(),
        }
        Some(match self.commands[start] {
            CommandItem::Command(ref c) => c,
            _ => unreachable!(),
        })
    }
    /// Return an iterator over a sequence of actions to be performed by the client application to
    /// redo.
    ///
    /// # Example
    /// ```
    /// use undo_2::{Action,Commands};
    ///
    /// #[derive(Debug, Eq, PartialEq)]
    /// enum Command {
    ///     A,
    ///     B,
    /// }
    /// use Command::*;
    ///
    /// let mut commands = Commands::new();
    ///
    /// commands.push(A);
    /// commands.push(B);
    /// commands.undo();
    /// let v: Vec<_> = commands.redo().collect();
    ///
    /// assert_eq!(v, [Action::Do(&B)]);
    /// ```
    #[must_use = "the returned actions should be realized"]
    pub fn redo(&mut self) -> ActionIter<'_, T> {
        self.redo_repeat(0)
    }
    /// Return an iterator over a sequence of actions to be performed by the client application to
    /// redo `repeat + 1` time.
    ///
    /// # Example
    /// ```
    /// use undo_2::{Action,Commands};
    ///
    /// #[derive(Debug, Eq, PartialEq)]
    /// enum Command {
    ///     A,
    ///     B,
    /// }
    /// use Command::*;
    ///
    /// let mut commands = Commands::new();
    ///
    /// commands.push(A);
    /// commands.push(B);
    /// commands.undo();
    /// commands.undo();
    /// let v: Vec<_> = commands.redo_repeat(1).collect();
    ///
    /// assert_eq!(v, [Action::Do(&A),Action::Do(&B)]);
    /// ```
    #[must_use = "the returned actions should be realized"]
    pub fn redo_repeat(&mut self, repeat: usize) -> ActionIter<'_, T> {
        let l = self.len();
        match self.commands.last_mut() {
            Some(CommandItem::Undo(i)) => {
                if let Some(ni) = i.checked_sub(repeat + 1) {
                    let t = l - 2 - *i;
                    *i = ni;
                    ActionIter::do_at_count(&self.commands, &mut self.undo_cache, t, repeat)
                } else {
                    let count = *i;
                    self.commands.pop();
                    ActionIter::do_at_count(&self.commands, &mut self.undo_cache, l - 2, count)
                }
            }
            _ => ActionIter::new(),
        }
    }
    /// Return an iterator over a sequence of actions to be performed by the client application to
    /// redo all undo.
    ///
    /// # Example
    /// ```
    /// use undo_2::{Action,Commands};
    ///
    /// #[derive(Debug, Eq, PartialEq)]
    /// enum Command {
    ///     A,
    ///     B,
    ///     C,
    /// }
    /// use Command::*;
    ///
    /// let mut commands = Commands::new();
    ///
    /// commands.push(A);
    /// commands.push(B);
    /// commands.undo();
    /// commands.undo();
    ///
    /// let v: Vec<_> = commands.redo_all().collect();
    /// assert_eq!(v, [Action::Do(&A), Action::Do(&B)]);
    /// ```
    #[must_use = "the returned actions should be realized"]
    pub fn redo_all(&mut self) -> ActionIter<'_, T> {
        let l = self.len();
        match self.commands.last_mut() {
            Some(CommandItem::Undo(i)) => {
                let count = *i;
                self.commands.pop();
                ActionIter::do_at_count(&self.commands, &mut self.undo_cache, l - 2, count)
            }
            _ => ActionIter::new(),
        }
    }
    /// Return `true` if the last action is an undo.
    ///
    /// # Example
    /// ```
    /// use undo_2::Commands;
    ///
    /// #[derive(Debug, Eq, PartialEq)]
    /// enum Command {
    ///     A,
    ///     B,
    /// }
    /// use Command::*;
    ///
    /// let mut commands = Commands::new();
    /// assert!(!commands.is_undoing());
    ///
    /// commands.push(A);
    /// assert!(!commands.is_undoing());
    ///
    /// commands.undo();
    /// assert!(commands.is_undoing());
    ///
    /// commands.push(A);
    /// commands.push(A);
    /// commands.undo();
    /// commands.undo();
    /// assert!(commands.is_undoing());
    /// commands.redo();
    /// assert!(commands.is_undoing());
    /// commands.redo();
    /// assert!(!commands.is_undoing());
    /// ```
    pub fn is_undoing(&self) -> bool {
        matches!(self.commands.last(), Some(CommandItem::Undo(_)))
    }

    /// Return the index of the first realized [command item](CommandItem).
    ///
    /// # Example
    /// ```
    /// use undo_2::*;
    /// #[derive(Debug, Eq, PartialEq)]
    /// enum Command {
    ///     A,
    ///     B,
    /// }
    /// use Command::*;
    ///
    /// let mut c = Commands::new();
    ///
    /// c.push(A);
    /// c.push(B);
    ///
    /// let v: Vec<_> = c.iter().collect();
    /// assert_eq!(v, [&CommandItem::Command(A), &CommandItem::Command(B)]);
    ///
    /// assert_eq!(c.current_command_index(), Some(1));
    ///
    /// c.undo();
    ///
    /// let v: Vec<_> = c.iter().collect();
    /// assert_eq!(v, [&CommandItem::Command(A), &CommandItem::Command(B), &CommandItem::Undo(0)]);
    ///
    /// assert_eq!(c.current_command_index(), Some(0));
    /// ```
    pub fn current_command_index(&self) -> Option<usize> {
        let mut it = self.iter_realized();
        it.next()?;
        Some(it.current)
    }

    /// Repeat undo or redo so that the last realiazed command correspond to
    /// the [CommandItem] index passed `index`.
    ///
    /// ```
    /// use undo_2::{Action,Commands, CommandItem};
    /// use std::time::{Instant, Duration};
    ///
    /// #[derive(Debug, Eq, PartialEq)]
    /// enum Command {
    ///     A,
    ///     B,
    ///     C,
    ///     D,
    ///     E,
    /// }
    /// use Command::*;
    ///
    /// let mut commands = Commands::new();
    ///
    /// let t0 = Instant::now();
    /// let t1 = t0 + Duration::from_secs(1);
    /// let t2 = t0 + Duration::from_secs(2);
    /// let t3 = t0 + Duration::from_secs(3);
    /// let t4 = t0 + Duration::from_secs(4);
    /// commands.push((t0,A));
    /// commands.push((t1,B));
    /// commands.undo();
    /// commands.push((t2,C));
    /// commands.push((t3,D));
    /// commands.undo();
    /// commands.undo();
    /// commands.push((t4,E));
    ///
    ///
    /// let v: Vec<_> = commands.iter_realized().collect();
    /// assert_eq!(v, [&(t4,E),&(t0,A)]);
    ///
    /// let index = commands.iter().position(|item| match item {
    ///         CommandItem::Command(item) => item.0 == t2,
    ///         _ => false
    ///     }).unwrap();
    ///
    /// let actions = commands.undo_or_redo_to_index(index);
    /// let a: Vec<_> = actions.collect();
    /// assert_eq!(a, [Action::Undo(&(t4,E)), Action::Do(&(t2,C))]);
    ///
    /// let v: Vec<_> = commands.iter_realized().collect();
    /// assert_eq!(v, [&(t2,C),&(t0,A)]);
    /// ```
    pub fn undo_or_redo_to_index(&mut self, i: usize) -> ActionIter<'_, T> {
        use CommandItem::*;
        let cur_i = match self.last() {
            None => return ActionIter::new(),
            Some(Command(_)) => self.len() - 1,
            Some(Undo(i)) => self.len() - 2 - i,
        };
        match i.cmp(&cur_i) {
            Ordering::Greater => self.redo_repeat(i - cur_i - 1),
            Ordering::Less => self.undo_repeat(cur_i - i - 1),
            Ordering::Equal => ActionIter::new(),
        }
    }
    /// Clear all the commands.
    ///
    /// # Example
    ///
    /// ```
    /// use undo_2::Commands;
    ///
    /// #[derive(Debug, Eq, PartialEq)]
    /// enum Command {
    ///     A,
    ///     B,
    /// }
    /// use Command::*;
    ///
    /// let mut commands = Commands::new();
    ///
    /// commands.push(A);
    /// commands.push(B);
    ///
    /// commands.clear();
    ///
    /// let v: Vec<_> = commands.iter_realized().collect();
    /// assert_eq!(v.len(), 0);
    /// ```
    pub fn clear(&mut self) {
        self.commands.clear();
    }
    /// Remove all removable commands that have been added before the
    /// first item fulfilling the predicate.
    ///
    /// A command is removable if it was added before the predicate fulfilling item
    /// and is not covered by any undo.
    ///
    /// Complexity: O(n)
    ///
    /// ```
    /// use undo_2::{Action,Commands};
    /// use std::time::{Instant, Duration};
    ///
    /// #[derive(Debug, Eq, PartialEq)]
    /// enum Command {
    ///     A,
    ///     B,
    ///     C,
    ///     D,
    ///     E,
    /// }
    /// use Command::*;
    ///
    /// let mut commands = Commands::new();
    ///
    /// let t0 = Instant::now();
    /// let t1 = t0 + Duration::from_secs(1);
    /// let t2 = t0 + Duration::from_secs(2);
    /// let t3 = t0 + Duration::from_secs(3);
    /// let t4 = t0 + Duration::from_secs(4);
    /// commands.push((t0,A));
    /// commands.push((t1,B));
    /// commands.push((t2,C));
    /// commands.push((t3,D));
    /// commands.push((t4,E));
    ///
    /// commands.remove_until(|(t, _)| *t > t1);
    ///
    /// let v: Vec<_> = commands.iter_realized().collect();
    /// assert_eq!(v, [&(t4,E),&(t3,D), &(t2,C)]);
    ///
    ///
    /// let mut commands = Commands::new();
    ///
    /// commands.push((t0,A));
    /// commands.push((t1,B)); //B
    /// commands.push((t2,C));
    /// commands.undo();
    /// commands.undo();// undo covering B
    /// commands.push((t3,D));
    /// commands.push((t4,E));
    ///
    /// commands.remove_until(|(t, _)| *t > t1);
    ///
    /// commands.undo();//remove E
    /// commands.undo();//remove D
    /// commands.undo();//undo the 2 undos
    ///
    /// // B not removed because it is covered by an undo
    /// let v: Vec<_> = commands.iter_realized().collect();
    /// assert_eq!(v, [&(t2,C),&(t1,B)]);
    ///
    /// ```
    pub fn remove_until(&mut self, mut stop_pred: impl FnMut(&T) -> bool) {
        if let Some(i) = self.commands.iter().position(move |c| match c {
            CommandItem::Undo(_) => false,
            CommandItem::Command(c) => stop_pred(c),
        }) {
            self.remove_first(i)
        }
    }
    /// Try to keep `count` most recent commands by dropping removable commands.
    ///
    /// A command is removable if it was added before the 'count' last commands
    /// and is not covered by any undo.
    ///
    /// Complexity: O(n)
    ///
    /// ```
    /// use undo_2::{Action,Commands};
    /// use std::time::{Instant, Duration};
    ///
    /// #[derive(Debug, Eq, PartialEq)]
    /// enum Command {
    ///     A,
    ///     B,
    ///     C,
    ///     D,
    ///     E,
    /// }
    /// use Command::*;
    ///
    /// let mut commands = Commands::new();
    ///
    /// let t0 = Instant::now();
    /// let t1 = t0 + Duration::from_secs(1);
    /// let t2 = t0 + Duration::from_secs(2);
    /// let t3 = t0 + Duration::from_secs(3);
    /// let t4 = t0 + Duration::from_secs(4);
    /// commands.push((t0,A));
    /// commands.push((t1,B));
    /// commands.push((t2,C));
    /// commands.push((t3,D));
    /// commands.push((t4,E));
    ///
    /// commands.keep_last(2);
    ///
    /// let v: Vec<_> = commands.iter_realized().collect();
    /// assert_eq!(v, [&(t4,E),&(t3,D)]);
    ///
    ///
    /// let mut commands = Commands::new();
    ///
    /// commands.push((t0,A));
    /// commands.push((t1,B)); //B
    /// commands.push((t2,C));
    /// commands.undo();
    /// commands.undo();// undo covering B
    /// commands.push((t3,D));
    /// commands.push((t4,E));
    ///
    /// // sequence of undo count for 1
    /// // so try to remove A and B
    /// commands.keep_last(4);
    ///
    /// commands.undo();//remove E
    /// commands.undo();//remove D
    /// commands.undo();//undo the 2 undos
    ///
    /// // B not removed because it is covered by an undo
    /// let v: Vec<_> = commands.iter_realized().collect();
    /// assert_eq!(v, [&(t2,C),&(t1,B)]);
    /// ```
    pub fn keep_last(&mut self, count: usize) {
        let i = self.len().saturating_sub(count);
        self.remove_first(i)
    }
    /// Remove `count` or less of the oldest command.
    ///
    /// Less commands may be dropped to ensure that none of the dropped
    /// command is covered by an undo within the recent non dropped commands.
    ///
    /// Complexity: O(n)
    ///
    /// ```
    /// use undo_2::{Action,Commands};
    /// use std::time::{Instant, Duration};
    ///
    /// #[derive(Debug, Eq, PartialEq)]
    /// enum Command {
    ///     A,
    ///     B,
    ///     C,
    ///     D,
    ///     E,
    /// }
    /// use Command::*;
    ///
    /// let mut commands = Commands::new();
    ///
    /// let t0 = Instant::now();
    /// let t1 = t0 + Duration::from_secs(1);
    /// let t2 = t0 + Duration::from_secs(2);
    /// let t3 = t0 + Duration::from_secs(3);
    /// let t4 = t0 + Duration::from_secs(4);
    /// commands.push((t0,A));
    /// commands.push((t1,B));
    /// commands.push((t2,C));
    /// commands.push((t3,D));
    /// commands.push((t4,E));
    ///
    /// commands.remove_first(3);
    ///
    /// let v: Vec<_> = commands.iter_realized().collect();
    /// assert_eq!(v, [&(t4,E),&(t3,D)]);
    ///
    ///
    /// let mut commands = Commands::new();
    ///
    /// commands.push((t0,A));
    /// commands.push((t1,B)); //B
    /// commands.push((t2,C));
    /// commands.undo();
    /// commands.undo();// undo covering B
    /// commands.push((t3,D));
    /// commands.push((t4,E));
    ///
    /// // sequence of undo count for 1
    /// // so try to remove A and B
    /// commands.remove_first(2);
    ///
    /// commands.undo();//remove E
    /// commands.undo();//remove D
    /// commands.undo();//undo the 2 undos
    ///
    /// // B not removed because it is covered by an undo
    /// let v: Vec<_> = commands.iter_realized().collect();
    /// assert_eq!(v, [&(t2,C),&(t1,B)]);
    /// ```
    pub fn remove_first(&mut self, i: usize) {
        let j = self.remove_i(i, self.commands.len());
        self.commands.drain(..j);
    }
    fn remove_i(&self, mut i: usize, end: usize) -> usize {
        let i0 = i;
        for j in i0..end {
            if let CommandItem::Undo(count) = self.commands[j] {
                if j - count - 1 < i {
                    i = self.remove_i(j - count - 1, i)
                }
            }
        }
        i
    }
    /// Iterate the sequence of [*realized commands*](Commands#method.iter_realized) from the
    /// newest to the oldest.
    ///
    /// *Realized commands* are commands that are not undone. For example assuming
    /// the folowing sequence of commands:
    ///
    /// | Command | State |
    /// |---------|-------|
    /// | Init    |       |
    /// | Do A    | A     |
    /// | Do B    | A, B  |
    /// | Undo    | A     |
    /// | Do C    | A, C  |
    ///
    ///  The iterator would iterator over the sequence [C, A].
    ///
    /// ```
    /// use undo_2::{Action,Commands};
    ///
    /// #[derive(Debug, Eq, PartialEq)]
    /// enum Command {
    ///     A,
    ///     B,
    ///     C,
    ///     D,
    ///     E,
    /// }
    /// use Command::*;
    ///
    /// let mut commands = Commands::new();
    ///
    /// commands.push(A);
    /// commands.push(B);
    /// commands.push(C);
    /// commands.undo();
    /// commands.undo();
    /// commands.push(D);
    /// commands.push(E);
    ///
    /// let v: Vec<_> = commands.iter_realized().collect();
    /// assert_eq!(v, [&E,&D, &A]);
    /// ```
    pub fn iter_realized(&self) -> IterRealized<'_, T> {
        IterRealized {
            commands: &self.commands,
            current: self.commands.len(),
        }
    }
    /// Merge a sequence of [*realized commands*](Commands#method.iter_realized) into a single new
    /// command or remove the sequence.
    ///
    /// The parameter `f` takes as an input a [IterRealized], and returns a
    /// [`std::ops::ControlFlow<Option<Merge>, Option<Merge>>`](std::ops::ControlFlow). If the
    /// returned value contain a `Some(merge)`[Merge], the action specified by `merge` is then
    /// inserted in place.
    ///
    /// The function is excuted recursively while it returns a `ControlFlow::Continue(_)` with a
    /// [realized iterator](Commands#method.iter_realized) that is advanced by 1 if no merge
    /// command is returned, or set to the element previous to the last merge command.
    ///
    /// The execution stops when the functions either returned `ControlFlow::Break` or after the
    /// last element in the iteration.
    ///
    /// *Remember*: the element are iterated from the newest to the oldest (in reverse order).
    ///
    /// # Example
    ///
    /// ```
    /// use undo_2::{Commands, CommandItem, Merge, IterRealized};
    /// use std::ops::ControlFlow;
    ///
    /// #[derive(Eq, PartialEq, Debug)]
    /// enum Command {
    ///     A,
    ///     B,
    ///     AB,
    /// }
    ///
    /// use Command::*;
    ///
    /// fn is_ab<'a>(mut it: IterRealized<'a, Command>) -> (bool, IterRealized<'a, Command>) {
    ///     let cond = it.next() == Some(&B) && it.next() == Some(&A);
    ///     (cond, it)
    /// }
    ///
    ///
    /// let mut commands = Commands::new();
    /// commands.push(A);
    /// commands.push(B);
    ///
    /// commands.merge(|start| {
    ///     if let (true, end) = is_ab(start.clone()) {
    ///         ControlFlow::Continue(Some(Merge {
    ///             start,
    ///             end,
    ///             command: Some(AB),
    ///         }))
    ///     } else {
    ///         ControlFlow::Continue(None)
    ///     }
    /// });
    ///
    /// assert_eq!(&*commands, &[AB.into()]);
    /// ```
    pub fn merge<F>(&mut self, mut f: F)
    where
        for<'a> F:
            FnMut(IterRealized<'a, T>) -> ControlFlow<Option<Merge<'a, T>>, Option<Merge<'a, T>>>,
    {
        use ControlFlow::*;
        self.splice(|it| match f(it) {
            Continue(c) => Continue(c.map(|m| m.into())),
            Break(c) => Break(c.map(|m| m.into())),
        })
    }

    /// Replace a sequence of command by an other. This is a generalization of
    /// [Commands::merge](Commands#method.merge)
    ///
    /// The parameter `f` takes as an input a [IterRealized], and returns a
    /// [`std::ops::ControlFlow<Option<Splice>, Option<Splice>>`](std::ops::ControlFlow). If the returned value
    /// contain a `Some(splice)`[Splice], the actions specified by `splice` are then inserted in
    /// place.
    ///
    /// The function is excuted recursively while it returns a `ControlFlow::Continue(_)` with a
    /// [realized iterator](Commands#method.iter_realized) that is advanced by 1 if no merge
    /// command is returned, or set to the element previous to the last merge command.
    ///
    /// The execution stops when the functions either returned `ControlFlow::Break` or after the
    /// last element in the iteration.
    ///
    /// *Remember*: the element are iterated from the newest to the oldest (in reverse order).
    ///
    /// # Example
    ///
    /// ```
    /// use undo_2::{Commands, CommandItem, Splice, IterRealized};
    /// use std::ops::ControlFlow;
    ///
    /// // we suppose that A, B, C is equivalent to D,E
    /// #[derive(Eq, PartialEq, Debug)]
    /// enum Command {
    ///     A,
    ///     B,
    ///     C,
    ///     D,
    ///     E,
    /// }
    ///
    /// use Command::*;
    ///
    /// fn is_abc<'a>(mut it: IterRealized<'a, Command>) -> (bool, IterRealized<'a, Command>) {
    ///     let cond = it.next() == Some(&C) && it.next() == Some(&B) && it.next() == Some(&A);
    ///     (cond, it)
    /// }
    ///
    ///
    /// let mut commands = Commands::new();
    /// commands.push(A);
    /// commands.push(B);
    /// commands.push(C);
    ///
    /// commands.splice(|start| {
    ///     if let (true, end) = is_abc(start.clone()) {
    ///         ControlFlow::Continue(Some(Splice {
    ///             start,
    ///             end,
    ///             commands: [D,E],
    ///         }))
    ///     } else {
    ///         ControlFlow::Continue(None)
    ///     }
    /// });
    ///
    /// assert_eq!(&*commands, &[D.into(), E.into()]);
    /// ```
    pub fn splice<F, I>(&mut self, mut f: F)
    where
        F: for<'a> FnMut(
            IterRealized<'a, T>,
        )
            -> ControlFlow<Option<Splice<'a, T, I>>, Option<Splice<'a, T, I>>>,
        I: IntoIterator<Item = T>,
    {
        use ControlFlow::*;
        let mut start = self.commands.len();
        while start != 0 {
            let it = IterRealized {
                commands: &self.commands,
                current: start,
            };
            match f(it) {
                Continue(Some(m)) => {
                    let rev_start = m.start.current;
                    let rev_end = m.end.current;
                    let commands = m.commands;
                    self.do_splice(rev_start, rev_end, commands);
                    start = rev_end;
                }
                Break(Some(m)) => {
                    let rev_start = m.start.current;
                    let rev_end = m.end.current;
                    let commands = m.commands;
                    self.do_splice(rev_start, rev_end, commands);
                    break;
                }
                Break(None) => break,
                Continue(None) => start -= 1,
            }
        }
    }
    fn do_splice<I>(&mut self, rev_start: usize, rev_end: usize, commands: I)
    where
        I: IntoIterator<Item = T>,
    {
        let end_i = rev_start;
        let start_i = rev_end;
        self.commands
            .splice(start_i..end_i, commands.into_iter().map(|c| c.into()));
    }

    /// Clean up the history of all the undone commands.
    ///
    /// After this call the sequence of command will not contain
    /// any `CommandItem::Undo`
    ///
    /// # Example
    /// ```
    /// use undo_2::{CommandItem, Commands};
    ///
    /// #[derive(Debug, PartialEq)]
    /// enum Command {
    ///     A,
    ///     B,
    ///     C,
    /// }
    /// use Command::*;
    /// let mut c = Commands::default();
    ///
    /// c.push(A);
    /// c.push(B);
    /// c.undo();
    /// c.push(C);
    /// assert_eq!(*c, [A.into(), B.into(), CommandItem::Undo(0), C.into()]);
    ///
    /// c.remove_all_undone();
    /// assert_eq!(*c, [A.into(), C.into()]);
    /// ```
    pub fn remove_all_undone(&mut self) {
        self.remove_undone(|i| i)
    }
    /// Clean up the history of all undone commands before a given
    /// [realized iterator](Commands#method.iter_realized).
    ///
    /// # Example
    /// ```
    /// use undo_2::{Commands,CommandItem};
    ///
    /// #[derive(Debug, PartialEq)]
    /// enum Command {
    ///     A,
    ///     B,
    ///     C,
    ///     D,
    /// }
    /// use Command::*;
    /// let mut c = Commands::default();
    ///
    /// c.push(A);
    /// c.push(B);
    /// c.undo();
    /// c.push(C);
    /// c.push(C);
    /// c.undo();
    /// c.push(D);
    /// assert_eq!(
    ///     *c,
    ///     [
    ///         A.into(),
    ///         B.into(),
    ///         CommandItem::Undo(0),
    ///         C.into(),
    ///         C.into(),
    ///         CommandItem::Undo(0),
    ///         D.into()
    ///     ]
    /// );
    ///
    /// let v: Vec<_> = c.iter_realized().collect();
    /// assert_eq!(*v, [&D, &C, &A]);
    ///
    /// c.remove_undone(|mut it| {
    ///     it.nth(1);
    ///     it
    /// });
    /// assert_eq!(
    ///     *c,
    ///     [A.into(), C.into(), C.into(), CommandItem::Undo(0), D.into()]
    /// );
    ///
    /// // This operation does not change the sequence of realized commands:
    /// let v: Vec<_> = c.iter_realized().collect();
    /// assert_eq!(*v, [&D, &C, &A]);
    /// ```
    pub fn remove_undone<F>(&mut self, from: F)
    where
        F: for<'a> FnOnce(IterRealized<'a, T>) -> IterRealized<'a, T>,
    {
        let from = from(self.iter_realized());

        let mut it = IterRealized {
            commands: &self.commands,
            ..from
        };

        self.undo_cache.clear();

        let start = it.current;
        while let Some(_) = it.next() {
            self.undo_cache.push(Action::Do(it.current));
        }

        cfg_if! {
            if #[cfg(RUSTC_IS_NIGTHLY)] {
                let mut index = 0;
                let mut it = self.undo_cache.iter().rev();
                let mut keep = it.next();
                self.commands.drain_filter(|_| {
                    let cond = match keep {
                        Some(a) => {
                            let cond = match a {
                                Action::Do(i) | Action::Undo(i) => index != *i,
                            };
                            if !cond {
                                keep = it.next();
                            }
                            cond
                        },
                        None => index < start,
                    };
                    index += 1;
                    cond
                });
            } else {
                let mut i = 0;
                let mut shift = 0;
                for u in self.undo_cache.iter().rev() {
                    match *u {
                        Action::Do(j) | Action::Undo(j) => {
                            self.commands.drain(i-shift..j-shift);
                            shift += j-i;
                            i = j + 1;
                        }
                    }
                }
                self.commands.drain(i-shift..start-shift);
            }
        }
    }
}

impl<T> Deref for Commands<T> {
    type Target = [CommandItem<T>];
    fn deref(&self) -> &Self::Target {
        &self.commands
    }
}
impl<T> AsRef<[CommandItem<T>]> for Commands<T> {
    fn as_ref(&self) -> &[CommandItem<T>] {
        self
    }
}
impl<T> Borrow<[CommandItem<T>]> for Commands<T> {
    fn borrow(&self) -> &[CommandItem<T>] {
        self
    }
}
impl<T> Extend<T> for Commands<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.commands.extend(iter.into_iter().map(|c| c.into()))
    }
}
impl<T> FromIterator<T> for Commands<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self {
            commands: iter.into_iter().map(|c| c.into()).collect(),
            undo_cache: vec![],
        }
    }
}
impl<'a, T> IntoIterator for &'a Commands<T> {
    type Item = &'a CommandItem<T>;
    type IntoIter = slice::Iter<'a, CommandItem<T>>;
    fn into_iter(self) -> Self::IntoIter {
        self.commands.iter()
    }
}
impl<T> IntoIterator for Commands<T> {
    type Item = CommandItem<T>;
    type IntoIter = std::vec::IntoIter<CommandItem<T>>;
    fn into_iter(self) -> Self::IntoIter {
        self.commands.into_iter()
    }
}
impl<T, I> Index<I> for Commands<T>
where
    I: SliceIndex<[CommandItem<T>]>,
{
    type Output = <I as SliceIndex<[CommandItem<T>]>>::Output;
    fn index(&self, index: I) -> &Self::Output {
        self.commands.index(index)
    }
}

impl<T> Action<T> {
    /// Map an `Action<T>` to an `Action<U>.`
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Action<U> {
        use Action::*;
        match self {
            Do(v) => Do(f(v)),
            Undo(v) => Undo(f(v)),
        }
    }
    /// Map `&Action<T>` to an `Action<&T>.`
    pub fn as_ref(&self) -> Action<&'_ T> {
        use Action::*;
        match self {
            Do(v) => Do(v),
            Undo(v) => Undo(v),
        }
    }
    /// Map `&mut Action<T>` to an `Action<&mut T>.`
    pub fn as_mut(&mut self) -> Action<&'_ mut T> {
        use Action::*;
        match self {
            Do(v) => Do(v),
            Undo(v) => Undo(v),
        }
    }
}

impl<T> Action<&T> {
    /// Map `Action<&T>` to an `Action<T>` by coping the content.
    pub fn copied(self) -> Action<T>
    where
        T: Copy,
    {
        self.map(|v| *v)
    }
    /// Map `Action<&T>` to an `Action<T>` by cloning the content.
    pub fn cloned(self) -> Action<T>
    where
        T: Clone,
    {
        self.map(|v| v.clone())
    }
}
impl<T> Action<&mut T> {
    /// Map `Action<&mut T>` to an `Action<T>` by coping the content.
    pub fn copied(self) -> Action<T>
    where
        T: Copy,
    {
        self.map(|v| *v)
    }
    /// Map `Action<&mut T>` to an `Action<T>` by cloning the content.
    pub fn cloned(self) -> Action<T>
    where
        T: Clone,
    {
        self.map(|v| v.clone())
    }
}

impl<T> From<T> for CommandItem<T> {
    fn from(value: T) -> Self {
        CommandItem::Command(value)
    }
}

impl<'a, T> From<Merge<'a, T>> for Splice<'a, T, option::IntoIter<T>> {
    fn from(m: Merge<'a, T>) -> Self {
        Splice {
            start: m.start,
            end: m.end,
            commands: m.command.into_iter(),
        }
    }
}

impl<'a, T> Iterator for IterRealized<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        use CommandItem::*;
        loop {
            self.current = self.current.checked_sub(1)?;
            match self.commands[self.current] {
                Command(ref c) => break Some(c),
                Undo(i) => self.current -= i + 1,
            }
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.current))
    }
}
impl<'a, T> FusedIterator for IterRealized<'a, T> {}

impl<'a, T> Iterator for ActionIter<'a, T> {
    type Item = Action<&'a T>;
    fn next(&mut self) -> Option<Self::Item> {
        self.to_do.next().map(|c| match c {
            Action::Do(j) => {
                if let CommandItem::Command(v) = &self.commands[*j] {
                    Action::Do(v)
                } else {
                    unreachable!()
                }
            }
            Action::Undo(j) => {
                if let CommandItem::Command(v) = &self.commands[*j] {
                    Action::Undo(v)
                } else {
                    unreachable!()
                }
            }
        })
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.to_do.size_hint()
    }
}
impl<'a, T> FusedIterator for ActionIter<'a, T> {}
impl<'a, T> ExactSizeIterator for ActionIter<'a, T> {}

impl<T: PartialEq + Eq> Action<T> {
    fn is_reverse_of(&self, other: &Self) -> bool {
        use Action::*;
        match self {
            Do(i) => matches!(other, Undo(j) if i == j),
            Undo(i) => matches!(other, Do(j) if i == j),
        }
    }
}

impl<'a, T> ActionIter<'a, T> {
    fn new() -> Self {
        Self {
            commands: &[],
            to_do: [].iter(),
        }
    }
    fn undo_at_count(
        commands: &'a [CommandItem<T>],
        cache: &'a mut Vec<Action<usize>>,
        i: usize,
        count: usize,
    ) -> Self {
        cache.clear();
        cache_undo_indexes(commands, i + 1 + count, i, cache);
        do_simplify(cache);
        Self {
            commands,
            to_do: cache.iter(),
        }
    }
    fn do_at_count(
        commands: &'a [CommandItem<T>],
        cache: &'a mut Vec<Action<usize>>,
        i: usize,
        count: usize,
    ) -> Self {
        cache.clear();
        cache_do_indexes(commands, i - count, i + 1, cache);
        do_simplify(cache);
        Self {
            commands,
            to_do: cache.iter(),
        }
    }
}
fn cache_undo_indexes<T>(
    commands: &[CommandItem<T>],
    undo_from: usize,
    undo_to: usize,
    to_do: &mut Vec<Action<usize>>,
) {
    for i in (undo_to..undo_from).into_iter().rev() {
        match commands[i] {
            CommandItem::Command(_) => to_do.push(Action::Undo(i)),
            CommandItem::Undo(count) => cache_do_indexes(commands, i - (count + 1), i, to_do),
        }
    }
}
fn cache_do_indexes<T>(
    commands: &[CommandItem<T>],
    do_from: usize,
    do_to: usize,
    to_do: &mut Vec<Action<usize>>,
) {
    for i in do_from..do_to {
        match commands[i] {
            CommandItem::Command(_) => to_do.push(Action::Do(i)),
            CommandItem::Undo(count) => cache_undo_indexes(commands, i, i - (count + 1), to_do),
        }
    }
}
fn do_simplify(to_do: &mut Vec<Action<usize>>) {
    if to_do.len() < 2 {
        return;
    }
    let mut analyzed = to_do.len() - 1;
    let mut cursor = to_do.len() - 1;
    while analyzed > 0 {
        analyzed -= 1;
        let action = &to_do[analyzed];
        if cursor < to_do.len() {
            if to_do[cursor].is_reverse_of(action) {
                cursor += 1;
            } else {
                to_do.drain(analyzed + 1..cursor);
                if cursor == analyzed + 1 {
                    cursor = analyzed
                } else {
                    cursor = analyzed + 1;
                    analyzed += 1;
                }
            }
        } else {
            to_do.drain(analyzed + 1..);
            cursor = analyzed;
        }
    }
    to_do.drain(..cursor);
}

#[cfg(test)]
mod test {
    use super::Action;
    use super::Action::*;
    #[test]
    fn simplify() {
        use super::do_simplify;
        fn simplify(mut to_do: Vec<Action<usize>>) -> Vec<Action<usize>> {
            do_simplify(&mut to_do);
            to_do
        }
        {
            let v = vec![];
            assert_eq!(simplify(v), vec![]);
        }
        {
            let v = vec![Do(1)];
            assert_eq!(simplify(v), vec![Do(1)]);
        }
        {
            let v = vec![Undo(1)];
            assert_eq!(simplify(v), vec![Undo(1)]);
        }
        {
            let v = vec![Do(1), Undo(1)];
            assert_eq!(simplify(v), vec![]);
        }
        {
            let v = vec![Do(0), Do(1), Undo(1)];
            assert_eq!(simplify(v), vec![Do(0)]);
        }
        {
            let v = vec![Do(1), Undo(1), Do(2)];
            assert_eq!(simplify(v), vec![Do(2)]);
        }
        {
            let v = vec![Do(0), Do(1), Undo(1), Do(2)];
            assert_eq!(simplify(v), vec![Do(0), Do(2)]);
        }
        {
            let v = vec![Do(1), Do(2), Undo(2), Undo(1)];
            assert_eq!(simplify(v), vec![]);
        }
        {
            let v = vec![Do(0), Do(1), Do(2), Undo(2), Undo(1)];
            assert_eq!(simplify(v), vec![Do(0)]);
        }
        {
            let v = vec![Do(1), Do(2), Undo(2), Undo(1), Do(3)];
            assert_eq!(simplify(v), vec![Do(3)]);
        }
        {
            let v = vec![Do(0), Do(1), Do(2), Undo(2), Undo(1), Do(3)];
            assert_eq!(simplify(v), vec![Do(0), Do(3)]);
        }
        {
            let v = vec![Do(0), Do(1), Do(2), Undo(2), Undo(1), Undo(0)];
            assert_eq!(simplify(v), vec![]);
        }
        {
            let v = vec![
                Do(0),
                Do(1),
                Do(2),
                Undo(2),
                Undo(1),
                Do(10),
                Undo(10),
                Undo(0),
            ];
            assert_eq!(simplify(v), vec![]);
        }
    }
}
