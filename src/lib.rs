#! [doc = include_str!("../README.md")]
use core::borrow::Borrow;
use core::iter::FusedIterator;
use core::ops::ControlFlow;
use core::ops::{Deref, Index};
use core::option;
use derivative::Derivative;
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
    /// Execute the action described by the inner parameter
    Do(T),
    /// Execute inverse of the action described by the inner parameter
    Undo(T),
}

/// Store the list of commads executed by the user.
///
/// Commands are added by invoking [`push`](#method.push) method. [`undo`](#method.undo) and [`redo`](#method.redo) return a list
/// of [`Action<T>`] that the application must execute.
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
///
/// let mut commands = Commands::new();
///
/// commands.push(Command::A);
/// commands.push(Command::B);
///
/// let v: Vec<_> = commands.undo().collect();
/// assert_eq!(v, [Action::Undo(&Command::B)]);
///
/// let v: Vec<_> = commands.undo().collect();
/// assert_eq!(v, [Action::Undo(&Command::A)]);
///
/// commands.push(Command::A);
///
/// let v: Vec<_> = commands.undo().collect();
/// assert_eq!(v, [Action::Undo(&Command::A)]);
///
/// // undo the first 2 undos
/// let v: Vec<_> = commands.undo().collect();
/// assert_eq!(v, [Action::Do(&Command::A), Action::Do(&Command::B)]);
/// ```
///
/// # Representation
///
/// `Commands` owns a slice of [CommandItem] that is accesible
/// by dereferencing the command.
///
/// It also
#[derive(Clone, Default, Derivative)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derivative(Debug, PartialEq, Eq, Hash)]
pub struct Commands<T> {
    commands: Vec<CommandItem<T>>,
    #[derivative(Debug = "ignore", PartialEq = "ignore", Hash = "ignore")]
    #[cfg_attr(feature = "serde", serde(skip))]
    undo_cache: Vec<Action<usize>>,
}

/// Specify a merge when calling [Commands::merge](Commands#method.merge)
///
/// The `start` and `end` parameters specifies the slice of command the will
/// be removed during the merge. But note that [IterRealized] iterate from the newest
/// to the oldest command, so the slice is reversed.
///
/// The `start` member designate passed the end of the slice, `end` is the beginning
/// of the slice. If `command` is `None` then the slice will be removed, otherwise if
/// the `command` is `Some(c)` the slice will be replace by `c`.
#[derive(Debug)]
pub struct Merge<'a, T> {
    pub start: IterRealized<'a, T>,
    pub end: IterRealized<'a, T>,
    pub command: Option<T>,
}

/// Specify a splice when calling [Commands::splice](Commands#method.splice)
///
/// The `start` and `end` parameters specifies the slice of command the will
/// be removed during the splice. But note that [IterRealized] iterate from the newest
/// to the oldest command, so the slice is reversed.
///
/// The `start` member designate passed the end of the slice, `end` is the beginning
/// of the slice. The removed slice is then replaced by the sequence of
/// commands denoted by `commands`.
#[derive(Debug)]
pub struct Splice<'a, T, I: IntoIterator<Item = T>> {
    pub start: IterRealized<'a, T>,
    pub end: IterRealized<'a, T>,
    pub commands: I,
}

#[derive(Derivative, Debug)]
#[derivative(Clone(bound = "It:Clone"))]
/// Iterator of actions returned by [Commands::undo](Commands#method.undo) and [Commands::redo](Commands#method.redo)
pub struct ActionIter<'a, T, It> {
    commands: &'a [CommandItem<T>],
    to_do: It,
}
/// Iterator of actions returned by [Commands::push](Commands#method.undo)
pub type UndoIter<'a, T> = ActionIter<'a, T, std::iter::Rev<std::slice::Iter<'a, Action<usize>>>>;
/// Iterator of actions returned by [Commands::push](Commands#method.redo)
pub type RedoIter<'a, T> = ActionIter<'a, T, std::slice::Iter<'a, Action<usize>>>;

/// The items store in [Commands].
///
/// The list of CommandItem is accessible by dereferencing
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
    Command(T),
    Undo(usize),
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
    ///
    /// let mut commands = Commands::new();
    ///
    /// commands.push(Command::A);
    ///
    /// let v: Vec<_> = commands.iter_realized().collect();
    /// assert_eq!(v, [&Command::A]);
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
    /// }
    ///
    /// let mut commands = Commands::new();
    ///
    /// commands.push(Command::A);
    /// commands.push(Command::B);
    /// let v: Vec<_> = commands.undo().collect();
    ///
    /// assert_eq!(v, [Action::Undo(&Command::B)]);
    /// ```
    #[must_use = "the returned undo command should be realized"]
    pub fn undo(&mut self) -> UndoIter<'_, T> {
        let l = self.len();
        match self.commands.last_mut() {
            None => UndoIter::new(),
            Some(CommandItem::Undo(i)) => {
                if *i + 2 < l {
                    *i += 1;
                    let t = l - *i - 2;
                    ActionIter::undo_at(&self.commands, &mut self.undo_cache, t)
                } else {
                    UndoIter::new()
                }
            }
            Some(CommandItem::Command(_)) => {
                self.commands.push(CommandItem::Undo(0));
                ActionIter::undo_at(&self.commands, &mut self.undo_cache, l - 1)
            }
        }
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
    ///
    /// let mut commands = Commands::new();
    ///
    /// commands.push(Command::A);
    /// commands.push(Command::B);
    /// commands.undo();
    /// let v: Vec<_> = commands.redo().collect();
    ///
    /// assert_eq!(v, [Action::Do(&Command::B)]);
    /// ```
    #[must_use = "the returned undo command should be realized"]
    pub fn redo(&mut self) -> RedoIter<'_, T> {
        let l = self.len();
        match self.commands.last_mut() {
            Some(CommandItem::Undo(i)) => {
                if let Some(ni) = i.checked_sub(1) {
                    let t = l - 2 - *i;
                    *i = ni;
                    ActionIter::do_at(&self.commands, &mut self.undo_cache, t)
                } else {
                    self.commands.pop();
                    ActionIter::do_at(
                        &self.commands,
                        &mut self.undo_cache,
                        self.commands.len() - 1,
                    )
                }
            }
            _ => RedoIter::new(),
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
    ///
    /// let mut commands = Commands::new();
    /// assert!(!commands.is_undoing());
    ///
    /// commands.push(Command::A);
    /// assert!(!commands.is_undoing());
    ///
    /// commands.undo();
    /// assert!(commands.is_undoing());
    ///
    /// commands.push(Command::A);
    /// commands.push(Command::A);
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
    ///
    /// let mut commands = Commands::new();
    ///
    /// commands.push(Command::A);
    /// commands.push(Command::B);
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
    ///
    /// let mut commands = Commands::new();
    ///
    /// let t0 = Instant::now();
    /// let t1 = t0 + Duration::from_secs(1);
    /// let t2 = t0 + Duration::from_secs(2);
    /// let t3 = t0 + Duration::from_secs(3);
    /// let t4 = t0 + Duration::from_secs(4);
    /// commands.push((t0,Command::A));
    /// commands.push((t1,Command::B));
    /// commands.push((t2,Command::C));
    /// commands.push((t3,Command::D));
    /// commands.push((t4,Command::E));
    ///
    /// commands.remove_until(|(t, _)| *t > t1);
    ///
    /// let v: Vec<_> = commands.iter_realized().collect();
    /// assert_eq!(v, [&(t4,Command::E),&(t3,Command::D), &(t2,Command::C)]);
    ///
    ///
    /// let mut commands = Commands::new();
    ///
    /// commands.push((t0,Command::A));
    /// commands.push((t1,Command::B)); //B
    /// commands.push((t2,Command::C));
    /// commands.undo();
    /// commands.undo();// undo covering B
    /// commands.push((t3,Command::D));
    /// commands.push((t4,Command::E));
    ///
    /// commands.remove_until(|(t, _)| *t > t1);
    ///
    /// commands.undo();//remove E
    /// commands.undo();//remove D
    /// commands.undo();//undo the 2 undos
    ///
    /// // B not removed because it is covered by an undo
    /// let v: Vec<_> = commands.iter_realized().collect();
    /// assert_eq!(v, [&(t2,Command::C),&(t1,Command::B)]);
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
    ///
    /// let mut commands = Commands::new();
    ///
    /// let t0 = Instant::now();
    /// let t1 = t0 + Duration::from_secs(1);
    /// let t2 = t0 + Duration::from_secs(2);
    /// let t3 = t0 + Duration::from_secs(3);
    /// let t4 = t0 + Duration::from_secs(4);
    /// commands.push((t0,Command::A));
    /// commands.push((t1,Command::B));
    /// commands.push((t2,Command::C));
    /// commands.push((t3,Command::D));
    /// commands.push((t4,Command::E));
    ///
    /// commands.keep_last(2);
    ///
    /// let v: Vec<_> = commands.iter_realized().collect();
    /// assert_eq!(v, [&(t4,Command::E),&(t3,Command::D)]);
    ///
    ///
    /// let mut commands = Commands::new();
    ///
    /// commands.push((t0,Command::A));
    /// commands.push((t1,Command::B)); //B
    /// commands.push((t2,Command::C));
    /// commands.undo();
    /// commands.undo();// undo covering B
    /// commands.push((t3,Command::D));
    /// commands.push((t4,Command::E));
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
    /// assert_eq!(v, [&(t2,Command::C),&(t1,Command::B)]);
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
    ///
    /// let mut commands = Commands::new();
    ///
    /// let t0 = Instant::now();
    /// let t1 = t0 + Duration::from_secs(1);
    /// let t2 = t0 + Duration::from_secs(2);
    /// let t3 = t0 + Duration::from_secs(3);
    /// let t4 = t0 + Duration::from_secs(4);
    /// commands.push((t0,Command::A));
    /// commands.push((t1,Command::B));
    /// commands.push((t2,Command::C));
    /// commands.push((t3,Command::D));
    /// commands.push((t4,Command::E));
    ///
    /// commands.remove_first(3);
    ///
    /// let v: Vec<_> = commands.iter_realized().collect();
    /// assert_eq!(v, [&(t4,Command::E),&(t3,Command::D)]);
    ///
    ///
    /// let mut commands = Commands::new();
    ///
    /// commands.push((t0,Command::A));
    /// commands.push((t1,Command::B)); //B
    /// commands.push((t2,Command::C));
    /// commands.undo();
    /// commands.undo();// undo covering B
    /// commands.push((t3,Command::D));
    /// commands.push((t4,Command::E));
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
    /// assert_eq!(v, [&(t2,Command::C),&(t1,Command::B)]);
    /// ```
    pub fn remove_first(&mut self, i: usize) {
        let j = self.remove_i(i, self.commands.len());
        self.commands.drain(..j);
    }
    fn remove_i(&self, mut i: usize, end: usize) -> usize {
        for j in i..end {
            if let CommandItem::Undo(count) = self.commands[j] {
                if j - count - 1 < i {
                    i = self.remove_i(j - count - 1, i)
                }
            }
        }
        i
    }
    /// Iterate the sequence of *realized commands* from the newest to the oldest.
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
    ///
    /// let mut commands = Commands::new();
    ///
    /// commands.push(Command::A);
    /// commands.push(Command::B);
    /// commands.push(Command::C);
    /// commands.undo();
    /// commands.undo();
    /// commands.push(Command::D);
    /// commands.push(Command::E);
    ///
    /// let v: Vec<_> = commands.iter_realized().collect();
    /// assert_eq!(v, [&Command::E,&Command::D, &Command::A]);
    /// ```
    pub fn iter_realized(&self) -> IterRealized<'_, T> {
        IterRealized {
            commands: &self.commands,
            current: self.commands.len(),
        }
    }
    /// Merge a sequence of realized commands into a single new command or remove the sequence.
    ///
    /// The parameter `f` takes as an input a [IterRealized], and returns a
    /// [`std::ops::ControlFlow<Option<Merge>, Option<Merge>>`](std::ops::ControlFlow). If the returned value
    /// contain a `Some(merge)`[Merge], the action specified by `merge` is then realized.
    ///
    /// The function is excuted recursively while it returns a `ControlFlow::Continue(_)` with a
    /// realized iterator that is advanced by 1 if no merge command is returned, or set to the
    /// element previous to the last merge command.
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
    /// contain a `Some(splice)`[Splice], the action specified by `splice` is then realized.
    ///
    /// The function is excuted recursively while it returns a `ControlFlow::Continue(_)` with a
    /// realized iterator that is advanced by 1 if no merge command is returned, or set to the
    /// element previous to the last merge command.
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
    /// commands.merge(|start| {
    ///     if let (true, end) = is_ab(start.clone()) {
    ///         ControlFlow::Continue(Some(Splice {
    ///             start,
    ///             end,
    ///             command: [D,E],
    ///         }))
    ///     } else {
    ///         ControlFlow::Continue(None)
    ///     }
    /// });
    ///
    /// assert_eq!(&*commands, &[D.into(), E.into()]);
    /// ```
    pub fn splice<F, I, J>(&mut self, mut f: F)
    where
        F: for<'a> FnMut(
            IterRealized<'a, T>,
        )
            -> ControlFlow<Option<Splice<'a, T, I>>, Option<Splice<'a, T, J>>>,
        I: IntoIterator<Item = T>,
        J: IntoIterator<Item = T>,
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
    pub fn do_splice<I>(&mut self, rev_start: usize, rev_end: usize, commands: I)
    where
        I: IntoIterator<Item = T>,
    {
        let end_i = rev_start;
        let start_i = rev_end;
        self.commands
            .splice(start_i..end_i, commands.into_iter().map(|c| c.into()));
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
impl<'a, T> IntoIterator for Commands<T> {
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
        T: Copy,
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
        T: Copy,
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
}
impl<'a, T> FusedIterator for IterRealized<'a, T> {}

impl<'a, T, It: Iterator<Item = &'a Action<usize>>> Iterator for ActionIter<'a, T, It> {
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
}
impl<'a, T, It: Iterator<Item = &'a Action<usize>>> FusedIterator for ActionIter<'a, T, It> {}

impl<T: PartialEq + Eq> Action<T> {
    fn is_reverse_of(&self, other: &Self) -> bool {
        use Action::*;
        match self {
            Do(i) => match other {
                Undo(j) if i == j => true,
                _ => false,
            },
            Undo(i) => match other {
                Do(j) if i == j => true,
                _ => false,
            },
        }
    }
}

impl<'a, T> UndoIter<'a, T> {
    fn new() -> Self {
        Self {
            commands: &[],
            to_do: [].iter().rev(),
        }
    }
    fn undo_at(
        commands: &'a [CommandItem<T>],
        cache: &'a mut Vec<Action<usize>>,
        i: usize,
    ) -> Self {
        cache.clear();
        new_undo(commands, i + 1, i, cache);
        do_simplify(cache);
        Self {
            commands,
            to_do: cache.iter().rev(),
        }
    }
}

impl<'a, T> RedoIter<'a, T> {
    fn new() -> Self {
        Self {
            commands: &[],
            to_do: [].iter(),
        }
    }
    fn do_at(commands: &'a [CommandItem<T>], cache: &'a mut Vec<Action<usize>>, i: usize) -> Self {
        cache.clear();
        new_do(commands, i, i + 1, cache);
        do_simplify(cache);
        Self {
            commands,
            to_do: cache.iter(),
        }
    }
}
fn new_undo<T>(
    commands: &[CommandItem<T>],
    undo_from: usize,
    undo_to: usize,
    to_do: &mut Vec<Action<usize>>,
) {
    for i in (undo_to..undo_from).into_iter().rev() {
        match commands[i] {
            CommandItem::Command(_) => to_do.push(Action::Undo(i)),
            CommandItem::Undo(count) => new_do(commands, i - (count + 1), i, to_do),
        }
    }
}
fn new_do<T>(
    commands: &[CommandItem<T>],
    do_from: usize,
    do_to: usize,
    to_do: &mut Vec<Action<usize>>,
) {
    for i in (do_from..do_to).into_iter().rev() {
        match commands[i] {
            CommandItem::Command(_) => to_do.push(Action::Do(i)),
            CommandItem::Undo(count) => new_undo(commands, i, i - (count + 1), to_do),
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
                    analyzed = analyzed + 1;
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
