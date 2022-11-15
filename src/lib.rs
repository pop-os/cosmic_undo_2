#! [doc = include_str!("../README.md")]
use core::iter::FusedIterator;
use core::ops::ControlFlow;
use core::ops::Deref;
use core::slice;
use derivative::Derivative;

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
#[derive(Default, Derivative)]
#[derivative(Debug)]
pub struct Commands<T> {
    commands: Vec<CommandItem<T>>,
    #[derivative(Debug = "ignore")]
    undo_cache: Vec<Action<usize>>,
}

/// Specify a merge when calling [Commands::merge](Commands#method.merge)
///
/// The `start` and `end` parameters specifies the slice of command the will
/// be removed during the merge. But note that [RealizedIter] iterate from the newest
/// to the oldest command, so the slice is reversed.
///
/// The `start` member designate passed the end of the slice, `end` is the beginning
/// of the slice. If `command` is `None` then the slice will be removed, otherwise if
/// the `command` is `Some(c)` the slice will be replace by `c`.
#[derive(Debug)]
pub struct Merge<'a, T> {
    pub start: RealizedIter<'a, T>,
    pub end: RealizedIter<'a, T>,
    pub command: Option<T>,
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

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
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
pub enum CommandItem<T> {
    Command(T),
    Undo(usize),
}

#[derive(Derivative, Debug)]
#[derivative(Clone(bound = ""))]
pub struct RealizedIter<'a, T> {
    commands: &'a [CommandItem<T>],
    current: usize,
}

pub type Iter<'a, T> = slice::Iter<'a, CommandItem<T>>;

impl<T> Commands<T> {
    /// Create a new empty command sequence of type `T`.
    pub fn new() -> Self {
        Self {
            commands: vec![],
            undo_cache: vec![],
        }
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
    /// let v: Vec<_> = commands.iter_back().collect();
    /// assert_eq!(v, [&Command::A]);
    /// ```
    pub fn push(&mut self, command: T) {
        self.commands.push(CommandItem::Command(command));
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
    /// let v: Vec<_> = commands.iter_back().collect();
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
    /// let v: Vec<_> = commands.iter_back().collect();
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
    /// let v: Vec<_> = commands.iter_back().collect();
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
    /// let v: Vec<_> = commands.iter_back().collect();
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
    /// let v: Vec<_> = commands.iter_back().collect();
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
    /// let v: Vec<_> = commands.iter_back().collect();
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
    /// let v: Vec<_> = commands.iter_back().collect();
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
    ///  | Command | State |
    ///  |---------|-------|
    ///  | Init    |       |
    ///  | Do A    | A     |
    ///  | Do B    | A, B  |
    ///  | Undo    | A     |
    ///  | Do C    | A, C  |
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
    /// let v: Vec<_> = commands.iter_back().collect();
    /// assert_eq!(v, [&Command::E,&Command::D, &Command::A]);
    /// ```
    pub fn iter_back(&self) -> RealizedIter<'_, T> {
        RealizedIter {
            commands: &self.commands,
            current: self.commands.len(),
        }
    }
    /// Merge a sequence of realized commands into a single new command or remove the sequence.
    ///
    /// The parameter `f` takes as an input a [RealizedIterator], and returns a
    /// [std::ops::ControlFlow<Option<Merge>>, Option<Merge>>]. If returned value
    /// contain a [Merge], the action specified by merge is then realized.
    ///
    /// The function is excuted recursively while it returns a `ControlFlow::Continue(_)` with a
    /// realized iterator that is decremented by 1 if no merge command is returned, or set to the
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
    /// use undo_2::{Commands, CommandItem, Merge, RealizedIter};
    /// use std::ops::ControlFlow;
    ///
    /// #[derive(Eq, PartialEq, Debug)]
    /// enum Command {
    ///     A,
    ///     B,
    ///     AB,
    /// }
    /// use Command::*;
    /// fn is_ab<'a>(mut it: RealizedIter<'a, Command>) -> (bool, RealizedIter<'a, Command>) {
    ///     let cond = it.next() == Some(&Command::B) && it.next() == Some(&Command::A);
    ///     (cond, it)
    /// }
    /// {
    ///     let mut commands = Commands::new();
    ///     commands.push(Command::A);
    ///     commands.push(Command::B);
    ///
    ///     commands.merge(|start| {
    ///         if let (true, end) = is_ab(start.clone()) {
    ///             println!("merge");
    ///             ControlFlow::Continue(Some(Merge {
    ///                 start,
    ///                 end,
    ///                 command: Some(Command::AB),
    ///             }))
    ///         } else {
    ///             ControlFlow::Continue(None)
    ///         }
    ///     });
    ///     assert_eq!(&*commands, &[AB.into()]);
    /// }
    /// ```
    pub fn merge<F>(&mut self, mut f: F)
    where
        for<'a> F:
            FnMut(RealizedIter<'a, T>) -> ControlFlow<Option<Merge<'a, T>>, Option<Merge<'a, T>>>,
    {
        use ControlFlow::*;
        let mut start = self.commands.len();
        while start != 0 {
            let it = RealizedIter {
                commands: &self.commands,
                current: start,
            };
            match f(it) {
                Continue(Some(m)) => {
                    let rev_start = m.start.current;
                    let rev_end = m.end.current;
                    let command = m.command;
                    self.do_merge(rev_start, rev_end, command);
                    start = rev_end;
                }
                Break(Some(m)) => {
                    let rev_start = m.start.current;
                    let rev_end = m.end.current;
                    let command = m.command;
                    self.do_merge(rev_start, rev_end, command);
                    break;
                }
                Break(None) => break,
                Continue(None) => start -= 1,
            }
        }
    }
    pub fn do_merge(&mut self, rev_start: usize, rev_end: usize, command: Option<T>) {
        let end_i = rev_start;
        let start_i = rev_end;
        if let Some(command) = command {
            self.commands[start_i] = CommandItem::Command(command);
            self.commands.drain(start_i + 1..end_i);
        } else {
            self.commands.drain(start_i..end_i);
        }
    }
}

impl<T> Deref for Commands<T> {
    type Target = [CommandItem<T>];
    fn deref(&self) -> &Self::Target {
        &self.commands
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

impl<'a, T> Iterator for RealizedIter<'a, T> {
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
impl<'a, T> FusedIterator for RealizedIter<'a, T> {}

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
    use super::Commands;
    #[test]
    fn com() {}
    #[test]
    #[allow(unused)]
    fn application() {
        enum Command {
            Add(char),
            Delete(char),
        }
        struct TextEditor {
            text: String,
            command: Commands<Command>,
        }
        impl TextEditor {
            pub fn new() -> Self {
                Self {
                    text: String::new(),
                    command: Commands::new(),
                }
            }
            pub fn add_char(&mut self, c: char) {
                self.text.push(c);
                self.command.push(Command::Add(c));
            }
            pub fn delete_char(&mut self) {
                if let Some(c) = self.text.pop() {
                    self.command.push(Command::Delete(c));
                }
            }
            pub fn undo(&mut self) {
                for action in self.command.undo() {
                    interpret_action(&mut self.text, action)
                }
            }
            pub fn redo(&mut self) {
                for action in self.command.redo() {
                    interpret_action(&mut self.text, action)
                }
            }
        }
        fn interpret_action(data: &mut String, action: Action<&Command>) {
            use Command::*;
            match action {
                Action::Do(Add(c)) | Action::Undo(Delete(c)) => {
                    data.push(*c);
                }
                Action::Undo(Add(_)) | Action::Do(Delete(_)) => {
                    data.pop();
                }
            }
        }
        let mut editor = TextEditor::new();
        editor.add_char('a'); //              :[1]
        editor.add_char('b'); //              :[2]
        editor.add_char('d'); //              :[3]
        assert_eq!(editor.text, "abd");

        editor.undo(); // first undo          :[4]
        assert_eq!(editor.text, "ab");

        editor.add_char('c'); //              :[5]
        assert_eq!(editor.text, "abc");

        editor.undo(); // Undo [5]            :[6]
        assert_eq!(editor.text, "ab");
        editor.undo(); // Undo the undo [4]   :[7]
        assert_eq!(editor.text, "abd");
        editor.undo(); // Undo [3]            :[8]
        assert_eq!(editor.text, "ab");
        editor.undo(); // Undo [2]            :[9]
        assert_eq!(editor.text, "a");

        editor.add_char('z'); //              :[10]
        assert_eq!(editor.text, "az");
        // when an action is performed after a sequence
        // of undo, the undos are merged: undos [6] to [9] are merged now

        editor.undo(); // back to [10]
        assert_eq!(editor.text, "a");
        editor.undo(); // back to [5]: reverses the consecutive sequence of undos in batch
        assert_eq!(editor.text, "abc");
        editor.undo(); // back to [4]
        assert_eq!(editor.text, "ab");
        editor.undo(); // back to [3]
        assert_eq!(editor.text, "abd");
        editor.undo(); // back to [2]
        assert_eq!(editor.text, "ab");
        editor.undo(); // back to [1]
        assert_eq!(editor.text, "a");
        editor.undo(); // back to [0]
        assert_eq!(editor.text, "");

        editor.redo(); // back to [1]
        assert_eq!(editor.text, "a");
        editor.redo(); // back to [2]
        assert_eq!(editor.text, "ab");
        editor.redo(); // back to [3]
        assert_eq!(editor.text, "abd");
        editor.redo(); // back to [4]
        assert_eq!(editor.text, "ab");
        editor.redo(); // back to [5]
        assert_eq!(editor.text, "abc");
        editor.redo(); // back to [9]: redo inner consecutive sequence of undos in batch
                       //              (undo are merged only when they are not the last action)
        assert_eq!(editor.text, "a");
        editor.redo(); // back to [10]
        assert_eq!(editor.text, "az");

        editor.add_char('1');
        editor.add_char('2');
        assert_eq!(editor.text, "az12");
        editor.undo();
        editor.undo();
        assert_eq!(editor.text, "az");
        editor.redo(); // undo is the last action, undo the undo only once
        assert_eq!(editor.text, "az1");
        editor.redo();
        assert_eq!(editor.text, "az12");
    }
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
    struct CommandString(Vec<(usize, char)>, Commands<(usize, char)>);
    impl CommandString {
        fn new() -> Self {
            CommandString(vec![], Commands::new())
        }
        fn push(&mut self, c: char) {
            let l = self.0.len();
            self.0.push((l, c));
            self.1.push((l, c));
        }
        #[track_caller]
        fn undo(&mut self) {
            Self::apply(&mut self.0, self.1.undo());
        }
        #[track_caller]
        fn redo(&mut self) {
            Self::apply(&mut self.0, self.1.redo());
        }
        #[track_caller]
        fn apply<'a>(
            s: &mut Vec<(usize, char)>,
            it: impl Iterator<Item = Action<&'a (usize, char)>>,
        ) {
            for c in it {
                match c {
                    Do(i) => {
                        assert_eq!(s.len(), i.0, "inconsitent push");
                        s.push(*i);
                    }
                    Undo(i) => {
                        assert_eq!(s.pop(), Some(*i), "inconsistent pop");
                    }
                }
            }
        }
    }
    #[test]
    fn command_sequence() {
        let mut c = CommandString::new();
        c.push('a');
        assert!(&c.0 == &[(0, 'a')]);
        assert!(c.1.len() == 1);
        c.undo();
        assert!(&c.0 == &[]);
        c.redo();
        assert!(&c.0 == &[(0, 'a')]);
        c.push('b');
        c.push('c');
        assert!(&c.0 == &[(0, 'a'), (1, 'b'), (2, 'c')]);
        c.redo();
        assert!(&c.0 == &[(0, 'a'), (1, 'b'), (2, 'c')]);
        c.undo();
        assert!(&c.0 == &[(0, 'a'), (1, 'b')]);
        c.push('d');
        assert!(&c.0 == &[(0, 'a'), (1, 'b'), (2, 'd')]);
        c.push('e');
        assert!(&c.0 == &[(0, 'a'), (1, 'b'), (2, 'd'), (3, 'e')]);
        c.undo();
        assert!(&c.0 == &[(0, 'a'), (1, 'b'), (2, 'd')]);
        c.undo();
        assert!(&c.0 == &[(0, 'a'), (1, 'b')]);
        c.undo();
        assert!(&c.0 == &[(0, 'a'), (1, 'b'), (2, 'c')]);
        c.undo();
        assert!(&c.0 == &[(0, 'a'), (1, 'b')]);
        c.undo();
        assert!(&c.0 == &[(0, 'a')]);
        c.push('f');
        assert!(&c.0 == &[(0, 'a'), (1, 'f')]);
        c.undo();
        assert!(&c.0 == &[(0, 'a')]);
        c.undo();
        assert!(&c.0 == &[(0, 'a'), (1, 'b'), (2, 'd'), (3, 'e')]);
        c.redo();
        assert!(&c.0 == &[(0, 'a')]);
        c.undo();
        assert!(&c.0 == &[(0, 'a'), (1, 'b'), (2, 'd'), (3, 'e')]);
    }
    #[test]
    fn crap() {
        use super::CommandItem;
        use super::Merge;
        use super::RealizedIter;
        use std::ops::ControlFlow;
        #[derive(Eq, PartialEq, Debug)]
        enum Command {
            A,
            B,
            AB,
        }
        use Command::*;
        fn is_ab<'a>(mut it: RealizedIter<'a, Command>) -> (bool, RealizedIter<'a, Command>) {
            let cond = it.next() == Some(&Command::B) && it.next() == Some(&Command::A);
            (cond, it)
        }
        {
            let mut commands = Commands::new();
            commands.push(Command::A);
            commands.push(Command::B);

            commands.merge(|start| {
                if let (true, end) = is_ab(start.clone()) {
                    println!("merge");
                    ControlFlow::Continue(Some(Merge {
                        start,
                        end,
                        command: Some(Command::AB),
                    }))
                } else {
                    ControlFlow::Continue(None)
                }
            });
            assert_eq!(&*commands, &[CommandItem::Command(AB)]);
        }
    }
    #[test]
    fn merge() {
        use super::CommandItem;
        use super::Merge;
        use super::RealizedIter;
        use std::ops::ControlFlow;
        #[derive(Eq, PartialEq, Debug)]
        enum Command {
            A,
            B,
            C,
            AB,
        }
        use Command::*;
        fn is_ab<'a>(mut it: RealizedIter<'a, Command>) -> (bool, RealizedIter<'a, Command>) {
            let cond = it.next() == Some(&Command::B) && it.next() == Some(&Command::A);
            (cond, it)
        }
        fn parse<'a>(
            start: RealizedIter<'a, Command>,
        ) -> ControlFlow<Option<Merge<'a, Command>>, Option<Merge<'a, Command>>> {
            if let (true, end) = is_ab(start.clone()) {
                println!("merge");
                ControlFlow::Continue(Some(Merge {
                    start,
                    end,
                    command: Some(Command::AB),
                }))
            } else {
                ControlFlow::Continue(None)
            }
        }
        {
            let mut commands = Commands::new();
            commands.push(Command::A);
            commands.push(Command::B);

            commands.merge(parse);
            assert_eq!(&commands.commands, &[CommandItem::Command(Command::AB)]);
        }
        {
            println!("new\n");
            let mut commands = Commands::new();
            commands.push(Command::A);
            commands.push(Command::C);
            commands.push(Command::B);
            commands.push(Command::A);
            commands.push(Command::B);

            commands.merge(parse);
            assert_eq!(
                &commands.commands,
                &[
                    CommandItem::Command(A),
                    CommandItem::Command(C),
                    CommandItem::Command(B),
                    CommandItem::Command(AB)
                ]
            );
        }
        {
            println!("new\n");
            let mut commands = Commands::new();
            commands.push(Command::A);
            commands.push(Command::C);
            commands.push(Command::A);
            commands.push(Command::B);
            commands.push(Command::B);
            commands.push(Command::A);
            commands.push(Command::B);

            commands.merge(parse);
            assert_eq!(
                &commands.commands,
                &[
                    CommandItem::Command(A),
                    CommandItem::Command(C),
                    CommandItem::Command(AB),
                    CommandItem::Command(B),
                    CommandItem::Command(AB)
                ]
            );
        }
        {
            println!("new\n");
            let mut commands = Commands::new();
            commands.push(Command::A);
            commands.push(Command::B);
            commands.push(Command::A);
            commands.push(Command::B);

            commands.merge(parse);
            assert_eq!(
                &*commands,
                &[CommandItem::Command(AB), CommandItem::Command(AB)]
            );
        }
    }
}
