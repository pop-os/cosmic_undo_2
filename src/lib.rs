use std::time::Instant;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
enum ComElem<T> {
    Command(T),
    Undo(usize),
}
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Command<T> {
    Do(T),
    Undo(T),
}

impl<T: PartialEq + Eq> Command<T> {
    fn is_reverse_of(&self, other: &Self) -> bool {
        use Command::*;
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

#[derive(Clone, Debug)]
pub struct CommandSequence<T> {
    commands: Vec<(Instant, ComElem<T>)>,
    undo_cache: Vec<Command<usize>>,
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct Iter<'a, T, It> {
    commands: &'a [(Instant, ComElem<T>)],
    to_do: It,
}
impl<'a, T, It: Iterator<Item = &'a Command<usize>>> Iterator for Iter<'a, T, It> {
    type Item = Command<&'a T>;
    fn next(&mut self) -> Option<Self::Item> {
        self.to_do.next().map(|c| match c {
            Command::Do(j) => {
                if let ComElem::Command(v) = &self.commands[*j].1 {
                    Command::Do(v)
                } else {
                    unreachable!()
                }
            }
            Command::Undo(j) => {
                if let ComElem::Command(v) = &self.commands[*j].1 {
                    Command::Undo(v)
                } else {
                    unreachable!()
                }
            }
        })
    }
}
pub type UndoIter<'a, T> = Iter<'a, T, std::iter::Rev<std::slice::Iter<'a, Command<usize>>>>;
impl<'a, T> UndoIter<'a, T> {
    fn new() -> Self {
        Self {
            commands: &[],
            to_do: [].iter().rev(),
        }
    }
    fn undo_at(
        commands: &'a [(Instant, ComElem<T>)],
        cache: &'a mut Vec<Command<usize>>,
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

pub type DoIter<'a, T> = Iter<'a, T, std::slice::Iter<'a, Command<usize>>>;
impl<'a, T> DoIter<'a, T> {
    fn new() -> Self {
        Self {
            commands: &[],
            to_do: [].iter(),
        }
    }
    fn do_at(
        commands: &'a [(Instant, ComElem<T>)],
        cache: &'a mut Vec<Command<usize>>,
        i: usize,
    ) -> Self {
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
    commands: &[(Instant, ComElem<T>)],
    undo_from: usize,
    undo_to: usize,
    to_do: &mut Vec<Command<usize>>,
) {
    for i in (undo_to..undo_from).into_iter().rev() {
        match commands[i] {
            (_, ComElem::Command(_)) => to_do.push(Command::Undo(i)),
            (_, ComElem::Undo(count)) => new_do(commands, i - (count + 1), i, to_do),
        }
    }
}
fn new_do<T>(
    commands: &[(Instant, ComElem<T>)],
    do_from: usize,
    do_to: usize,
    to_do: &mut Vec<Command<usize>>,
) {
    for i in (do_from..do_to).into_iter().rev() {
        match commands[i] {
            (_, ComElem::Command(_)) => to_do.push(Command::Do(i)),
            (_, ComElem::Undo(count)) => new_undo(commands, i, i - (count + 1), to_do),
        }
    }
}
fn do_simplify(to_do: &mut Vec<Command<usize>>) {
    if to_do.len() < 2 {
        return;
    }
    let mut analyzed = to_do.len() - 1;
    let mut cursor = to_do.len() - 1;
    while analyzed > 0 {
        analyzed -= 1;
        let com = &to_do[analyzed];
        if cursor < to_do.len() {
            if to_do[cursor].is_reverse_of(com) {
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

impl<T> CommandSequence<T> {
    pub fn new() -> Self {
        Self {
            commands: vec![],
            undo_cache: vec![],
        }
    }
    pub fn push(&mut self, command: T) {
        self.commands
            .push((Instant::now(), ComElem::Command(command)));
    }
    pub fn is_undoing(&self) -> bool {
        matches!(self.commands.last(), Some((_, ComElem::Undo(_))))
    }
    #[must_use = "the returned undo command should be realized"]
    pub fn undo(&mut self) -> UndoIter<'_, T> {
        let l = self.len();
        match self.commands.last_mut() {
            None => UndoIter::new(),
            Some((t, ComElem::Undo(i))) => {
                if *i + 2 < l {
                    *i += 1;
                    *t = Instant::now();
                    let t = l - *i - 2;
                    Iter::undo_at(&self.commands, &mut self.undo_cache, t)
                } else {
                    UndoIter::new()
                }
            }
            Some((_, ComElem::Command(_))) => {
                self.commands.push((Instant::now(), ComElem::Undo(0)));
                Iter::undo_at(&self.commands, &mut self.undo_cache, l - 1)
            }
        }
    }
    #[must_use = "the returned undo command should be realized"]
    pub fn redo(&mut self) -> DoIter<'_, T> {
        let l = self.len();
        match self.commands.last_mut() {
            Some((_, ComElem::Undo(i))) => {
                if let Some(ni) = i.checked_sub(1) {
                    let t = l - 2 - *i;
                    *i = ni;
                    Iter::do_at(&self.commands, &mut self.undo_cache, t)
                } else {
                    self.commands.pop();
                    Iter::do_at(
                        &self.commands,
                        &mut self.undo_cache,
                        self.commands.len() - 1,
                    )
                }
            }
            _ => DoIter::new(),
        }
    }
    pub fn len(&self) -> usize {
        self.commands.len()
    }
    pub fn remove_old_commands(&mut self, old_limit: Instant) {
        if let Some(i) = self.commands.iter().position(|(t, _)| t > &old_limit) {
            self.remove_first(i)
        }
    }
    pub fn clear(&mut self) {
        self.commands.clear();
    }
    pub fn keep_last(&mut self, count: usize) {
        let i = self.len().saturating_sub(count);
        self.remove_first(i)
    }
    fn remove_first(&mut self, i: usize) {
        self.commands.drain(..i);
    }
}

#[cfg(test)]
mod test {
    use super::Command;
    use super::Command::*;
    use super::CommandSequence;
    #[test]
    fn simplify() {
        use super::do_simplify;
        fn simplify(mut to_do: Vec<Command<usize>>) -> Vec<Command<usize>> {
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
    struct CommandString(Vec<(usize, char)>, CommandSequence<(usize, char)>);
    impl CommandString {
        fn new() -> Self {
            CommandString(vec![], CommandSequence::new())
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
            it: impl Iterator<Item = Command<&'a (usize, char)>>,
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
}
