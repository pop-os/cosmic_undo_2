#![allow(unused)]
use cosmic_undo_2::{Action, Commands};

#[derive(Debug, Eq, PartialEq)]
enum Command {
    A,
    B,
    C,
    D,
}
use Command::*;

#[test]
fn undo() {
    use Action::*;
    {
        let mut c = Commands::default();

        assert_eq!(c.can_undo(), false);
        assert_eq!(c.can_redo(), false);
        c.push(A);
        assert_eq!(c.can_undo(), true);
        assert_eq!(c.can_redo(), false);
        c.push(B);
        assert_eq!(c.can_undo(), true);
        assert_eq!(c.can_redo(), false);

        let v: Vec<_> = c.undo().collect();
        assert_eq!(v, [Undo(&B)]);
        assert_eq!(c.can_undo(), true);
        assert_eq!(c.can_redo(), true);
        let v: Vec<_> = c.undo().collect();
        assert_eq!(v, [Undo(&A)]);
        assert_eq!(c.can_undo(), false);
        assert_eq!(c.can_redo(), true);
    }
    {
        let mut c = Commands::default();

        assert_eq!(c.can_undo(), false);
        assert_eq!(c.can_redo(), false);
        c.push(A);
        assert_eq!(c.can_undo(), true);
        assert_eq!(c.can_redo(), false);
        c.push(B);
        assert_eq!(c.can_undo(), true);
        assert_eq!(c.can_redo(), false);
        c.undo();
        assert_eq!(c.can_undo(), true);
        assert_eq!(c.can_redo(), true);
        c.undo();
        assert_eq!(c.can_undo(), false);
        assert_eq!(c.can_redo(), true);
        c.push(C);
        assert_eq!(c.can_undo(), true);
        assert_eq!(c.can_redo(), false);

        let v: Vec<_> = c.undo().collect();
        assert_eq!(v, [Undo(&C)]);
        assert_eq!(c.can_undo(), true);
        assert_eq!(c.can_redo(), true);

        let v: Vec<_> = c.undo().collect();
        assert_eq!(v, [Do(&A), Do(&B)]);
        assert_eq!(c.can_undo(), true);
        assert_eq!(c.can_redo(), true);
        c.undo();
        assert_eq!(c.can_undo(), true);
        assert_eq!(c.can_redo(), true);
        c.undo();
        assert_eq!(c.can_undo(), false);
        assert_eq!(c.can_redo(), true);
        c.undo();
        assert_eq!(c.can_undo(), false);
        assert_eq!(c.can_redo(), true);
        
    }
    {
        let mut c = Commands::default();

        c.push(A); // A
        assert_eq!(c.can_undo(), true);
        assert_eq!(c.can_redo(), false);
        c.push(B); // A B
        assert_eq!(c.can_undo(), true);
        assert_eq!(c.can_redo(), false);
        c.undo(); //  A
        assert_eq!(c.can_undo(), true);
        assert_eq!(c.can_redo(), true);
        c.undo(); //
        assert_eq!(c.can_undo(), false);
        assert_eq!(c.can_redo(), true);
        c.push(C); // C
        c.undo(); //
        assert_eq!(c.can_undo(), true);
        assert_eq!(c.can_redo(), true);
        c.undo(); //  A B
        assert_eq!(c.can_undo(), true);
        c.push(D); // A B D
        assert_eq!(c.can_undo(), true);
        assert_eq!(c.can_redo(), false);

        let v: Vec<_> = c.undo().collect();
        assert_eq!(v, [Undo(&D)]);
        assert_eq!(c.can_undo(), true);
        assert_eq!(c.can_redo(), true);

        let v: Vec<_> = c.undo().collect();
        assert_eq!(v, [Undo(&B), Undo(&A), Do(&C)]);
        assert_eq!(c.can_undo(), true);
        assert_eq!(c.can_redo(), true);
    }
}