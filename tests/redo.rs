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
fn redo() {
    {
        let mut commands = Commands::new();

        commands.push(A); // A
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), false);
        commands.push(B); // A B
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), false);
        commands.undo(); // A
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), true);
        commands.undo(); //
        assert_eq!(commands.can_undo(), false);
        assert_eq!(commands.can_redo(), true);
        commands.push(C); // C
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), false);
        commands.undo(); //
        assert_eq!(commands.can_undo(), true);    
        assert_eq!(commands.can_redo(), true);
        commands.undo(); // A B
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), true);

        let v: Vec<_> = commands.redo().collect();
        assert_eq!(v, [Action::Undo(&B), Action::Undo(&A)]);
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), true);

        let v: Vec<_> = commands.redo().collect();
        assert_eq!(v, [Action::Do(&C)]);
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), false);
    }
    {
        let mut commands = Commands::new();

        commands.push(A); // A
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), false);
        commands.push(B); // A B
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), false);
        commands.undo(); // A
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), true);
        commands.undo(); //
                         //
        assert_eq!(commands.can_undo(), false);
        assert_eq!(commands.can_redo(), true);
        commands.push(C); // C
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), false);
                          //
        commands.undo(); //
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), true);
        commands.undo(); // A B
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), true);
        commands.undo(); // A
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), true);        
        commands.undo(); //
        assert_eq!(commands.can_undo(), false);
        assert_eq!(commands.can_redo(), true);

        commands.push(D); // D
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), false);

        commands.undo(); //
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), true);

        commands.undo(); // C
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), true);
        commands.undo(); //
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), true);
        commands.undo(); // A B
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), true);

        let v: Vec<_> = commands.redo().collect();
        assert_eq!(v, [Action::Undo(&B), Action::Undo(&A)]);
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), true);

        let v: Vec<_> = commands.redo().collect();
        assert_eq!(v, [Action::Do(&C)]);
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), true);

        let v: Vec<_> = commands.redo().collect();
        assert_eq!(v, [Action::Undo(&C)]);
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), true);

        let v: Vec<_> = commands.redo().collect();
        assert_eq!(v, [Action::Do(&D)]);
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), false);

        let v: Vec<_> = commands.redo().collect();
        assert_eq!(v, []);
        assert_eq!(commands.can_undo(), true);
        assert_eq!(commands.can_redo(), false);
    }
}

#[test]
fn redo_all() {
    let mut commands = Commands::new();

    commands.push(A);
    assert_eq!(commands.can_redo(), false);
    assert_eq!(commands.can_undo(), true);
    commands.push(B);
    assert_eq!(commands.can_redo(), false);
    assert_eq!(commands.can_undo(), true);
    commands.undo();
    assert_eq!(commands.can_redo(), true);
    assert_eq!(commands.can_undo(), true);
    commands.undo();
    assert_eq!(commands.can_redo(), true);
    assert_eq!(commands.can_undo(), false);

    let v: Vec<_> = commands.redo_all().collect();
    assert_eq!(v, [Action::Do(&A), Action::Do(&Command::B)]);
    assert_eq!(commands.can_redo(), false);
    assert_eq!(commands.can_undo(), true);
}