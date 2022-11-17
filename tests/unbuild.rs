#![allow(unused)]
use undo_2::Commands;

#[derive(Debug, Eq, PartialEq)]
enum Command {
    A,
    B,
    C,
}
use Command::*;

#[test]
fn unbuild() {
    let mut commands = Commands::new();

    commands.push(A);
    commands.push(B);
    commands.undo();
    commands.push(C);

    let c = commands.unbuild();
    assert_eq!(c, Some(&C));

    let c = commands.unbuild();
    assert_eq!(c, Some(&A));

    assert!(commands.unbuild().is_none());
}
