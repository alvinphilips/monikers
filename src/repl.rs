use std::io::{Stdin, Stdout, Write};

use crate::{lexer::Lexer, parser::Parser};

const PROMPT: &'static str = ">> ";

pub fn start(stdin: Stdin, mut stdout: Stdout) {
    let mut buffer = String::new();

    print!("{PROMPT}");
    stdout.flush().unwrap();

    while let Some(input) = stdin.read_line(&mut buffer).ok() {
        if input == 0 || buffer.split_whitespace().next() == Some("exit") {
            return;
        }

        let lexer = Lexer::new(&buffer[..input]);
        let mut parser = Parser::new(lexer);

        let program = parser.parse_program().unwrap();
        println!("{}", program);

        buffer.clear();
        print!("{PROMPT}");
        stdout.flush().unwrap();
    }
}
