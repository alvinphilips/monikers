use std::io::{Stdin, Stdout, Write};

use crate::{lexer::Lexer, parser::Parser};

const PROMPT: &str = ">> ";

pub fn start(stdin: Stdin, mut stdout: Stdout) {
    let mut buffer = String::new();

    print!("{PROMPT}");
    stdout.flush().unwrap();

    while let Ok(input) = stdin.read_line(&mut buffer) {
        if input == 0 || buffer.split_whitespace().next() == Some("exit") {
            return;
        }

        let lexer = Lexer::new(&buffer[..input]);
        let mut parser = Parser::new(lexer);

        match parser.parse_program() {
            Ok(program) => println!("{program}"),
            Err(errors) => {
                eprintln!("{errors}");
            }
        }

        buffer.clear();
        print!("{PROMPT}");
        stdout.flush().unwrap();
    }
}
