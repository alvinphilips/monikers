use std::io::{Stdin, Stdout, Write};

use crate::{lexer::Lexer, token::TokenType};

const PROMPT: &'static str = ">> ";

pub fn start(stdin: Stdin, mut stdout: Stdout) {
    let mut buffer = String::new();

    print!("{PROMPT}");
    stdout.flush().unwrap();

    while let Some(input) = stdin.read_line(&mut buffer).ok() {
        if input == 0 || buffer.split_whitespace().next() == Some("exit") {
            return;
        }

        let mut lexer = Lexer::new(&buffer[..input]);

        while let Some(tok) = lexer.next_token() {
            if tok.token_type == TokenType::EOF {
                break;
            }
            println!("{:?}", tok);
        }

        buffer.clear();
        print!("{PROMPT}");
        stdout.flush().unwrap();
    }
}
