use lexer::Lexer;
use monikers::*;
use color_eyre::Result;
use parser::Parser;

fn main() -> Result<()> {
    if let Some(path) = std::env::args().skip(1).next() {
        let file = std::fs::read_to_string(path)?;
        let lexer = Lexer::new(&file);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program()?;
        println!("{program}")
    } else {
        repl::start(std::io::stdin(), std::io::stdout());
    }

    Ok(())
}