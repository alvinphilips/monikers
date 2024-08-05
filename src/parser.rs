use crate::{ast::{Expression, Identifier, LetStatement, Program, ReturnStatement, Statement}, lexer::Lexer, token::{self, TokenType}};

#[derive(Default, Debug)]
pub struct Parser {
    lexer: Lexer,
    current_token: token::Token,
    peek_token: token::Token,
    pub errors: Vec<String>,
}

impl Parser {
    pub fn new(lexer: Lexer) -> Self {
        let mut p = Self {
            lexer,
            ..Default::default()
        };

        p.next_token();
        p.next_token();

        p
    }

    pub fn next_token(&mut self) {
        self.current_token = self.peek_token.clone();
        self.peek_token = self.lexer.next_token().unwrap();
    }

    pub fn parse_program(&mut self) -> Option<Program> {
        let mut program = Program::default();

        while !self.current_token_is(TokenType::EOF) {
            if let Some(stmt) = self.parse_statement() {
                program.statements.push(stmt);
            }
            self.next_token();
        }

        Some(program)
    }

    fn parse_statement(&mut self) -> Option<Box<dyn Statement>> {
        match self.current_token.token_type {
            TokenType::LET => self.parse_let_statement().and_then(|stmt| Some(Box::new(stmt) as Box<dyn Statement>)),
            TokenType::RETURN => self.parse_return_statement().and_then(|stmt| Some(Box::new(stmt) as Box<dyn Statement>)),
            _ => None
        }
    }

    fn parse_expression(&mut self) -> Option<Box<dyn Expression>> {
        Some(Box::new(Identifier::from_token(&self.current_token)))
    }

    fn parse_let_statement(&mut self) -> Option<LetStatement> {
        let token = self.current_token.clone();
        if !self.expect_peek(TokenType::IDENT) {
            return None;
        }
        let name = Identifier::from_token(&self.current_token);

        if !self.expect_peek(TokenType::ASSIGN) {
            return None;
        }

        while !self.current_token_is(TokenType::SEMICOLON) {
            self.next_token()
        }

        let value = self.parse_expression().unwrap();

        Some(LetStatement { token, name, value })
    }

    fn parse_return_statement(&mut self) -> Option<ReturnStatement> {
        let token = self.current_token.clone();
        
        while !self.current_token_is(TokenType::SEMICOLON) {
            self.next_token()
        }

        let return_value = self.parse_expression().unwrap();

        Some(ReturnStatement { token, return_value })
    }

    fn current_token_is(&self, check_type: TokenType) -> bool {
        self.current_token.token_type == check_type
    }

    fn peek_token_is(&self, check_type: TokenType) -> bool {
        self.peek_token.token_type == check_type
    }

    fn expect_peek(&mut self, expected: TokenType) -> bool {
        if self.peek_token_is(expected) {
            self.next_token();
            true
        } else {
            self.peek_error(expected);
            false
        }
    }

    fn peek_error(&mut self, expected: TokenType) {
        let msg = format!("Expected next token to be {:?}, got {:?} instead.", expected, self.current_token.token_type);
        self.errors.push(msg);
    }
}

mod tests {
    use crate::{ast::{LetStatement, Node, ReturnStatement, Statement}, lexer::Lexer};
    use super::Parser;

    #[test]
    fn test_let_statements() {
        let input = "let x = 5;
        let y = 10;
        let foobar = 838383;";

        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);

        let program = parser.parse_program().unwrap();
        check_parser_errors(&parser);

        assert_eq!(program.statements.len(), 3);

        for (i, ident) in ["x", "y", "foobar"].iter().enumerate() {
            let stmt = &program.statements[i];
            test_let_statement(stmt, *ident);
        }
    }

    #[test]
    fn test_return_statements() {
        let input = "return 5;
        return 10;
        return 993322;";

        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);

        let program = parser.parse_program().unwrap();
        check_parser_errors(&parser);

        assert_eq!(program.statements.len(), 3);

        for stmt in program.statements {
            let return_stmt = stmt.as_any().downcast_ref::<ReturnStatement>();
            assert!(return_stmt.is_some());
            assert_eq!(return_stmt.unwrap().token_literal(), "return");
        }
    }

    #[allow(dead_code)]
    fn test_let_statement(statement: &Box<dyn Statement>, name: &str) {
        assert_eq!(statement.token_literal(), "let");
        let let_statement = statement.as_any().downcast_ref::<LetStatement>();
        assert!(let_statement.is_some());
        assert_eq!(let_statement.unwrap().name.value, name);
        assert_eq!(let_statement.unwrap().name.token_literal(), name);
    }

    #[allow(dead_code)]
    fn check_parser_errors(parser: &Parser) {
        let errors = &parser.errors;

        if errors.len() == 0 {
            return;
        }

        eprintln!("parser has {} errors", errors.len());
        for error in errors {
            eprintln!("parser error: {}", error);
        }
    } 
}