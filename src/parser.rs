use std::collections::HashMap;

use crate::{ast::{Expression, ExpressionStatement, Identifier, IntegerLiteral, LetStatement, Program, ReturnStatement, Statement}, lexer::Lexer, token::{self, TokenType}};

pub enum OperatorPrecedence {
    LOWEST,
    EQUALS,
    LESSGREATER,
    SUM,
    PRODUCT,
    PREFIX,
    CALL,
}

#[derive(Default)]
pub struct Parser {
    lexer: Lexer,
    current_token: token::Token,
    peek_token: token::Token,
    pub errors: Vec<String>,
    prefix_parse_fns: HashMap<TokenType, Box<PrefixFunc>>,
    infix_parse_fns: HashMap<TokenType, Box<InfixFunc>>,
}

impl Parser {
    pub fn new(lexer: Lexer) -> Self {
        let mut p = Self {
            lexer,
            ..Default::default()
        };

        p.register_prefix(TokenType::IDENT, Box::new(Self::parse_identifier));
        p.register_prefix(TokenType::INT, Box::new(Self::parse_integer_literal));

        p.next_token();
        p.next_token();

        p
    }

    fn parse_identifier(&self) -> Box<dyn Expression> {
        return Box::new(Identifier {
            token: self.current_token.clone(),
            value: self.current_token.literal.clone(),
        });
    }

    fn parse_integer_literal(&self) -> Box<dyn Expression> {
        return Box::new(IntegerLiteral {
            token: self.current_token.clone(),
            value: self.current_token.literal.parse::<usize>().unwrap(),
        });
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
            _ => self.parse_expression_statement().and_then(|stmt| Some(Box::new(stmt) as Box<dyn Statement>)),
        }
    }

    fn parse_expression(&mut self, precedence: OperatorPrecedence) -> Option<Box<dyn Expression>> {
        let prefix_fn = self.prefix_parse_fns.get(&self.current_token.token_type)?;
        let left_expr = prefix_fn(&self);

        Some(left_expr)
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

        let value = self.parse_expression(OperatorPrecedence::LOWEST).unwrap();

        Some(LetStatement { token, name, value })
    }

    fn parse_return_statement(&mut self) -> Option<ReturnStatement> {
        let token = self.current_token.clone();
        
        while !self.current_token_is(TokenType::SEMICOLON) {
            self.next_token()
        }

        let return_value = self.parse_expression(OperatorPrecedence::LOWEST).unwrap();

        Some(ReturnStatement { token, return_value })
    }

    fn parse_expression_statement(&mut self) -> Option<ExpressionStatement> {
        let token = self.current_token.clone();

        let expression = self.parse_expression(OperatorPrecedence::LOWEST)?;

        if self.peek_token_is(TokenType::SEMICOLON) {
            self.next_token();
        }

        Some(ExpressionStatement { token, expression })
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

    fn register_prefix(&mut self, token_type: TokenType, func: Box<PrefixFunc>) {
        self.prefix_parse_fns.insert(token_type, func);
    }

    fn register_infix(&mut self, token_type: TokenType, func: Box<InfixFunc>) {
        self.infix_parse_fns.insert(token_type, func);
    }
}

pub type PrefixFunc = dyn Fn(&Parser) -> Box<dyn Expression>;
pub type InfixFunc = dyn Fn(Box<dyn Expression>) -> Box<dyn Expression>;

mod tests {
    use crate::{ast::{ExpressionStatement, Identifier, IntegerLiteral, LetStatement, Node, ReturnStatement, Statement}, lexer::Lexer};
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

    #[test]
    fn test_identifier_expression() {
        let input = "foobar;";

        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);

        let program = parser.parse_program().unwrap();
        check_parser_errors(&parser);

        assert_eq!(program.statements.len(), 1);

        let expression_stmt = program.statements[0].as_any().downcast_ref::<ExpressionStatement>();
        assert!(expression_stmt.is_some());

        let expr = &expression_stmt.unwrap().expression;
        let identifier = expr.as_any().downcast_ref::<Identifier>();
        assert!(identifier.is_some());

        assert_eq!(identifier.unwrap().value, "foobar");
        assert_eq!(identifier.unwrap().token_literal(), "foobar");
    }

    #[test]
    fn test_integer_literal_expression() {
        let input = "5;";

        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);

        let program = parser.parse_program().unwrap();
        check_parser_errors(&parser);

        assert_eq!(program.statements.len(), 1);

        let expression_stmt = program.statements[0].as_any().downcast_ref::<ExpressionStatement>();
        assert!(expression_stmt.is_some());

        let expr = &expression_stmt.unwrap().expression;
        let downcast_ref = expr.as_any().downcast_ref::<IntegerLiteral>();
        let literal = downcast_ref;
        assert!(literal.is_some());

        assert_eq!(literal.unwrap().value, 5);
        assert_eq!(literal.unwrap().token_literal(), "5");
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