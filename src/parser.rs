use crate::{
    ast::{BlockStatement, Boolean, IfExpression, InfixExpression},
    Map,
};
use thiserror::Error;

use crate::{
    ast::{
        Expression, ExpressionStatement, Identifier, IntegerLiteral, LetStatement,
        PrefixExpression, Program, ReturnStatement, Statement,
    },
    lexer::Lexer,
    token::{self, Token, TokenType},
};

#[derive(Debug, Default, Clone, Copy, PartialEq, PartialOrd)]
pub enum OperatorPrecedence {
    #[default]
    LOWEST,
    EQUALS,
    LESSGREATER,
    SUM,
    PRODUCT,
    PREFIX,
    CALL,
}

#[derive(Error, Debug)]
pub enum ParserError {}

#[derive(Default)]
pub struct Parser {
    lexer: Lexer,
    current_token: token::Token,
    peek_token: token::Token,
    pub errors: Vec<String>,
    prefix_parse_fns: Map<TokenType, PrefixFunc>,
    infix_parse_fns: Map<TokenType, InfixFunc>,
    precedences: Map<TokenType, OperatorPrecedence>,
}

impl Parser {
    pub fn new(lexer: Lexer) -> Self {
        let mut p = Self {
            lexer,
            ..Default::default()
        };

        p.precedences
            .insert(TokenType::EQ, OperatorPrecedence::EQUALS);
        p.precedences
            .insert(TokenType::NE, OperatorPrecedence::EQUALS);
        p.precedences
            .insert(TokenType::LT, OperatorPrecedence::LESSGREATER);
        p.precedences
            .insert(TokenType::GT, OperatorPrecedence::LESSGREATER);
        p.precedences
            .insert(TokenType::PLUS, OperatorPrecedence::SUM);
        p.precedences
            .insert(TokenType::MINUS, OperatorPrecedence::SUM);
        p.precedences
            .insert(TokenType::ASTERISK, OperatorPrecedence::PRODUCT);
        p.precedences
            .insert(TokenType::SLASH, OperatorPrecedence::PRODUCT);

        p.register_prefix(TokenType::IDENT, Self::parse_identifier);
        p.register_prefix(TokenType::INT, Self::parse_integer_literal);
        p.register_prefix(TokenType::BANG, Self::parse_prefix_expression);
        p.register_prefix(TokenType::MINUS, Self::parse_prefix_expression);
        p.register_prefix(TokenType::TRUE, Self::parse_boolean);
        p.register_prefix(TokenType::FALSE, Self::parse_boolean);
        p.register_prefix(TokenType::LPAREN, Self::parse_grouped_expression);
        p.register_prefix(TokenType::IF, Self::parse_if_expression);

        p.register_infix(TokenType::PLUS, Self::parse_infix_expression);
        p.register_infix(TokenType::MINUS, Self::parse_infix_expression);
        p.register_infix(TokenType::ASTERISK, Self::parse_infix_expression);
        p.register_infix(TokenType::SLASH, Self::parse_infix_expression);
        p.register_infix(TokenType::EQ, Self::parse_infix_expression);
        p.register_infix(TokenType::NE, Self::parse_infix_expression);
        p.register_infix(TokenType::LT, Self::parse_infix_expression);
        p.register_infix(TokenType::GT, Self::parse_infix_expression);

        p.next_token();
        p.next_token();

        p
    }

    fn parse_identifier(&mut self) -> Box<dyn Expression> {
        return Box::new(Identifier {
            token: self.current_token.clone(),
            value: self.current_token.literal.clone(),
        });
    }

    fn parse_integer_literal(&mut self) -> Box<dyn Expression> {
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
            TokenType::LET => self
                .parse_let_statement()
                .and_then(|stmt| Some(Box::new(stmt) as Box<dyn Statement>)),
            TokenType::RETURN => self
                .parse_return_statement()
                .and_then(|stmt| Some(Box::new(stmt) as Box<dyn Statement>)),
            _ => self
                .parse_expression_statement()
                .and_then(|stmt| Some(Box::new(stmt) as Box<dyn Statement>)),
        }
    }

    fn parse_expression(&mut self, precedence: OperatorPrecedence) -> Option<Box<dyn Expression>> {
        let token_type = self.current_token.token_type;
        let prefix_fn = {
            self.prefix_parse_fns
                .get(&token_type)
                .expect(&format!("No prefix parse function found {}.", token_type))
        };

        let mut left_expr = prefix_fn(self);

        while !self.peek_token_is(TokenType::SEMICOLON) && precedence < self.peek_precedence() {
            if let Some(&infix_fn) = self.infix_parse_fns.get(&self.peek_token.token_type) {
                self.next_token();
                left_expr = infix_fn(self, left_expr);
            } else {
                return Some(left_expr);
            }
        }

        Some(left_expr)
    }

    fn parse_prefix_expression(&mut self) -> Box<dyn Expression> {
        let token = self.current_token.clone();
        let operator = self.current_token.literal.clone();

        self.next_token();

        let right = self.parse_expression(OperatorPrecedence::PREFIX).unwrap();

        Box::new(PrefixExpression {
            token,
            operator,
            right,
        })
    }

    fn parse_infix_expression(&mut self, left: Box<dyn Expression>) -> Box<dyn Expression> {
        let token = self.current_token.clone();
        let operator = self.current_token.literal.clone();

        let precedence = self.current_precedence();
        self.next_token();
        let right = self.parse_expression(precedence).unwrap();

        Box::new(InfixExpression {
            token,
            left,
            operator,
            right,
        })
    }

    fn parse_grouped_expression(&mut self) -> Box<dyn Expression> {
        self.next_token();

        let expr = self.parse_expression(OperatorPrecedence::LOWEST).unwrap();

        assert!(self.expect_peek(TokenType::RPAREN));

        expr
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

        let value = Box::new(Identifier {
            token: self.current_token.clone(),
            value: "uwu".into(),
        });

        Some(LetStatement { token, name, value })
    }

    fn parse_return_statement(&mut self) -> Option<ReturnStatement> {
        let token = self.current_token.clone();

        while !self.current_token_is(TokenType::SEMICOLON) {
            self.next_token()
        }

        let return_value = Box::new(Identifier {
            token: self.current_token.clone(),
            value: "uwu".into(),
        });

        Some(ReturnStatement {
            token,
            return_value,
        })
    }

    fn parse_expression_statement(&mut self) -> Option<ExpressionStatement> {
        let token = self.current_token.clone();

        let expression = self.parse_expression(OperatorPrecedence::LOWEST)?;

        if self.peek_token_is(TokenType::SEMICOLON) {
            self.next_token();
        }

        Some(ExpressionStatement { token, expression })
    }

    fn parse_if_expression(&mut self) -> Box<dyn Expression> {
        let token = self.current_token.clone();

        assert!(self.expect_peek(TokenType::LPAREN));

        self.next_token();

        let condition = self.parse_expression(OperatorPrecedence::LOWEST).unwrap();

        assert!(self.expect_peek(TokenType::RPAREN));
        assert!(self.expect_peek(TokenType::LBRACE));

        let consequence = self.parse_block_statement();

        Box::new(IfExpression { token, condition, consequence, alternative: None})
    }

    fn parse_block_statement(&mut self) -> BlockStatement {
        let mut block = BlockStatement {token: self.current_token.clone(), statements: Vec::new()};

        self.next_token();

        while !self.current_token_is(TokenType::RBRACE) && !self.current_token_is(TokenType::EOF) {
            if let Some(stmt) = self.parse_statement() {
                block.statements.push(stmt);
            }
            self.next_token();
        }
        block
    }

    fn parse_boolean(&mut self) -> Box<dyn Expression> {
        Box::new(Boolean {
            token: self.current_token.clone(),
            value: self.current_token_is(TokenType::TRUE),
        })
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
            self.peek_error(&expected);
            false
        }
    }

    fn peek_precedence(&self) -> OperatorPrecedence {
        self.precedences
            .get(&self.peek_token.token_type)
            .copied()
            .unwrap_or_default()
    }

    fn current_precedence(&self) -> OperatorPrecedence {
        self.precedences
            .get(&self.current_token.token_type)
            .copied()
            .unwrap_or_default()
    }

    fn peek_error(&mut self, expected: &TokenType) {
        let msg = format!(
            "Expected next token to be {:?}, got {:?} instead.",
            expected, self.current_token.token_type
        );
        self.errors.push(msg);
    }

    fn register_prefix(&mut self, token_type: TokenType, func: PrefixFunc) {
        self.prefix_parse_fns.insert(token_type, func);
    }

    fn register_infix(&mut self, token_type: TokenType, func: InfixFunc) {
        self.infix_parse_fns.insert(token_type, func);
    }
}

pub type PrefixFunc = fn(&mut Parser) -> Box<dyn Expression>;
pub type InfixFunc = fn(&mut Parser, Box<dyn Expression>) -> Box<dyn Expression>;

#[cfg(test)]
mod tests {
    use std::usize;

    use super::Parser;
    use crate::ast::{Boolean, IfExpression, InfixExpression};
    #[allow(unused_imports)]
    use crate::{
        ast::{
            Expression, ExpressionStatement, Identifier, IntegerLiteral, LetStatement, Node,
            PrefixExpression, ReturnStatement, Statement,
        },
        lexer::Lexer,
    };

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

        let expression_stmt = program.statements[0]
            .as_any()
            .downcast_ref::<ExpressionStatement>();
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

        let expression_stmt = program.statements[0]
            .as_any()
            .downcast_ref::<ExpressionStatement>();
        assert!(expression_stmt.is_some());

        let expr = &expression_stmt.unwrap().expression;
        test_integer_literal(expr, 5);
    }

    #[test]
    fn test_prefix_expressions() {
        struct PrefixTest {
            input: &'static str,
            operator: &'static str,
            value: ExpectedLiteral,
        }

        let prefix_tests = [
            PrefixTest {
                input: "!5;",
                operator: "!",
                value: 5.into(),
            },
            PrefixTest {
                input: "-15;",
                operator: "-",
                value: 15.into(),
            },
            PrefixTest {
                input: "!true;",
                operator: "!",
                value: true.into(),
            },
            PrefixTest {
                input: "!false;",
                operator: "!",
                value: false.into(),
            },
        ];

        for test in prefix_tests {
            let lexer = Lexer::new(&test.input);
            let mut parser = Parser::new(lexer);

            let program = parser.parse_program().unwrap();
            check_parser_errors(&parser);

            assert_eq!(program.statements.len(), 1);

            println!("{}", program.statements[0]);

            let expression_stmt = program.statements[0]
                .as_any()
                .downcast_ref::<ExpressionStatement>();
            assert!(expression_stmt.is_some());

            let prefix_stmt = expression_stmt
                .unwrap()
                .expression
                .as_any()
                .downcast_ref::<PrefixExpression>()
                .expect("Expression is not a PrefixExpression");

            assert_eq!(prefix_stmt.operator, test.operator);
            test_literal_expression(&prefix_stmt.right, test.value);
        }
    }

    #[test]
    fn test_infix_expressions() {
        struct InfixTest {
            input: &'static str,
            left: ExpectedLiteral,
            operator: &'static str,
            right: ExpectedLiteral,
        }

        let infix_tests = [
            InfixTest {
                input: "5 + 5;",
                left: 5.into(),
                operator: "+",
                right: 5.into(),
            },
            InfixTest {
                input: "5 - 5;",
                left: 5.into(),
                operator: "-",
                right: 5.into(),
            },
            InfixTest {
                input: "5 * 5;",
                left: 5.into(),
                operator: "*",
                right: 5.into(),
            },
            InfixTest {
                input: "5 / 5;",
                left: 5.into(),
                operator: "/",
                right: 5.into(),
            },
            InfixTest {
                input: "5 > 5;",
                left: 5.into(),
                operator: ">",
                right: 5.into(),
            },
            InfixTest {
                input: "5 < 5;",
                left: 5.into(),
                operator: "<",
                right: 5.into(),
            },
            InfixTest {
                input: "5 == 5;",
                left: 5.into(),
                operator: "==",
                right: 5.into(),
            },
            InfixTest {
                input: "5 != 5;",
                left: 5.into(),
                operator: "!=",
                right: 5.into(),
            },
            InfixTest {
                input: "true == true;",
                left: true.into(),
                operator: "==",
                right: true.into(),
            },
            InfixTest {
                input: "true != false;",
                left: true.into(),
                operator: "!=",
                right: false.into(),
            },
            InfixTest {
                input: "false == false;",
                left: false.into(),
                operator: "==",
                right: false.into(),
            },
        ];

        for test in infix_tests {
            let lexer = Lexer::new(&test.input);
            let mut parser = Parser::new(lexer);

            let program = parser.parse_program().unwrap();
            check_parser_errors(&parser);

            assert_eq!(program.statements.len(), 1);

            println!("{}", program.statements[0]);

            let expression_stmt = program.statements[0]
                .as_any()
                .downcast_ref::<ExpressionStatement>();
            assert!(expression_stmt.is_some());

            test_infix_expression(
                &expression_stmt.unwrap().expression,
                test.left,
                test.operator,
                test.right,
            )
        }
    }

    #[test]
    fn test_operator_precedence() {
        struct OperatorPrecedenceTest {
            input: &'static str,
            expected: &'static str,
        }

        let operator_precedence_tests = [
            OperatorPrecedenceTest {
                input: "-a * b",
                expected: "((-a) * b)",
            },
            OperatorPrecedenceTest {
                input: "!-a",
                expected: "(!(-a))",
            },
            OperatorPrecedenceTest {
                input: "a + b + c",
                expected: "((a + b) + c)",
            },
            OperatorPrecedenceTest {
                input: "a + b - c",
                expected: "((a + b) - c)",
            },
            OperatorPrecedenceTest {
                input: "a * b / c",
                expected: "((a * b) / c)",
            },
            OperatorPrecedenceTest {
                input: "a + b / c",
                expected: "(a + (b / c))",
            },
            OperatorPrecedenceTest {
                input: "a + b * c + d / e - f",
                expected: "(((a + (b * c)) + (d / e)) - f)",
            },
            OperatorPrecedenceTest {
                input: "5 > 4 == 3 < 4",
                expected: "((5 > 4) == (3 < 4))",
            },
            OperatorPrecedenceTest {
                input: "5 < 4 != 3 > 4",
                expected: "((5 < 4) != (3 > 4))",
            },
            OperatorPrecedenceTest {
                input: "3 + 4 * 5 == 3 * 1 + 4 * 5",
                expected: "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))",
            },
            OperatorPrecedenceTest {
                input: "3 + 4 * 5 == 3 * 1 + 4 * 5",
                expected: "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))",
            },
            OperatorPrecedenceTest {
                input: "true",
                expected: "true",
            },
            OperatorPrecedenceTest {
                input: "false",
                expected: "false",
            },
            OperatorPrecedenceTest {
                input: "3 > 5 == false",
                expected: "((3 > 5) == false)",
            },
            OperatorPrecedenceTest {
                input: "3 < 5 == true",
                expected: "((3 < 5) == true)",
            },
            OperatorPrecedenceTest {
                input: "1 + (2 + 3) + 4",
                expected: "((1 + (2 + 3)) + 4)",
            },
            OperatorPrecedenceTest {
                input: "(5 + 5) * 2",
                expected: "((5 + 5) * 2)",
            },
            OperatorPrecedenceTest {
                input: "2 / (5 + 5)",
                expected: "(2 / (5 + 5))",
            },
            OperatorPrecedenceTest {
                input: "-(5 + 5)",
                expected: "(-(5 + 5))",
            },
            OperatorPrecedenceTest {
                input: "!(true == true)",
                expected: "(!(true == true))",
            },
        ];

        for test in operator_precedence_tests {
            let lexer = Lexer::new(&test.input);
            let mut parser = Parser::new(lexer);

            let program = parser.parse_program().unwrap();
            check_parser_errors(&parser);

            assert_eq!(format!("{}", program), test.expected)
        }
    }

    

        #[test]
        fn test_if_expression() {
            let input = "if (x < y) { x }";

            let lexer = Lexer::new(input);
            let mut parser = Parser::new(lexer);

            let program = parser.parse_program().unwrap();
            check_parser_errors(&parser);

            assert_eq!(program.statements.len(), 1);

            let if_stmt = program.statements[0]
                .as_any().downcast_ref::<ExpressionStatement>().unwrap()
                .expression.as_any().downcast_ref::<IfExpression>().unwrap();

            test_infix_expression(&if_stmt.condition, "x".into(), "<", "y".into());

            assert_eq!(if_stmt.consequence.statements.len(), 1);

            let consequence = if_stmt.consequence.statements[0].as_any().downcast_ref::<ExpressionStatement>().unwrap();

            test_identifier(&consequence.expression, "x");

            assert!(if_stmt.alternative.is_none());
        }

    fn test_let_statement(statement: &Box<dyn Statement>, name: &str) {
        assert_eq!(statement.token_literal(), "let");
        let let_statement = statement.as_any().downcast_ref::<LetStatement>();
        assert!(let_statement.is_some());
        assert_eq!(let_statement.unwrap().name.value, name);
        assert_eq!(let_statement.unwrap().name.token_literal(), name);
    }

    enum ExpectedLiteral {
        Int(usize),
        Str(String),
        Bool(bool),
    }

    impl From<usize> for ExpectedLiteral {
        fn from(value: usize) -> Self {
            Self::Int(value)
        }
    }

    impl From<&str> for ExpectedLiteral {
        fn from(value: &str) -> Self {
            Self::Str(value.into())
        }
    }

    impl From<bool> for ExpectedLiteral {
        fn from(value: bool) -> Self {
            Self::Bool(value)
        }
    }

    fn test_literal_expression(expr: &Box<dyn Expression>, value: ExpectedLiteral) {
        match value {
            ExpectedLiteral::Int(i) => test_integer_literal(expr, i),
            ExpectedLiteral::Str(s) => test_identifier(expr, &s),
            ExpectedLiteral::Bool(b) => test_boolean_literal(expr, b),
        }
    }

    fn test_identifier(expr: &Box<dyn Expression>, value: &str) {
        let identifier = expr
            .as_any()
            .downcast_ref::<Identifier>()
            .expect("Expression was not an Identifier.");

        assert_eq!(identifier.value, value);
        assert_eq!(identifier.token_literal(), value);
    }

    fn test_integer_literal(expr: &Box<dyn Expression>, value: usize) {
        let literal = expr
            .as_any()
            .downcast_ref::<IntegerLiteral>()
            .expect("Expression was not an IntegerLiteral.");

        assert_eq!(literal.value, value);
        assert_eq!(literal.token_literal(), format!("{value}"));
    }

    fn test_boolean_literal(expr: &Box<dyn Expression>, value: bool) {
        let literal = expr
            .as_any()
            .downcast_ref::<Boolean>()
            .expect("Expression was not an IntegerLiteral.");

        assert_eq!(literal.value, value);
        assert_eq!(literal.token_literal(), format!("{value}"));
    }

    fn test_infix_expression(
        expr: &Box<dyn Expression>,
        left: ExpectedLiteral,
        operator: &str,
        right: ExpectedLiteral,
    ) {
        let infix = expr
            .as_any()
            .downcast_ref::<InfixExpression>()
            .expect("Expression was not a InfixExpression.");

        test_literal_expression(&infix.left, left);
        assert_eq!(infix.operator, operator);
        test_literal_expression(&infix.right, right);
    }

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
