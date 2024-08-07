use crate::{
    ast::{BlockStatement, Boolean, CallExpression, FunctionLiteral, IfExpression, InfixExpression},
    Map,
};
use thiserror::Error;
use eyre::{eyre, Context, Result};

use crate::{
    ast::{
        Expression, ExpressionStatement, Identifier, IntegerLiteral, LetStatement,
        PrefixExpression, Program, ReturnStatement, Statement,
    },
    lexer::Lexer,
    token::{self, TokenType},
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
pub enum ParserError {
    #[error("expression did not evaluate to an integer literal.")]
    InvalidIntegerLiteral(#[from] std::num::ParseIntError),
    #[error("no prefix function found for token {0}")]
    PrefixFnMissing(TokenType),
    #[error("unexpected token. expected: `{0}`, got: `{1}`")]
    UnexpectedToken(TokenType, TokenType),
    #[error("reached end of stream while parsing.")]
    ReachedEndOfStream,
}

pub type PrefixFunc = fn(&mut Parser) -> Result<Box<dyn Expression>>;
pub type InfixFunc = fn(&mut Parser, Box<dyn Expression>) -> Result<Box<dyn Expression>>;

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
        p.precedences
            .insert(TokenType::LPAREN, OperatorPrecedence::CALL);

        p.register_prefix(TokenType::EOF, Self::parse_unexpected_eof);
        p.register_prefix(TokenType::IDENT, Self::parse_identifier);
        p.register_prefix(TokenType::INT, Self::parse_integer_literal);
        p.register_prefix(TokenType::BANG, Self::parse_prefix_expression);
        p.register_prefix(TokenType::MINUS, Self::parse_prefix_expression);
        p.register_prefix(TokenType::TRUE, Self::parse_boolean);
        p.register_prefix(TokenType::FALSE, Self::parse_boolean);
        p.register_prefix(TokenType::LPAREN, Self::parse_grouped_expression);
        p.register_prefix(TokenType::IF, Self::parse_if_expression);
        p.register_prefix(TokenType::FUNCTION, Self::parse_function_literal);

        p.register_infix(TokenType::PLUS, Self::parse_infix_expression);
        p.register_infix(TokenType::MINUS, Self::parse_infix_expression);
        p.register_infix(TokenType::ASTERISK, Self::parse_infix_expression);
        p.register_infix(TokenType::SLASH, Self::parse_infix_expression);
        p.register_infix(TokenType::EQ, Self::parse_infix_expression);
        p.register_infix(TokenType::NE, Self::parse_infix_expression);
        p.register_infix(TokenType::LT, Self::parse_infix_expression);
        p.register_infix(TokenType::GT, Self::parse_infix_expression);
        p.register_infix(TokenType::LPAREN, Self::parse_call_expression);

        p.next_token();
        p.next_token();

        p
    }

    fn parse_identifier(&mut self) -> Result<Box<dyn Expression>> {
        if !self.current_token_is(TokenType::IDENT) {
            Err(eyre!("Invalid token type {}", self.current_token.token_type))?
        }
        Ok(Box::new(Identifier {
            token: self.current_token.clone(),
            value: self.current_token.literal.clone(),
        }))
    }

    fn parse_integer_literal(&mut self) -> Result<Box<dyn Expression>> {
        Ok(Box::new(IntegerLiteral {
            token: self.current_token.clone(),
            value: self.current_token.literal.parse::<usize>()?,
        }))
    }

    pub fn next_token(&mut self) {
        self.current_token = self.peek_token.clone();
        self.peek_token = self.lexer.next_token().unwrap();
    }

    pub fn parse_program(&mut self) -> Result<Program, Vec<eyre::Report>> {
        let mut program = Program::default();

        let mut errors = Vec::new();
        while !self.current_token_is(TokenType::EOF) {
            match self.parse_statement() {
                Ok(stmt) => {
                    program.statements.push(stmt);
                },
                Err(error) => errors.push(error)
            }
            self.next_token();
        }

        if !errors.is_empty() {
            Err(errors)?;
        }

        Ok(program)
    }

    fn parse_statement(&mut self) -> Result<Box<dyn Statement>> {
        match self.current_token.token_type {
            TokenType::LET => self.parse_let_statement(),
            TokenType::RETURN => self.parse_return_statement(),
            _ => self.parse_expression_statement(),
        }
    }

    fn parse_expression(&mut self, precedence: OperatorPrecedence) -> Result<Box<dyn Expression>> {
        let token_type = self.current_token.token_type;
        let prefix_fn = {
            self.prefix_parse_fns
                .get(&token_type)
                .ok_or(ParserError::PrefixFnMissing(token_type))?
        };

        let mut left_expr = prefix_fn(self)?;

        while !self.peek_token_is(TokenType::SEMICOLON) && precedence < self.peek_precedence()? {
            if let Some(&infix_fn) = self.infix_parse_fns.get(&self.peek_token.token_type) {
                self.next_token();
                left_expr = infix_fn(self, left_expr)?;
            } else {
                return Ok(left_expr);
            }
        }

        Ok(left_expr)
    }

    fn parse_prefix_expression(&mut self) -> Result<Box<dyn Expression>> {
        let token = self.current_token.clone();
        let operator = self.current_token.literal.clone();

        self.next_token();

        let right = self.parse_expression(OperatorPrecedence::PREFIX)?;

        Ok(Box::new(PrefixExpression {
            token,
            operator,
            right,
        }))
    }

    fn parse_infix_expression(&mut self, left: Box<dyn Expression>) -> Result<Box<dyn Expression>> {
        let token = self.current_token.clone();
        let operator = self.current_token.literal.clone();

        let precedence = self.current_precedence();
        self.next_token();
        let right = self.parse_expression(precedence)?;

        Ok(Box::new(InfixExpression {
            token,
            left,
            operator,
            right,
        }))
    }

    fn parse_call_expression(&mut self, function: Box<dyn Expression>) -> Result<Box<dyn Expression>> {
        let token = self.current_token.clone();

        let arguments = self.parse_call_arguments()?;
        
        Ok(Box::new(CallExpression { token, function, arguments }))
    }

    fn parse_grouped_expression(&mut self) -> Result<Box<dyn Expression>> {
        self.next_token();

        let expr = self.parse_expression(OperatorPrecedence::LOWEST)?;

        self.expect_peek(TokenType::RPAREN)?;

        Ok(expr)
    }

    fn parse_let_statement(&mut self) -> Result<Box<dyn Statement>> {
        let token = self.current_token.clone();

        self.expect_peek(TokenType::IDENT)?;
        let name = Identifier::from_token(&self.current_token);

        self.expect_peek(TokenType::ASSIGN)?;

        self.next_token();
        
        let value = self.parse_expression(OperatorPrecedence::LOWEST)?;

        if self.peek_token_is(TokenType::SEMICOLON) {
            self.next_token()
        }

        Ok(Box::new(LetStatement { token, name, value }))
    }

    fn parse_return_statement(&mut self) -> Result<Box<dyn Statement>> {
        let token = self.current_token.clone();

        self.next_token();

        let return_value = self.parse_expression(OperatorPrecedence::LOWEST)?;

        if self.peek_token_is(TokenType::SEMICOLON) {
            self.next_token()
        }

        Ok(Box::new(ReturnStatement {
            token,
            return_value,
        }))
    }

    fn parse_expression_statement(&mut self) -> Result<Box<dyn Statement>> {
        let token = self.current_token.clone();

        let expression = self.parse_expression(OperatorPrecedence::LOWEST)?;

        if self.peek_token_is(TokenType::SEMICOLON) {
            self.next_token();
        }

        Ok(Box::new(ExpressionStatement { token, expression }))
    }

    fn parse_if_expression(&mut self) -> Result<Box<dyn Expression>> {
        let token = self.current_token.clone();

        self.expect_peek(TokenType::LPAREN)?;

        self.next_token();

        let condition = self.parse_expression(OperatorPrecedence::LOWEST)?;

        self.expect_peek(TokenType::RPAREN)?;
        self.expect_peek(TokenType::LBRACE)?;

        let consequence = self.parse_block_statement()?;

        let alternative = if self.peek_token_is(TokenType::ELSE) {
            self.next_token();

            self.expect_peek(TokenType::LBRACE)?;

            Some(self.parse_block_statement()?)
        } else {
            None
        };

        Ok(Box::new(IfExpression { token, condition, consequence, alternative}))
    }

    fn parse_function_literal(&mut self) -> Result<Box<dyn Expression>> {
        let token = self.current_token.clone();

        self.expect_peek(TokenType::LPAREN)?;

        let parameters = self.parse_function_parameters()?;

        self.expect_peek(TokenType::LBRACE)?;

        let body = self.parse_block_statement()?;

        Ok(Box::new(FunctionLiteral { token, parameters, body }))
    }

    fn parse_function_parameters(&mut self) -> Result<Vec<Identifier>> {
        let mut parameters = Vec::new();
        while !self.peek_token_is(TokenType::RPAREN) {
            self.next_token();
            let parse_identifier = self.parse_identifier()?;
            let param = parse_identifier.as_any().downcast_ref::<Identifier>().ok_or(eyre!("Expression is not an identifier"))?;
            parameters.push(param.clone());
            if !self.peek_token_is(TokenType::RPAREN) {
                self.expect_peek(TokenType::COMMA)?;
            }
        }
        self.next_token();

        Ok(parameters)
    }

    fn parse_call_arguments(&mut self) -> Result<Vec<Box<dyn Expression>>> {
        let mut arguments = Vec::new();
        while !self.peek_token_is(TokenType::RPAREN) {
            self.next_token();
            let arg = self.parse_expression(OperatorPrecedence::LOWEST)?;
            arguments.push(arg);
            if !self.peek_token_is(TokenType::RPAREN) {
                self.expect_peek(TokenType::COMMA)?;
            }
        }
        self.next_token();

        Ok(arguments)
    }

    fn parse_block_statement(&mut self) -> Result<BlockStatement> {
        let mut block = BlockStatement {token: self.current_token.clone(), statements: Vec::new()};

        self.next_token();

        while !self.current_token_is(TokenType::RBRACE) && !self.current_token_is(TokenType::EOF) {
            let stmt = self.parse_statement()?;
            block.statements.push(stmt);
            self.next_token();
        }

        Ok(block)
    }

    fn parse_boolean(&mut self) -> Result<Box<dyn Expression>> {
        Ok(Box::new(Boolean {
            token: self.current_token.clone(),
            value: self.current_token_is(TokenType::TRUE),
        }))
    }

    fn parse_unexpected_eof(&mut self) -> Result<Box<dyn Expression>> {
        Err(ParserError::ReachedEndOfStream)?
    }

    fn current_token_is(&self, check_type: TokenType) -> bool {
        self.current_token.token_type == check_type
    }

    fn peek_token_is(&self, check_type: TokenType) -> bool {
        self.peek_token.token_type == check_type
    }

    fn expect_peek(&mut self, expected: TokenType) -> Result<()> {
        if self.peek_token_is(expected) {
            self.next_token();
            Ok(())
        } else {
            Err(ParserError::UnexpectedToken(expected, self.peek_token.token_type))?
        }
    }

    fn peek_precedence(&self) -> Result<OperatorPrecedence> {
        if self.current_token_is(TokenType::EOF) && self.peek_token_is(TokenType::EOF) {
            Err(ParserError::ReachedEndOfStream)?;
        }
        Ok(self.precedences
            .get(&self.peek_token.token_type)
            .copied()
            .unwrap_or_default())
    }

    fn current_precedence(&self) -> OperatorPrecedence {
        self.precedences
            .get(&self.current_token.token_type)
            .copied()
            .unwrap_or_default()
    }

    fn register_prefix(&mut self, token_type: TokenType, func: PrefixFunc) {
        self.prefix_parse_fns.insert(token_type, func);
    }

    fn register_infix(&mut self, token_type: TokenType, func: InfixFunc) {
        self.infix_parse_fns.insert(token_type, func);
    }
}

#[cfg(test)]
mod tests {
    use std::usize;

    use super::Parser;
    use crate::ast::{Boolean, CallExpression, FunctionLiteral, IfExpression, InfixExpression};
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

        for (i, &(ident, value)) in [("x", 5usize), ("y", 10), ("foobar", 838383)].iter().enumerate() {
            let stmt = &program.statements[i];
            test_let_statement(stmt, ident, value.into());
        }
    }

    #[test]
    fn test_return_statements() {
        let input = "return 5;
        return 10;
        return 993322;";

        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let return_values = [5usize, 10, 993322];

        let program = parser.parse_program().unwrap();
        check_parser_errors(&parser);

        assert_eq!(program.statements.len(), 3);

        for (i, stmt) in program.statements.iter().enumerate() {
            let return_stmt = stmt.as_any().downcast_ref::<ReturnStatement>();
            assert!(return_stmt.is_some());
            assert_eq!(return_stmt.unwrap().token_literal(), "return");
            test_literal_expression(&return_stmt.unwrap().return_value, return_values[i].into())
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
            OperatorPrecedenceTest {
                input: "a + add(b * c) + d",
                expected: "((a + add((b * c))) + d)",
            },
            OperatorPrecedenceTest {
                input: "add(a, b, 1, 2 * 3, 4 + 5, add(6, 7 * 8))",
                expected: "add(a, b, 1, (2 * 3), (4 + 5), add(6, (7 * 8)))",
            },
            OperatorPrecedenceTest {
                input: "add(a + b + c * d / f + g)",
                expected: "add((((a + b) + ((c * d) / f)) + g))",
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

    #[test]
    fn test_if_else_expression() {
        let input = "if (x < y) { x } else { y }";

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

        assert!(if_stmt.alternative.is_some());

        let alternative = if_stmt.alternative.as_ref().unwrap();

        let alternative = alternative.statements[0].as_any().downcast_ref::<ExpressionStatement>().unwrap();

        test_identifier(&alternative.expression, "y");
    }

    #[test]
    fn test_function_literal() {
        let input = "fn (x, y) { x + y }";

        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);

        let program = parser.parse_program().unwrap();
        check_parser_errors(&parser);

        assert_eq!(program.statements.len(), 1);

        let fn_stmt = program.statements[0]
            .as_any().downcast_ref::<ExpressionStatement>().unwrap()
            .expression.as_any().downcast_ref::<FunctionLiteral>().unwrap();

        for param in &fn_stmt.parameters {
            println!("{param}")
        }
        assert_eq!(fn_stmt.parameters.len(), 2);
        
        let params = fn_stmt.parameters.iter().map(|param| Box::new(param.clone()) as Box<dyn Expression>).collect::<Vec<_>>();

        test_literal_expression(&params[0], "x".into());
        test_literal_expression(&params[1], "y".into());

        assert_eq!(fn_stmt.body.statements.len(), 1);

        let body = fn_stmt.body.statements[0].as_any().downcast_ref::<ExpressionStatement>().unwrap();

        test_infix_expression(&body.expression, "x".into(), "+", "y".into());

    }

    #[test]
    fn test_function_parameters() {
        struct FunctionParametersTest {
            input: &'static str,
            params: Vec<&'static str>,
        }

        let func_param_tests = [
            FunctionParametersTest {
                input: "fn() {};",
                params: vec![],
            },
            FunctionParametersTest {
                input: "fn(x) {};",
                params: vec!["x"],
            },
            FunctionParametersTest {
                input: "fn(x,) {};",
                params: vec!["x"],
            },
            FunctionParametersTest {
                input: "fn(x, y) {};",
                params: vec!["x", "y"],
            },
            FunctionParametersTest {
                input: "fn(x, y,) {};",
                params: vec!["x", "y"],
            },
            FunctionParametersTest {
                input: "fn(x, y, z) {};",
                params: vec!["x", "y", "z"],
            },
        ];

        for test in &func_param_tests {
            let lexer = Lexer::new(test.input);
            let mut parser = Parser::new(lexer);
    
            let program = parser.parse_program().unwrap();
            check_parser_errors(&parser);
    
            assert_eq!(program.statements.len(), 1);

            let fn_stmt = program.statements[0]
            .as_any().downcast_ref::<ExpressionStatement>().unwrap()
            .expression.as_any().downcast_ref::<FunctionLiteral>().unwrap();

            for param in &fn_stmt.parameters {
                println!("{param}")
            }

            assert_eq!(fn_stmt.parameters.len(), test.params.len());

            for (result, expected) in fn_stmt.parameters.iter().zip(&test.params) {
                assert_eq!(&result.value, expected);
            }
        }
    }

    #[test]
    fn test_call_expression() {
        let input = "add (1, 2 * 3, 4 + 5)";

        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);

        let program = parser.parse_program().unwrap();
        check_parser_errors(&parser);

        assert_eq!(program.statements.len(), 1);

        let call_expr = program.statements[0]
            .as_any().downcast_ref::<ExpressionStatement>().unwrap()
            .expression.as_any().downcast_ref::<CallExpression>().unwrap();

        assert_eq!(call_expr.arguments.len(), 3);
        
        let params = &call_expr.arguments;

        test_literal_expression(&params[0], 1.into());
        test_infix_expression(&params[1], 2.into(), "*", 3.into());
        test_infix_expression(&params[2], 4.into(), "+", 5.into());
    }

    fn test_let_statement(statement: &Box<dyn Statement>, name: &str, value: ExpectedLiteral) {
        assert_eq!(statement.token_literal(), "let");
        let let_statement = statement.as_any().downcast_ref::<LetStatement>();
        assert!(let_statement.is_some());
        assert_eq!(let_statement.unwrap().name.value, name);
        assert_eq!(let_statement.unwrap().name.token_literal(), name);
        test_literal_expression(&let_statement.unwrap().value, value)
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
