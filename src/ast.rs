use crate::token::{self, Token};
use std::any::Any;

pub trait Node: std::fmt::Debug + std::fmt::Display {
    fn token_literal(&self) -> &str;
    fn as_any(&self) -> &dyn Any;
}

pub trait Statement: Node {
}

pub trait Expression: Node {
}

#[derive(Debug, Default)]
pub struct Program {
    pub statements: Vec<Box<dyn Statement>>,
}

impl Node for Program {
    fn token_literal(&self) -> &str {
        if self.statements.len() == 0 {
            return "";
        }

        return self.statements[0].token_literal()
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl std::fmt::Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for stmt in &self.statements {
            write!(f, "{}", stmt)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct LetStatement {
    pub token: token::Token,
    pub name: Identifier,
    pub value: Box<dyn Expression>,
}

impl Node for LetStatement {
    fn token_literal(&self) -> &str {
        return &self.token.literal;
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Statement for LetStatement {}

impl std::fmt::Display for LetStatement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {} = {};", self.token_literal(), self.name, self.value)
    }
}

#[derive(Debug)]
pub struct ReturnStatement {
    pub token: token::Token,
    pub return_value: Box<dyn Expression>,
}

impl Node for ReturnStatement {
    fn token_literal(&self) -> &str {
        return &self.token.literal;
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Statement for ReturnStatement {}

impl std::fmt::Display for ReturnStatement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {};", self.token_literal(), self.return_value)
    }
}

#[derive(Debug)]
pub struct ExpressionStatement {
    pub token: token::Token,
    pub expression: Box<dyn Expression>,
}

impl Node for ExpressionStatement {
    fn token_literal(&self) -> &str {
        return &self.token.literal;
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Statement for ExpressionStatement {}

impl std::fmt::Display for ExpressionStatement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.expression)
    }
}

#[derive(Debug)]
pub struct Identifier {
    pub token: token::Token,
    pub value: String,
}

impl Node for Identifier {
    fn token_literal(&self) -> &str {
        return &self.token.literal;
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Expression for Identifier {}

impl std::fmt::Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(Debug)]
pub struct IntegerLiteral {
    pub token: token::Token,
    pub value: usize,
}

impl Node for IntegerLiteral {
    fn token_literal(&self) -> &str {
        return &self.token.literal;
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Expression for IntegerLiteral {}

impl std::fmt::Display for IntegerLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl Identifier {
    pub fn from_token(token: &Token) -> Self {
        Self {
            token: token.clone(),
            value: token.literal.clone(),
        }
    }
}

mod tests {
    use crate::token::{self, Token, TokenType};

    use super::{LetStatement, Program, Statement};

    #[test]
    fn test_string() {
        let program: Program = Program {
            statements: vec![Box::new(
                LetStatement {
                    token: Token::new(TokenType::LET, "let"),
                    name: super::Identifier { token:Token::new(TokenType::IDENT, "myVar"), value: "myVar".into() },
                    value: Box::new(super::Identifier { token:Token::new(TokenType::IDENT, "anotherVar"), value: "anotherVar".into() }),
                }
            )],
        };

        assert_eq!(format!("{}", program), "let myVar = anotherVar;")
    }
}