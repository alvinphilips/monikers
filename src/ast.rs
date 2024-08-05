use crate::token::{self, Token};
use std::any::Any;

pub trait Node: std::fmt::Debug {
    fn token_literal(&self) -> String;
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
    fn token_literal(&self) -> String {
        if self.statements.len() == 0 {
            return String::new();
        }

        return self.statements[0].token_literal()
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

#[derive(Debug)]
pub struct LetStatement {
    pub token: token::Token,
    pub name: Identifier,
    pub value: Box<dyn Expression>,
}

impl Node for LetStatement {
    fn token_literal(&self) -> String {
        return self.token.literal.clone();
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}
impl Statement for LetStatement {}

#[derive(Debug)]
pub struct ReturnStatement {
    pub token: token::Token,
    pub return_value: Box<dyn Expression>,
}

impl Node for ReturnStatement {
    fn token_literal(&self) -> String {
        return self.token.literal.clone();
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}
impl Statement for ReturnStatement {}

#[derive(Debug)]
pub struct Identifier {
    pub token: token::Token,
    pub value: String,
}

impl Node for Identifier {
    fn token_literal(&self) -> String {
        return self.token.literal.clone();
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Expression for Identifier {}

impl Identifier {
    pub fn from_token(token: &Token) -> Self {
        Self {
            token: token.clone(),
            value: token.literal.clone(),
        }
    }
}