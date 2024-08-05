use std::collections::HashMap;
use lazy_static::lazy_static;

#[derive(PartialEq, Clone, Copy, Debug, Default)]
pub enum TokenType {
    #[default]
    ILLEGAL,
    EOF,

    // Identifiers and Literals
    IDENT,
    INT,

    // Operators
    ASSIGN,
    PLUS,
    MINUS,
    BANG,
    ASTERISK,
    SLASH,

    LT,
    GT,
    EQ,
    NE,

    // Delimiters
    COMMA,
    SEMICOLON,

    LPAREN,
    RPAREN,
    LBRACE,
    RBRACE,

    // Keywords
    FUNCTION,
    LET,
    TRUE,
    FALSE,
    IF,
    ELSE,
    RETURN,
}

impl std::fmt::Display for TokenType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ILLEGAL => write!(f, "ILLEGAL"),
            Self::EOF => write!(f, "EOF"),
            Self::IDENT => write!(f, "IDENT"),
            Self::INT => write!(f, "INT"),
            Self::ASSIGN => write!(f, "="),
            Self::PLUS => write!(f, "+"),
            Self::COMMA => write!(f, ","),
            Self::SEMICOLON => write!(f, ";"),
            Self::LPAREN => write!(f, "("),
            Self::RPAREN => write!(f, ")"),
            Self::LBRACE => write!(f, "{{"),
            Self::RBRACE => write!(f, "}}"),
            Self::FUNCTION => write!(f, "FUNCTION"),
            Self::LET => write!(f, "LET"),
            Self::MINUS => write!(f, "-"),
            Self::BANG => write!(f, "!"),
            Self::ASTERISK => write!(f, "*"),
            Self::SLASH => write!(f, "/"),
            Self::LT => write!(f, "<"),
            Self::GT => write!(f, ">"),
            Self::EQ => write!(f, "=="),
            Self::NE => write!(f, "!="),
            Self::TRUE => write!(f, "TRUE"),
            Self::FALSE => write!(f, "FALSE"),
            Self::IF => write!(f, "IF"),
            Self::ELSE => write!(f, "ELSE"),
            Self::RETURN => write!(f, "RETURN"),
        }
    }
}

lazy_static! {
    static ref Keywords: HashMap<String, TokenType> = {
        let mut k = HashMap::new();
        k.insert("fn".to_string(), TokenType::FUNCTION);
        k.insert("let".to_string(), TokenType::LET);
        k.insert("if".to_string(), TokenType::IF);
        k.insert("else".to_string(), TokenType::ELSE);
        k.insert("return".to_string(), TokenType::RETURN);
        k.insert("true".to_string(), TokenType::TRUE);
        k.insert("false".to_string(), TokenType::FALSE);
        k
    };
}

impl TokenType {
    pub fn lookup_ident(identifier: &str) -> TokenType {
        *Keywords.get(identifier).unwrap_or(&Self::IDENT)
    }
}

#[derive(Debug, Clone, Default)]
pub struct Token {
    pub token_type: TokenType,
    pub literal: String,
}

impl Token {
    pub fn new(token_type: TokenType, literal: &str) -> Self {
        Token { token_type, literal: literal.into() }
    }
}