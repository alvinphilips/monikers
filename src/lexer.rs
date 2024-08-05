use core::str;

use crate::token::{Token, TokenType};

#[derive(Default, Debug)]
pub struct Lexer {
    input: String,
    position: usize,
    read_position: usize,
    character: u8,
}

impl Lexer {
    pub fn new(input: &str) -> Self {
        let mut l = Self {
            input: input.into(),
            ..Default::default()
        };
        l.read_char();
        l
    }

    pub fn next_token(&mut self) -> Option<Token> {
        self.skip_whitespace();

        let token = match self.character {
            b'\0' => Some(Self::new_token(TokenType::EOF, self.character)),
            b'=' => {
                if self.peek_char() == b'=' {
                    let ch = self.character;
                    self.read_char();
                    Some(Token::new(TokenType::EQ, str::from_utf8(&[ch, self.character]).unwrap()))
                } else {
                    Some(Self::new_token(TokenType::ASSIGN, self.character))
                }
            },
            b'+' => Some(Self::new_token(TokenType::PLUS, self.character)),
            b'-' => Some(Self::new_token(TokenType::MINUS, self.character)),
            b'!' => {
                if self.peek_char() == b'=' {
                    let ch = self.character;
                    self.read_char();
                    Some(Token::new(TokenType::NE, str::from_utf8(&[ch, self.character]).unwrap()))
                } else {
                    Some(Self::new_token(TokenType::BANG, self.character))
                }
            },
            b'*' => Some(Self::new_token(TokenType::ASTERISK, self.character)),
            b'/' => Some(Self::new_token(TokenType::SLASH, self.character)),
            b'<' => Some(Self::new_token(TokenType::LT, self.character)),
            b'>' => Some(Self::new_token(TokenType::GT, self.character)),
            b'(' => Some(Self::new_token(TokenType::LPAREN, self.character)),
            b')' => Some(Self::new_token(TokenType::RPAREN, self.character)),
            b'{' => Some(Self::new_token(TokenType::LBRACE, self.character)),
            b'}' => Some(Self::new_token(TokenType::RBRACE, self.character)),
            b',' => Some(Self::new_token(TokenType::COMMA, self.character)),
            b';' => Some(Self::new_token(TokenType::SEMICOLON, self.character)),
            _ => {
                if Self::is_letter(self.character) {
                    let literal = self.read_identifier();
                    let tok_type = TokenType::lookup_ident(&literal);
                    Some(Token::new(tok_type, &literal))
                } else if self.character.is_ascii_digit() {
                    Some(Token::new(TokenType::INT, &self.read_number()))
                } else {
                    None
                }
            }
        };

        self.read_char();

        token
    }

    fn read_char(&mut self) {
        if self.read_position >= self.input.len() {
            self.character = 0
        } else {
            self.character = self.input.as_bytes()[self.read_position]
        }

        self.position = self.read_position;
        self.read_position += 1;
    }

    fn peek_char(&self) -> u8 {
        if self.read_position >= self.input.len() {
            return 0;
        }

        return self.input.as_bytes()[self.read_position];
    }

    fn read_identifier(&mut self) -> String {
        let pos = self.position;
        while Self::is_letter(self.character) {
            self.read_char()
        }
        self.read_position -= 1;

        return str::from_utf8(&self.input.as_bytes()[pos..self.position]).unwrap().into();
    }

    fn read_number(&mut self) -> String {
        let pos = self.position;
        while self.character.is_ascii_digit() {
            self.read_char()
        }
        self.read_position -= 1;

        return str::from_utf8(&self.input.as_bytes()[pos..self.position]).unwrap().into();
    }

    fn new_token(token_type: TokenType, character: u8) -> Token {
        Token::new(token_type, str::from_utf8(&[character]).unwrap())
    }

    fn is_letter(character: u8) -> bool {
        return character.is_ascii_alphabetic() || character == b'_';
    }

    fn skip_whitespace(&mut self) {
        while let Some(_) = match self.character {
            b' ' | b'\t' | b'\n' | b'\r' => Some(self.character),
            _ => None
        } {
            self.read_char()
        }
    }
}

mod tests {
    #[test]
    fn test_next_token() {
        use crate::token::{Token, TokenType};
        let input = r"let five = 5;
        let ten = 10;

        let add = fn ( x, y ) {
            x + y;
        };
        
        let result = add(five, ten);
        !-/*;
        5 < 10 > 5;

        if (5 < 10) {
            return true;
        } else {
            return false;
        }

        10 == 10;
        10 != 9;
        ";

        let expected_tokens = [
            Token::new(TokenType::LET, "let"),
            Token::new(TokenType::IDENT, "five"),
            Token::new(TokenType::ASSIGN, "="),
            Token::new(TokenType::INT, "5"),
            Token::new(TokenType::SEMICOLON, ";"),
            Token::new(TokenType::LET, "let"),
            Token::new(TokenType::IDENT, "ten"),
            Token::new(TokenType::ASSIGN, "="),
            Token::new(TokenType::INT, "10"),
            Token::new(TokenType::SEMICOLON, ";"),
            Token::new(TokenType::LET, "let"),
            Token::new(TokenType::IDENT, "add"),
            Token::new(TokenType::ASSIGN, "="),
            Token::new(TokenType::FUNCTION, "fn"),
            Token::new(TokenType::LPAREN, "("),
            Token::new(TokenType::IDENT, "x"),
            Token::new(TokenType::COMMA, ","),
            Token::new(TokenType::IDENT, "y"),
            Token::new(TokenType::RPAREN, ")"),
            Token::new(TokenType::LBRACE, "{"),
            Token::new(TokenType::IDENT, "x"),
            Token::new(TokenType::PLUS, "+"),
            Token::new(TokenType::IDENT, "y"),
            Token::new(TokenType::SEMICOLON, ";"),
            Token::new(TokenType::RBRACE, "}"),
            Token::new(TokenType::SEMICOLON, ";"),
            Token::new(TokenType::LET, "let"),
            Token::new(TokenType::IDENT, "result"),
            Token::new(TokenType::ASSIGN, "="),
            Token::new(TokenType::IDENT, "add"),
            Token::new(TokenType::LPAREN, "("),
            Token::new(TokenType::IDENT, "five"),
            Token::new(TokenType::COMMA, ","),
            Token::new(TokenType::IDENT, "ten"),
            Token::new(TokenType::RPAREN, ")"),
            Token::new(TokenType::SEMICOLON, ";"),
            Token::new(TokenType::BANG, "!"),
            Token::new(TokenType::MINUS, "-"),
            Token::new(TokenType::SLASH, "/"),
            Token::new(TokenType::ASTERISK, "*"),
            Token::new(TokenType::SEMICOLON, ";"),
            Token::new(TokenType::INT, "5"),
            Token::new(TokenType::LT, "<"),
            Token::new(TokenType::INT, "10"),
            Token::new(TokenType::GT, ">"),
            Token::new(TokenType::INT, "5"),
            Token::new(TokenType::SEMICOLON, ";"),
            Token::new(TokenType::IF, "if"),
            Token::new(TokenType::LPAREN, "("),
            Token::new(TokenType::INT, "5"),
            Token::new(TokenType::LT, "<"),
            Token::new(TokenType::INT, "10"),
            Token::new(TokenType::RPAREN, ")"),
            Token::new(TokenType::LBRACE, "{"),
            Token::new(TokenType::RETURN, "return"),
            Token::new(TokenType::TRUE, "true"),
            Token::new(TokenType::SEMICOLON, ";"),
            Token::new(TokenType::RBRACE, "}"),
            Token::new(TokenType::ELSE, "else"),
            Token::new(TokenType::LBRACE, "{"),
            Token::new(TokenType::RETURN, "return"),
            Token::new(TokenType::FALSE, "false"),
            Token::new(TokenType::SEMICOLON, ";"),
            Token::new(TokenType::RBRACE, "}"),
            Token::new(TokenType::INT, "10"),
            Token::new(TokenType::EQ, "=="),
            Token::new(TokenType::INT, "10"),
            Token::new(TokenType::SEMICOLON, ";"),
            Token::new(TokenType::INT, "10"),
            Token::new(TokenType::NE, "!="),
            Token::new(TokenType::INT, "9"),
            Token::new(TokenType::SEMICOLON, ";"),
        ];

        let mut l = super::Lexer::new(input);

        for expected in expected_tokens {
            let tok: Token = l.next_token().expect(&format!("Expected Some(Token {:?}, Literal: {}), Got None.", expected.token_type, expected.literal));

            println!("{}, {}", tok.literal, expected.literal);
            assert_eq!(tok.token_type, expected.token_type);
            assert_eq!(tok.literal, expected.literal);
        }
    }
}