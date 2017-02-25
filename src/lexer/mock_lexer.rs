use std::cell::Cell;
use lexer::Lexer;
use tokens::*;
use errors::SyntaxError;

pub struct MockLexer {
    tokens: Vec<(TokenType, TokenValue)>,
    pos: Cell<usize>,
}

impl Lexer for MockLexer {
    fn get_next_token(&self) -> Result<Token, SyntaxError> {
        let pos = self.pos.get();
        self.pos.set(pos + 1);
        if pos + 1 > self.tokens.len() {
            Ok(Token::new(TokenType::Eof, None, (pos, pos + 1)))
        } else {
            match self.tokens[pos].1 {
                TokenValue::Empty => {
                    Ok(Token::new(self.tokens[pos].0.clone(), None, (pos, pos + 1)))
                }
                _ => {
                    Ok(Token::new(self.tokens[pos].0.clone(),
                                  Some(self.tokens[pos].1.clone()),
                                  (pos, pos + 1)))
                }
            }
        }
    }

    fn get_position(&self) -> usize {
        self.pos.get()
    }
}

impl MockLexer {
    pub fn new(tokens: Vec<(TokenType, TokenValue)>) -> MockLexer {
        MockLexer {
            tokens: tokens,
            pos: Cell::new(0),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lexer::Lexer;

    #[test]
    fn mocklexer_returns_first_token_when_calling_get_next_token_for_the_first_time() {
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(42))];
        let mocklexer = MockLexer::new(tokens);
        let token = mocklexer.get_next_token().unwrap();
        assert_eq!(token.token_type, TokenType::Integer);
        match token.value.unwrap() {
            TokenValue::Integer(value) => assert_eq!(42, value),
            _ => assert!(false),
        }
    }

    #[test]
    fn mocklexer_returns_second_token_when_calling_get_next_token_for_the_second_time() {
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(42)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus))];
        let mocklexer = MockLexer::new(tokens);
        let _tmp = mocklexer.get_next_token().unwrap();
        let token = mocklexer.get_next_token().unwrap();
        assert_eq!(token.token_type, TokenType::Operator);
        match token.value.unwrap() {
            TokenValue::Operator(value) => assert_eq!(OperatorType::Plus, value),
            _ => assert!(false),
        }
    }

    #[test]
    fn mocklexer_returns_token_with_value_none_when_encountering_novalue() {
        let tokens = vec![(TokenType::LParen, TokenValue::Empty)];
        let mocklexer = MockLexer::new(tokens);
        let token = mocklexer.get_next_token().unwrap();
        assert_eq!(token.token_type, TokenType::LParen);
        assert!(token.value.is_none());
    }

    #[test]
    fn mocklexer_returns_eof_when_no_more_tokens_are_available() {
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(42))];
        let mocklexer = MockLexer::new(tokens);
        let _tmp = mocklexer.get_next_token().unwrap();
        let token = mocklexer.get_next_token().unwrap();
        assert_eq!(token.token_type, TokenType::Eof);
    }
}
