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
            Ok(Token::new(self.tokens[pos].0.clone(),
                          Some(self.tokens[pos].1.clone()),
                          (pos, pos + 1)))
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
    use tokens::*;

    #[test]
    fn mocklexer_returns_first_token_when_calling_get_next_token_for_the_first_time() {
        let tokens = vec![(TokenType::Integer, TokenValue::IntegerValue(42))];
        let mocklexer = MockLexer::new(tokens);
        let token = mocklexer.get_next_token().unwrap();
        assert_eq!(token.token_type, TokenType::Integer);
        match token.value.unwrap() {
            TokenValue::IntegerValue(value) => assert_eq!(42, value),
            TokenValue::OperatorValue(_) => assert!(false),
        }
    }

    #[test]
    fn mocklexer_returns_second_token_when_calling_get_next_token_for_the_second_time() {
        let tokens = vec![(TokenType::Integer, TokenValue::IntegerValue(42)),
                          (TokenType::Operator, TokenValue::OperatorValue(OperatorType::Plus))];
        let mocklexer = MockLexer::new(tokens);
        let _tmp = mocklexer.get_next_token().unwrap();
        let token = mocklexer.get_next_token().unwrap();
        assert_eq!(token.token_type, TokenType::Operator);
        match token.value.unwrap() {
            TokenValue::IntegerValue(_) => assert!(false),
            TokenValue::OperatorValue(value) => assert_eq!(OperatorType::Plus, value),
        }
    }

    #[test]
    fn mocklexer_returns_eof_when_no_more_tokens_are_available() {
        let tokens = vec![(TokenType::Integer, TokenValue::IntegerValue(42))];
        let mocklexer = MockLexer::new(tokens);
        let _tmp = mocklexer.get_next_token().unwrap();
        let token = mocklexer.get_next_token().unwrap();
        assert_eq!(token.token_type, TokenType::Eof);
    }
}
