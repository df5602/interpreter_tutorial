use std::cell::Cell;
use tokens::*;
use errors::SyntaxError;
use lexer::Lexer;

#[derive(Debug)]
pub struct PascalLexer {
    chars: Vec<char>,
    pos: Cell<usize>,
}

impl Lexer for PascalLexer {
    // Returns the next token in the input
    // Result is the token, if possible, Error "Invalid token" otherwise
    fn get_next_token(&self) -> Result<Token, SyntaxError> {
        // Advance to the next non-whitespace character
        self.skip_whitespace();

        let pos = self.pos.get();

        // Return EOF when we have reached the end of the input
        if pos + 1 > self.chars.len() {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::Eof, None, (pos, pos + 1)));
        }

        let current_char = self.chars[pos];

        // Return INTEGER when the next character is a digit
        if current_char.is_digit(10) {
            let value = self.get_integer();
            return Ok(Token::new(TokenType::Integer,
                                 Some(TokenValue::Integer(value)),
                                 (pos, self.pos.get())));
        }

        // Return PLUS when the next character is '+'
        if current_char == '+' {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::Operator,
                                 Some(TokenValue::Operator(OperatorType::Plus)),
                                 (pos, pos + 1)));
        }

        // Return MINUS when the next character is '-'
        if current_char == '-' {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::Operator,
                                 Some(TokenValue::Operator(OperatorType::Minus)),
                                 (pos, pos + 1)));
        }

        // Return TIMES when the next character is '*'
        if current_char == '*' {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::Operator,
                                 Some(TokenValue::Operator(OperatorType::Times)),
                                 (pos, pos + 1)));
        }

        // Return DIVISION when the next character is '/'
        if current_char == '/' {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::Operator,
                                 Some(TokenValue::Operator(OperatorType::Division)),
                                 (pos, pos + 1)));
        }

        // Return LPAREN when the next character is '('
        if current_char == '(' {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::LParen, None, (pos, pos + 1)));
        }

        // Return RPAREN when the next character is ')'
        if current_char == ')' {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::RParen, None, (pos, pos + 1)));
        }

        // Current character didn't match any known token, return error
        Err(SyntaxError {
            msg: "Invalid token".to_string(),
            position: (pos, pos + 1),
        })
    }

    fn get_position(&self) -> usize {
        self.pos.get()
    }
}

impl PascalLexer {
    pub fn new(text: &str) -> PascalLexer {
        PascalLexer {
            chars: text.chars().collect(),
            pos: Cell::new(0),
        }
    }

    // Returns a multi-digit (unsigned, base 10) integer
    // Precondition: First character is digit
    fn get_integer(&self) -> u64 {
        let mut pos = self.pos.get();
        let mut current_char = self.chars[pos];
        assert!(current_char.is_digit(10));
        let mut result = current_char.to_digit(10).unwrap() as u64;

        loop {
            pos += 1;

            if pos + 1 > self.chars.len() {
                break;
            }

            current_char = self.chars[pos];
            if current_char.is_digit(10) {
                result = result * 10 + (current_char.to_digit(10).unwrap() as u64);
            } else {
                break;
            }
        }

        self.pos.set(pos);
        result
    }

    // Advances the position to the next non-whitespace character
    fn skip_whitespace(&self) {
        let mut pos = self.pos.get();

        loop {
            // Terminate if we have reached the end of the input
            if pos + 1 > self.chars.len() {
                break;
            }

            // Read character at current position
            let current_char = self.chars[pos];

            // Is current character whitespace character?
            if current_char.is_whitespace() {
                // Advance position and continue
                pos += 1;
            } else {
                break;
            }
        }

        // Set new position
        self.pos.set(pos);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokens::*;
    use lexer::Lexer;

    #[test]
    fn lexer_get_next_token_returns_eof_when_input_is_empty() {
        let lexer = PascalLexer::new(&"".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Eof, next_token.token_type);
    }

    #[test]
    fn lexer_get_next_token_returns_token_or_error_when_input_is_not_empty() {
        let lexer = PascalLexer::new(&"3+5".to_string());
        let next_token = lexer.get_next_token();
        match next_token {
            Ok(token) => assert!(token.token_type != TokenType::Eof),
            Err(_) => assert!(true),
        }
    }

    #[test]
    fn lexer_get_next_token_returns_integer_when_input_is_digit() {
        let lexer = PascalLexer::new(&"3".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Integer, next_token.token_type);
    }

    #[test]
    fn lexer_get_next_token_returns_integer_value_when_input_is_digit() {
        let lexer = PascalLexer::new(&"3".to_string());
        let next_token = lexer.get_next_token().unwrap();
        match next_token.value.unwrap() {
            TokenValue::Integer(value) => assert_eq!(3, value),
            _ => assert!(false),
        }
    }

    #[test]
    fn lexer_get_next_token_returns_next_token_when_called_second_time() {
        let lexer = PascalLexer::new(&"+3".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Operator, next_token.token_type);
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Integer, next_token.token_type);
    }

    #[test]
    fn lexer_get_next_token_returns_plus_when_input_is_plus() {
        let lexer = PascalLexer::new(&"+".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Operator, next_token.token_type);
    }

    #[test]
    fn lexer_get_next_token_returns_operator_value_plus_when_input_is_operator_plus() {
        let lexer = PascalLexer::new(&"+".to_string());
        let next_token = lexer.get_next_token().unwrap();
        match next_token.value.unwrap() {
            TokenValue::Operator(value) => assert_eq!(OperatorType::Plus, value),
            _ => assert!(false),
        }
    }

    #[test]
    fn lexer_get_next_token_returns_minus_when_input_is_minus() {
        let lexer = PascalLexer::new(&"-".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Operator, next_token.token_type);
    }

    #[test]
    fn lexer_get_next_token_returns_operator_value_minus_when_input_is_operator_minus() {
        let lexer = PascalLexer::new(&"-".to_string());
        let next_token = lexer.get_next_token().unwrap();
        match next_token.value.unwrap() {
            TokenValue::Operator(value) => assert_eq!(OperatorType::Minus, value),
            _ => assert!(false),
        }
    }

    #[test]
    fn lexer_get_next_token_returns_times_when_input_is_times() {
        let lexer = PascalLexer::new(&"*".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Operator, next_token.token_type);
    }

    #[test]
    fn lexer_get_next_token_returns_operator_value_times_when_input_is_operator_times() {
        let lexer = PascalLexer::new(&"*".to_string());
        let next_token = lexer.get_next_token().unwrap();
        match next_token.value.unwrap() {
            TokenValue::Operator(value) => assert_eq!(OperatorType::Times, value),
            _ => assert!(false),
        }
    }

    #[test]
    fn lexer_get_next_token_returns_division_when_input_is_division() {
        let lexer = PascalLexer::new(&"/".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Operator, next_token.token_type);
    }

    #[test]
    fn lexer_get_next_token_returns_operator_value_division_when_input_is_operator_division() {
        let lexer = PascalLexer::new(&"/".to_string());
        let next_token = lexer.get_next_token().unwrap();
        match next_token.value.unwrap() {
            TokenValue::Operator(value) => assert_eq!(OperatorType::Division, value),
            _ => assert!(false),
        }
    }

    #[test]
    fn lexer_get_next_token_returns_error_when_input_is_letter() {
        let lexer = PascalLexer::new(&"a".to_string());
        let next_token = lexer.get_next_token();
        match next_token {
            Ok(_) => assert!(false),
            Err(_) => assert!(true),
        }
    }

    #[test]
    fn lexer_get_integer_returns_multi_digit_integer() {
        let lexer = PascalLexer::new(&"123".to_string());
        let result = lexer.get_integer();
        assert_eq!(123, result);
    }

    #[test]
    fn lexer_get_integer_should_advance_position_correctly() {
        let lexer = PascalLexer::new(&"123".to_string());
        let _result = lexer.get_integer();
        assert_eq!(3, lexer.pos.get());
    }

    #[test]
    fn lexer_get_integer_should_only_advance_as_long_as_there_are_more_digits() {
        let lexer = PascalLexer::new(&"12a".to_string());
        let result = lexer.get_integer();
        assert_eq!(12, result);
        assert_eq!(2, lexer.pos.get());
    }

    #[test]
    fn lexer_skip_whitespace_should_skip_all_whitespaces_until_eof() {
        let lexer = PascalLexer::new(&"  \n".to_string());
        lexer.skip_whitespace();
        assert_eq!(3, lexer.pos.get());
    }

    #[test]
    fn lexer_skip_whitespace_should_skip_all_whitespaces_until_first_non_whitespace_char() {
        let lexer = PascalLexer::new(&"  3".to_string());
        lexer.skip_whitespace();
        assert_eq!(2, lexer.pos.get());
    }

    #[test]
    fn lexer_skip_whitespace_should_not_skip_non_whitespace_characters() {
        let lexer = PascalLexer::new(&"123".to_string());
        lexer.skip_whitespace();
        assert_eq!(0, lexer.pos.get());
    }

    #[test]
    fn lexer_get_next_token_returns_left_parenthesis_when_input_is_left_parenthesis() {
        let lexer = PascalLexer::new(&"(".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::LParen, next_token.token_type);
    }

    #[test]
    fn lexer_get_next_token_returns_right_parenthesis_when_input_is_right_parenthesis() {
        let lexer = PascalLexer::new(&")".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::RParen, next_token.token_type);
    }
}