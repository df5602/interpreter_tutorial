//! This module contains a lexer that recognizes `Token`s in a Pascal program.
use std::cell::Cell;
use std::i64;
use tokens::*;
use errors::SyntaxError;
use lexer::Lexer;

#[derive(Debug)]
/// Lexer that recognizes `Token`s in a Pascal program.
/// Implements `Lexer` trait.
pub struct PascalLexer {
    chars: Vec<char>,
    pos: Cell<usize>,
}

impl Lexer for PascalLexer {
    /// Returns the next token in the input
    /// Result is the token, if possible, Error "Invalid token" otherwise
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
            let value = self.get_integer()?;
            return Ok(Token::new(TokenType::Integer,
                                 Some(TokenValue::Integer(value)),
                                 (pos, self.pos.get())));
        }

        // Return IDENTIFIER or keyword when the next character is alphabetic
        // or an underscore.
        if current_char.is_alphabetic() || current_char == '_' {
            return self.recognize_identifier_or_keyword();
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

        // Return DOT when the next character is '.'
        if current_char == '.' {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::Dot, None, (pos, pos + 1)));
        }

        // Return SEMICOLON when the next character is ';'
        if current_char == ';' {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::Semicolon, None, (pos, pos + 1)));
        }

        // Return ASSIGN when the next two characters are ':='
        if current_char == ':' {
            if let Some('=') = self.peek(1) {
                self.pos.set(pos + 2);
                return Ok(Token::new(TokenType::Assign, None, (pos, pos + 2)));
            }
        }

        // Current character didn't match any known token, return error
        Err(SyntaxError {
            msg: "Invalid token".to_string(),
            position: (pos, pos + 1),
        })
    }

    /// Returns actual position in the input
    fn get_position(&self) -> usize {
        self.pos.get()
    }
}

impl PascalLexer {
    /// Constructs new `PascalLexer` that tokenizes the input passed in `text`.
    pub fn new(text: &str) -> PascalLexer {
        PascalLexer {
            chars: text.chars().collect(),
            pos: Cell::new(0),
        }
    }

    /// Returns a multi-digit (unsigned, base 10) integer
    /// Precondition: First character is digit
    fn get_integer(&self) -> Result<i64, SyntaxError> {
        let mut pos = self.pos.get();
        let start_pos = pos;
        let mut current_char = self.chars[pos];
        assert!(current_char.is_digit(10));
        let mut result = current_char.to_digit(10).unwrap() as i64;

        loop {
            pos += 1;

            if pos + 1 > self.chars.len() {
                break;
            }

            current_char = self.chars[pos];
            if current_char.is_digit(10) {
                let current_digit = current_char.to_digit(10).unwrap() as i64;
                if result > (i64::MAX - current_digit) / 10 {
                    return Err(SyntaxError {
                        msg: "Integer overflow (exceeds storage capacity of signed 64-bit integer)"
                            .to_string(),
                        position: (start_pos, pos),
                    });
                }
                result = result * 10 + current_digit;
            } else {
                break;
            }
        }

        self.pos.set(pos);
        Ok(result)
    }

    /// Recognizes an identifier or a keyword
    /// * Returns a keyword `Token` if the input matches a keyword
    /// * Returns an IDENTIFIER `Token` otherwise
    fn recognize_identifier_or_keyword(&self) -> Result<Token, SyntaxError> {
        let start_pos = self.pos.get();
        let mut pos = start_pos;
        let mut current_char = self.chars[pos];
        assert!(current_char.is_alphabetic() || current_char == '_');
        let mut result = current_char.to_string();

        loop {
            pos += 1;

            if pos + 1 > self.chars.len() {
                break;
            }

            current_char = self.chars[pos];
            if current_char.is_alphanumeric() {
                result.push(current_char);
            } else {
                break;
            }
        }

        self.pos.set(pos);

        // Convert to lower case, since identifiers and keywords are case-insensitive
        result = result.to_lowercase();

        match result.as_ref() {
            "begin" => return Ok(Token::new(TokenType::Begin, None, (start_pos, pos))),
            "end" => return Ok(Token::new(TokenType::End, None, (start_pos, pos))),
            "div" => {
                return Ok(Token::new(TokenType::Operator,
                                     Some(TokenValue::Operator(OperatorType::Division)),
                                     (start_pos, pos)))
            }
            _ => {}
        }

        // Identifier name is stored in a String at the beginning of this function.
        // Moving the following into the match statement leads to problems with the borrow checker.
        Ok(Token::new(TokenType::Identifier,
                      Some(TokenValue::Identifier(result)),
                      (start_pos, pos)))
    }

    /// Advances the position to the next non-whitespace character
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

    /// Peeks `n` characters in front of the current position.
    /// Returns the character `n` positions in front of the current position,
    /// or `None` if end of the input is reached.
    fn peek(&self, n: usize) -> Option<char> {
        let pos = self.pos.get();

        if pos + n + 1 > self.chars.len() {
            None
        } else {
            Some(self.chars[pos + n])
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
        let lexer = PascalLexer::new(&"div".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Operator, next_token.token_type);
    }

    #[test]
    fn lexer_get_next_token_returns_operator_value_division_when_input_is_operator_division() {
        let lexer = PascalLexer::new(&"div".to_string());
        let next_token = lexer.get_next_token().unwrap();
        match next_token.value.unwrap() {
            TokenValue::Operator(value) => assert_eq!(OperatorType::Division, value),
            _ => assert!(false),
        }
    }

    #[test]
    fn lexer_get_integer_returns_multi_digit_integer() {
        let lexer = PascalLexer::new(&"123".to_string());
        let result = lexer.get_integer().unwrap();
        assert_eq!(123, result);
    }

    #[test]
    fn lexer_get_integer_should_advance_position_correctly() {
        let lexer = PascalLexer::new(&"123".to_string());
        let _result = lexer.get_integer().unwrap();
        assert_eq!(3, lexer.pos.get());
    }

    #[test]
    fn lexer_get_integer_should_only_advance_as_long_as_there_are_more_digits() {
        let lexer = PascalLexer::new(&"12a".to_string());
        let result = lexer.get_integer().unwrap();
        assert_eq!(12, result);
        assert_eq!(2, lexer.pos.get());
    }

    #[test]
    fn lexer_get_integer_should_return_error_when_input_is_larger_than_fit_in_i64() {
        let lexer = PascalLexer::new(&"9223372036854775808".to_string());
        let result = lexer.get_integer();
        assert!(result.is_err());
    }

    #[test]
    fn lexer_get_integer_should_return_number_when_input_fits_in_i64() {
        let lexer = PascalLexer::new(&"9223372036854775807".to_string());
        let result = lexer.get_integer().unwrap();
        assert_eq!(9223372036854775807, result);
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
    fn lexer_should_recognize_expressions_that_contain_multi_digit_integer() {
        let lexer = PascalLexer::new(&"44+3".to_string());
        let mut next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Integer, next_token.token_type);
        assert_eq!(44, next_token.value.unwrap().extract_integer_value());
        next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Operator, next_token.token_type);
        assert_eq!(OperatorType::Plus,
                   next_token.value.unwrap().extract_operator_type());
        next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Integer, next_token.token_type);
        assert_eq!(3, next_token.value.unwrap().extract_integer_value());
    }

    #[test]
    fn lexer_should_recognize_expressions_that_begin_with_whitespace_characters() {
        let lexer = PascalLexer::new(&" 2 + 3".to_string());
        let mut next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Integer, next_token.token_type);
        assert_eq!(2, next_token.value.unwrap().extract_integer_value());
        next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Operator, next_token.token_type);
        assert_eq!(OperatorType::Plus,
                   next_token.value.unwrap().extract_operator_type());
        next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Integer, next_token.token_type);
        assert_eq!(3, next_token.value.unwrap().extract_integer_value());
    }

    #[test]
    fn lexer_should_recognize_expressions_that_contain_whitespace_characters() {
        let lexer = PascalLexer::new(&"2 + 3".to_string());
        let mut next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Integer, next_token.token_type);
        assert_eq!(2, next_token.value.unwrap().extract_integer_value());
        next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Operator, next_token.token_type);
        assert_eq!(OperatorType::Plus,
                   next_token.value.unwrap().extract_operator_type());
        next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Integer, next_token.token_type);
        assert_eq!(3, next_token.value.unwrap().extract_integer_value());
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

    #[test]
    fn lexer_get_next_token_returns_dot_token_when_input_is_dot() {
        let lexer = PascalLexer::new(&".".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Dot, next_token.token_type);
    }

    #[test]
    fn lexer_get_next_token_returns_semicolon_token_when_input_is_semicolon() {
        let lexer = PascalLexer::new(&";".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Semicolon, next_token.token_type);
    }

    #[test]
    fn lexer_get_next_token_returns_assign_token_when_input_is_assignment_operator() {
        let lexer = PascalLexer::new(&":=".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Assign, next_token.token_type);
    }

    #[test]
    fn lexer_get_next_token_doesnt_return_assign_token_when_input_is_only_colon() {
        let lexer = PascalLexer::new(&":".to_string());
        let next_token = lexer.get_next_token();
        match next_token {
            Err(_) => assert!(true),
            _ => assert!(false),
        }
    }

    #[test]
    fn lexer_get_next_token_doesnt_ret_assign_tok_when_input_is_colon_not_followed_by_eq_sign() {
        let lexer = PascalLexer::new(&":?".to_string());
        let next_token = lexer.get_next_token();
        match next_token {
            Err(_) => assert!(true),
            _ => assert!(false),
        }
    }

    #[test]
    fn lexer_get_next_token_returns_begin_token_when_input_is_begin_keyword_uppercase() {
        let lexer = PascalLexer::new(&"BEGIN".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Begin, next_token.token_type);
    }

    #[test]
    fn lexer_get_next_token_returns_begin_token_when_input_is_begin_keyword_mixed_case() {
        let lexer = PascalLexer::new(&"beGIN".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Begin, next_token.token_type);
    }

    #[test]
    fn lexer_get_next_token_returns_end_token_when_input_is_end_keyword_uppercase() {
        let lexer = PascalLexer::new(&"END".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::End, next_token.token_type);
    }

    #[test]
    fn lexer_get_next_token_returns_end_token_when_input_is_end_keyword_lowercase() {
        let lexer = PascalLexer::new(&"end".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::End, next_token.token_type);
    }

    #[test]
    fn lexer_get_next_token_returns_identifier_token_when_input_is_string() {
        let lexer = PascalLexer::new(&"number".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Identifier, next_token.token_type);
        match next_token.value.unwrap() {
            TokenValue::Identifier(id) => assert_eq!("number", id),
            _ => assert!(false),
        }
    }

    #[test]
    fn lexer_identifiers_are_case_insensitive() {
        let lexer = PascalLexer::new(&"nUmBeR".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Identifier, next_token.token_type);
        match next_token.value.unwrap() {
            TokenValue::Identifier(id) => assert_eq!("number", id),
            _ => assert!(false),
        }
    }

    #[test]
    fn lexer_get_next_token_returns_identifier_token_when_input_contains_digits() {
        let lexer = PascalLexer::new(&"numb3r".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Identifier, next_token.token_type);
        match next_token.value.unwrap() {
            TokenValue::Identifier(id) => assert_eq!("numb3r", id),
            _ => assert!(false),
        }
    }

    #[test]
    fn lexer_get_next_token_non_alphanumeric_characters_are_not_part_of_identifier() {
        let lexer = PascalLexer::new(&"number?123".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Identifier, next_token.token_type);
        match next_token.value.unwrap() {
            TokenValue::Identifier(id) => assert_eq!("number", id),
            _ => assert!(false),
        }
    }

    #[test]
    fn lexer_get_next_token_identifiers_dont_start_with_digit() {
        let lexer = PascalLexer::new(&"1foo".to_string());
        let next_token = lexer.get_next_token().unwrap();
        match next_token.token_type {
            TokenType::Identifier => assert!(false),
            _ => assert!(true),
        }
    }

    #[test]
    fn lexer_get_next_token_identifiers_can_start_with_underscore() {
        let lexer = PascalLexer::new(&"_number".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Identifier, next_token.token_type);
        match next_token.value.unwrap() {
            TokenValue::Identifier(id) => assert_eq!("_number", id),
            _ => assert!(false),
        }
    }

    #[test]
    fn lexer_get_next_token_identifiers_dont_end_with_underscore() {
        let lexer = PascalLexer::new(&"num_".to_string());
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Identifier, next_token.token_type);
        match next_token.value.unwrap() {
            TokenValue::Identifier(id) => assert_eq!("num", id),
            _ => assert!(false),
        }
    }
}
