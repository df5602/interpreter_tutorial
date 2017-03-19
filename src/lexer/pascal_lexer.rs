//! This module contains a lexer that recognizes `Token`s in a Pascal program.
use std::cell::Cell;
use std::i64;
use std::str::FromStr;
use std::error::Error;
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
        let mut pos: usize;
        let mut current_char: char;

        loop {
            // Advance to the next non-whitespace character
            self.skip_whitespace();

            pos = self.pos.get();

            // Return EOF when we have reached the end of the input
            if pos + 1 > self.chars.len() {
                self.pos.set(pos + 1);
                return Ok(Token::new(TokenType::Eof, None, Span::new(pos, pos + 1)));
            }

            current_char = self.chars[pos];

            // Skip comments
            if current_char == '{' {
                self.skip_comments();
            } else {
                break;
            }
        }

        // Return number when the next character is a digit
        if current_char.is_digit(10) {
            return self.parse_number();
        }

        // Return floating point number when the next character is a dot followed by a digit,
        // otherwise, return DOT when the next character is '.'
        if current_char == '.' {
            let next_char = self.peek(1);
            if next_char.is_some() && next_char.unwrap().is_digit(10) {
                return self.parse_number();
            } else {
                self.pos.set(pos + 1);
                return Ok(Token::new(TokenType::Dot, None, Span::new(pos, pos + 1)));
            }
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
                                 Span::new(pos, pos + 1)));
        }

        // Return MINUS when the next character is '-'
        if current_char == '-' {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::Operator,
                                 Some(TokenValue::Operator(OperatorType::Minus)),
                                 Span::new(pos, pos + 1)));
        }

        // Return TIMES when the next character is '*'
        if current_char == '*' {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::Operator,
                                 Some(TokenValue::Operator(OperatorType::Times)),
                                 Span::new(pos, pos + 1)));
        }

        // Return FloatDivision when the next character is '/'
        if current_char == '/' {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::Operator,
                                 Some(TokenValue::Operator(OperatorType::FloatDivision)),
                                 Span::new(pos, pos + 1)));
        }

        // Return LPAREN when the next character is '('
        if current_char == '(' {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::LParen, None, Span::new(pos, pos + 1)));
        }

        // Return RPAREN when the next character is ')'
        if current_char == ')' {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::RParen, None, Span::new(pos, pos + 1)));
        }

        // Return COMMA when the next character is ','
        if current_char == ',' {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::Comma, None, Span::new(pos, pos + 1)));
        }

        // Return SEMICOLON when the next character is ';'
        if current_char == ';' {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::Semicolon, None, Span::new(pos, pos + 1)));
        }

        // Return ASSIGN when the next two characters are ':=',
        // else return COLON when the next character is ':'
        if current_char == ':' {
            if let Some('=') = self.peek(1) {
                self.pos.set(pos + 2);
                return Ok(Token::new(TokenType::Assign, None, Span::new(pos, pos + 2)));
            } else {
                self.pos.set(pos + 1);
                return Ok(Token::new(TokenType::Colon, None, Span::new(pos, pos + 1)));
            }
        }

        // Current character didn't match any known token, return error
        Err(SyntaxError {
                msg: format!("Invalid token: `{}`", current_char),
                span: Span::new(pos, pos + 1),
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
        // The following leads to a speedup of almost factor 2 compared with
        // calling text.chars().collect() directy.
        let mut tmp = Vec::with_capacity(text.len());
        for ch in text.chars() {
            tmp.push(ch);
        }
        PascalLexer {
            chars: tmp,
            pos: Cell::new(0),
        }
    }

    /// Returns a multi-digit (unsigned, base 10) integer
    /// Precondition: First character is digit
    fn parse_number(&self) -> Result<Token, SyntaxError> {
        let mut pos = self.pos.get();
        let mut current_char = self.chars[pos];
        assert!(current_char.is_digit(10) || current_char == '.');

        let start_pos = pos;
        let mut overflow = false;
        let mut is_float = current_char == '.';

        // Find end of number
        loop {
            pos += 1;

            if pos + 1 > self.chars.len() {
                break;
            }

            current_char = self.chars[pos];
            if !current_char.is_digit(10) {
                // Accept first dot as point in a floating point number
                if !is_float && current_char == '.' {
                    is_float = true;
                } else {
                    break;
                }
            }
        }

        self.pos.set(pos);

        // Convert to String, so that we can use the built-in parse methods (necessary
        // for floating point)
        let mut number = String::with_capacity(pos - start_pos);
        for ch in self.chars[start_pos..pos].iter() {
            number.push(*ch);
        }

        // Parse number
        let mut token_value = None;
        if !is_float {
            let parsed_number = i64::from_str(&number);
            match parsed_number {
                Ok(value) => token_value = Some(TokenValue::Integer(value)),
                Err(e) => {
                    // The Error kind returned by i64::from_str() is unfortunately private,
                    // so we can't match on it. The following workaround creates an overflow error,
                    // which can be used to compare against the real error returned by the from_str()
                    // function to determine whether we have an overflow error or something else.
                    let overflow_error = i64::from_str("9223372036854775808").unwrap_err();
                    if e == overflow_error {
                        overflow = true;
                    } else {
                        panic!("Error parsing integer: {} [number: {}]",
                               e.description(),
                               number)
                    }
                }
            }
        } else {
            let parsed_number = f64::from_str(&number);
            match parsed_number {
                Ok(value) => token_value = Some(TokenValue::Real(value)),
                Err(e) => {
                    panic!("Error parsing floating point number: {} [number: {}]",
                           e.description(),
                           number)
                }
            }
        }

        if overflow {
            Err(SyntaxError {
                    msg: "Integer overflow (exceeds storage capacity of signed 64-bit integer)"
                        .to_string(),
                    span: Span::new(start_pos, pos),
                })
        } else if !is_float {
            assert!(token_value.is_some());
            Ok(Token::new(TokenType::IntegerLiteral,
                          token_value,
                          Span::new(start_pos, pos)))
        } else {
            assert!(token_value.is_some());
            Ok(Token::new(TokenType::RealLiteral,
                          token_value,
                          Span::new(start_pos, pos)))
        }
    }

    /// Recognizes an identifier or a keyword
    /// * Returns a keyword `Token` if the input matches a keyword
    /// * Returns an IDENTIFIER `Token` otherwise
    fn recognize_identifier_or_keyword(&self) -> Result<Token, SyntaxError> {
        let start_pos = self.pos.get();
        let mut pos = start_pos;
        let mut current_char = self.chars[pos];
        assert!(current_char.is_alphabetic() || current_char == '_');

        loop {
            pos += 1;

            if pos + 1 > self.chars.len() {
                break;
            }

            current_char = self.chars[pos];
            if !current_char.is_alphanumeric() {
                break;
            }
        }

        self.pos.set(pos);

        // Convert to lower case, since identifiers and keywords are case-insensitive
        let mut result = String::with_capacity(pos - start_pos);
        for c in self.chars[start_pos..pos].iter() {
            for d in c.to_lowercase() {
                result.push(d);
            }
        }

        match result.as_ref() {
            "begin" => return Ok(Token::new(TokenType::Begin, None, Span::new(start_pos, pos))),
            "end" => return Ok(Token::new(TokenType::End, None, Span::new(start_pos, pos))),
            "program" => return Ok(Token::new(TokenType::Program, None, Span::new(start_pos, pos))),
            "var" => return Ok(Token::new(TokenType::Var, None, Span::new(start_pos, pos))),
            "integer" => {
                return Ok(Token::new(TokenType::TypeSpecifier,
                                     Some(TokenValue::Type(Type::Integer)),
                                     Span::new(start_pos, pos)))
            }
            "real" => {
                return Ok(Token::new(TokenType::TypeSpecifier,
                                     Some(TokenValue::Type(Type::Real)),
                                     Span::new(start_pos, pos)))
            }
            "div" => {
                return Ok(Token::new(TokenType::Operator,
                                     Some(TokenValue::Operator(OperatorType::IntegerDivision)),
                                     Span::new(start_pos, pos)))
            }
            _ => {}
        }

        // Identifier name is stored in a String at the beginning of this function.
        // Moving the following into the match statement leads to problems with the borrow checker.
        Ok(Token::new(TokenType::Identifier,
                      Some(TokenValue::Identifier(result)),
                      Span::new(start_pos, pos)))
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

    /// Skips comments (any characters enclosed in curly braces).
    /// Nested comments are not supported.
    fn skip_comments(&self) {
        let mut pos = self.pos.get();
        assert_eq!(self.chars[pos], '{');

        loop {
            // Terminate if we have reached the end of the input
            if pos + 1 > self.chars.len() {
                break;
            }

            // Continue unless current character is the closing brace
            if self.chars[pos] == '}' {
                break;
            } else {
                pos += 1;
            }
        }

        self.pos.set(pos + 1);
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
    #[cfg(feature = "benchmarks")]
    use test::Bencher;

    use lexer::Lexer;

    fn assert_input_generates_token(input: &str, token: TokenType) {
        let lexer = PascalLexer::new(input);
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(next_token.token_type, token);
    }

    macro_rules! assert_input_generates_token_with_value {
        ($input:expr, $variant:path, $val:expr) => (
            let lexer = PascalLexer::new($input);
            let next_token = lexer.get_next_token().unwrap();
            match next_token.value.unwrap() {
                $variant(value) => assert_eq!($val, value),
                _ => assert!(false),
            }
        )
    }

    #[test]
    fn lexer_get_next_token_returns_eof_when_input_is_empty() {
        assert_input_generates_token("", TokenType::Eof);
    }

    #[test]
    fn lexer_get_next_token_returns_token_or_error_when_input_is_not_empty() {
        let lexer = PascalLexer::new("3+5");
        let next_token = lexer.get_next_token();
        match next_token {
            Ok(token) => assert!(token.token_type != TokenType::Eof),
            Err(_) => assert!(true),
        }
    }

    #[test]
    fn lexer_get_next_token_returns_integer_when_input_is_digit() {
        assert_input_generates_token("3", TokenType::IntegerLiteral);
    }

    #[test]
    fn lexer_get_next_token_returns_integer_value_when_input_is_digit() {
        assert_input_generates_token_with_value!("3", TokenValue::Integer, 3);
    }

    #[test]
    fn lexer_get_next_token_returns_next_token_when_called_second_time() {
        let lexer = PascalLexer::new("+3");
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Operator, next_token.token_type);
        let next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::IntegerLiteral, next_token.token_type);
    }

    #[test]
    fn lexer_get_next_token_returns_plus_when_input_is_plus() {
        assert_input_generates_token("+", TokenType::Operator);
    }

    #[test]
    fn lexer_get_next_token_returns_operator_value_plus_when_input_is_operator_plus() {
        assert_input_generates_token_with_value!("+", TokenValue::Operator, OperatorType::Plus);
    }

    #[test]
    fn lexer_get_next_token_returns_minus_when_input_is_minus() {
        assert_input_generates_token("-", TokenType::Operator);
    }

    #[test]
    fn lexer_get_next_token_returns_operator_value_minus_when_input_is_operator_minus() {
        assert_input_generates_token_with_value!("-", TokenValue::Operator, OperatorType::Minus);
    }

    #[test]
    fn lexer_get_next_token_returns_times_when_input_is_times() {
        assert_input_generates_token("*", TokenType::Operator);
    }

    #[test]
    fn lexer_get_next_token_returns_operator_value_times_when_input_is_operator_times() {
        assert_input_generates_token_with_value!("*", TokenValue::Operator, OperatorType::Times);
    }

    #[test]
    fn lexer_get_next_token_returns_integer_division_when_input_is_integer_division() {
        assert_input_generates_token("div", TokenType::Operator);
    }

    #[test]
    fn lexer_get_next_token_returns_op_value_integer_division_when_input_is_integer_division() {
        assert_input_generates_token_with_value!("div",
                                                 TokenValue::Operator,
                                                 OperatorType::IntegerDivision);
    }

    #[test]
    fn lexer_get_next_token_returns_float_division_when_input_is_float_division() {
        assert_input_generates_token("/", TokenType::Operator);
    }

    #[test]
    fn lexer_get_next_token_returns_op_value_float_division_when_input_is_float_division() {
        assert_input_generates_token_with_value!("/",
                                                 TokenValue::Operator,
                                                 OperatorType::FloatDivision);
    }

    #[test]
    fn lexer_parse_number_returns_multi_digit_integer() {
        let lexer = PascalLexer::new("123");
        let token = lexer.parse_number().unwrap();
        match token.value.unwrap() {
            TokenValue::Integer(value) => assert_eq!(123, value),
            _ => assert!(false),
        }
    }

    #[test]
    fn lexer_parse_number_should_advance_position_correctly() {
        let lexer = PascalLexer::new("123");
        let _result = lexer.parse_number().unwrap();
        assert_eq!(3, lexer.pos.get());
    }

    #[test]
    fn lexer_parse_number_should_only_advance_as_long_as_there_are_more_digits() {
        let lexer = PascalLexer::new("12a");
        let token = lexer.parse_number().unwrap();
        match token.value.unwrap() {
            TokenValue::Integer(value) => assert_eq!(12, value),
            _ => assert!(false),
        }
        assert_eq!(2, lexer.pos.get());
    }

    #[test]
    fn lexer_parse_number_should_return_error_when_input_is_larger_than_fit_in_i64() {
        let lexer = PascalLexer::new("9223372036854775808");
        let result = lexer.parse_number();
        assert!(result.is_err());
    }

    #[test]
    fn lexer_parse_number_should_return_number_when_input_fits_in_i64() {
        let lexer = PascalLexer::new("9223372036854775807");
        let token = lexer.parse_number().unwrap();
        match token.value.unwrap() {
            TokenValue::Integer(value) => assert_eq!(9223372036854775807, value),
            _ => assert!(false),
        }
    }

    #[test]
    fn lexer_parse_number_returns_floating_point_number() {
        let lexer = PascalLexer::new("12.3");
        let token = lexer.parse_number().unwrap();
        match token.value.unwrap() {
            TokenValue::Real(value) => assert_eq!(12.3, value),
            _ => assert!(false),
        }
    }

    #[test]
    fn lexer_parse_number_returns_floating_point_number_with_only_one_point() {
        let lexer = PascalLexer::new("12.3.0");
        let token = lexer.parse_number().unwrap();
        match token.value.unwrap() {
            TokenValue::Real(value) => assert_eq!(12.3, value),
            _ => assert!(false),
        }
    }

    #[test]
    fn lexer_parse_number_accepts_floating_point_numbers_with_trailing_dot() {
        let lexer = PascalLexer::new("12.");
        let token = lexer.parse_number().unwrap();
        match token.value.unwrap() {
            TokenValue::Real(value) => assert_eq!(12.0, value),
            _ => assert!(false),
        }
    }

    #[test]
    fn lexer_parse_number_accepts_floating_point_numbers_with_leading_dot() {
        let lexer = PascalLexer::new(".12");
        let token = lexer.parse_number().unwrap();
        match token.value.unwrap() {
            TokenValue::Real(value) => assert_eq!(0.12, value),
            _ => assert!(false),
        }
    }

    #[test]
    fn lexer_get_next_token_accepts_floating_point_numbers_with_leading_dot() {
        assert_input_generates_token_with_value!(".12", TokenValue::Real, 0.12);
    }

    #[test]
    fn lexer_parse_number_should_advance_position_correctly_when_parsing_float() {
        let lexer = PascalLexer::new("123.0");
        let _result = lexer.parse_number().unwrap();
        assert_eq!(5, lexer.pos.get());
    }

    #[test]
    fn lexer_parse_number_advances_position_correctly_when_parsing_float_with_trailing_dot() {
        let lexer = PascalLexer::new("123.");
        let _result = lexer.parse_number().unwrap();
        assert_eq!(4, lexer.pos.get());
    }

    #[test]
    fn lexer_parse_number_advances_position_correctly_when_parsing_float_with_leading_dot() {
        let lexer = PascalLexer::new(".123");
        let _result = lexer.parse_number().unwrap();
        assert_eq!(4, lexer.pos.get());
    }

    #[test]
    fn lexer_parse_number_only_advances_as_long_as_there_are_more_digits_in_the_flt_number() {
        let lexer = PascalLexer::new("12.1123a");
        let token = lexer.parse_number().unwrap();
        match token.value.unwrap() {
            TokenValue::Real(value) => assert_eq!(12.1123, value),
            _ => assert!(false),
        }
        assert_eq!(7, lexer.pos.get());
    }

    #[test]
    fn lexer_skip_whitespace_should_skip_all_whitespaces_until_eof() {
        let lexer = PascalLexer::new("  \n");
        lexer.skip_whitespace();
        assert_eq!(3, lexer.pos.get());
    }

    #[test]
    fn lexer_skip_whitespace_should_skip_all_whitespaces_until_first_non_whitespace_char() {
        let lexer = PascalLexer::new("  3");
        lexer.skip_whitespace();
        assert_eq!(2, lexer.pos.get());
    }

    #[test]
    fn lexer_skip_whitespace_should_not_skip_non_whitespace_characters() {
        let lexer = PascalLexer::new("123");
        lexer.skip_whitespace();
        assert_eq!(0, lexer.pos.get());
    }

    #[test]
    fn lexer_skip_comments_should_skip_all_characters_enclosed_in_curly_braces() {
        let lexer = PascalLexer::new("{comment}");
        lexer.skip_comments();
        assert_eq!(9, lexer.pos.get());
    }

    #[test]
    fn lexer_get_next_token_should_skip_comments() {
        assert_input_generates_token("{I am a comment}BEGIN", TokenType::Begin);
    }

    #[test]
    fn lexer_get_next_token_should_handle_whitespace_after_comment() {
        assert_input_generates_token("{I am a comment} BEGIN", TokenType::Begin);
    }

    #[test]
    fn lexer_get_next_token_should_skip_double_comments() {
        assert_input_generates_token("{ Comment 1 }{ Comment 2} BEGIN", TokenType::Begin);
    }

    #[test]
    fn lexer_get_next_token_should_skip_double_comments_separated_by_whitespace() {
        assert_input_generates_token("{ Comment 1 } { Comment 2} BEGIN", TokenType::Begin);
    }

    #[test]
    fn lexer_get_next_token_should_skip_single_comment() {
        assert_input_generates_token("{ Comment 1 }", TokenType::Eof);
    }

    #[test]
    fn lexer_should_recognize_expressions_that_contain_multi_digit_integer() {
        let lexer = PascalLexer::new("44+3");
        let mut next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::IntegerLiteral, next_token.token_type);
        assert_eq!(44, next_token.value.unwrap().extract_integer_value());
        next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Operator, next_token.token_type);
        assert_eq!(OperatorType::Plus,
                   next_token.value.unwrap().extract_operator_type());
        next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::IntegerLiteral, next_token.token_type);
        assert_eq!(3, next_token.value.unwrap().extract_integer_value());
    }

    #[test]
    fn lexer_should_recognize_expressions_that_begin_with_whitespace_characters() {
        let lexer = PascalLexer::new(" 2 + 3");
        let mut next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::IntegerLiteral, next_token.token_type);
        assert_eq!(2, next_token.value.unwrap().extract_integer_value());
        next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Operator, next_token.token_type);
        assert_eq!(OperatorType::Plus,
                   next_token.value.unwrap().extract_operator_type());
        next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::IntegerLiteral, next_token.token_type);
        assert_eq!(3, next_token.value.unwrap().extract_integer_value());
    }

    #[test]
    fn lexer_should_recognize_expressions_that_contain_whitespace_characters() {
        let lexer = PascalLexer::new("2 + 3");
        let mut next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::IntegerLiteral, next_token.token_type);
        assert_eq!(2, next_token.value.unwrap().extract_integer_value());
        next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::Operator, next_token.token_type);
        assert_eq!(OperatorType::Plus,
                   next_token.value.unwrap().extract_operator_type());
        next_token = lexer.get_next_token().unwrap();
        assert_eq!(TokenType::IntegerLiteral, next_token.token_type);
        assert_eq!(3, next_token.value.unwrap().extract_integer_value());
    }

    #[test]
    fn lexer_get_next_token_returns_left_parenthesis_when_input_is_left_parenthesis() {
        assert_input_generates_token("(", TokenType::LParen);
    }

    #[test]
    fn lexer_get_next_token_returns_right_parenthesis_when_input_is_right_parenthesis() {
        assert_input_generates_token(")", TokenType::RParen);
    }

    #[test]
    fn lexer_get_next_token_returns_dot_token_when_input_is_dot() {
        assert_input_generates_token(".", TokenType::Dot);
    }

    #[test]
    fn lexer_get_next_token_returns_semicolon_token_when_input_is_semicolon() {
        assert_input_generates_token(";", TokenType::Semicolon);
    }

    #[test]
    fn lexer_get_next_token_returns_colon_token_when_input_is_colon() {
        assert_input_generates_token(":", TokenType::Colon);
    }

    #[test]
    fn lexer_get_next_token_doesnt_return_colon_token_when_input_is_colon_followed_by_eq() {
        let lexer = PascalLexer::new(":=");
        let next_token = lexer.get_next_token().unwrap();
        assert!(next_token.token_type != TokenType::Colon);
    }

    #[test]
    fn lexer_get_next_token_returns_assign_token_when_input_is_assignment_operator() {
        assert_input_generates_token(":=", TokenType::Assign);
    }

    #[test]
    fn lexer_get_next_token_advances_position_correctly_for_assign_token() {
        let lexer = PascalLexer::new(":=");
        let _ = lexer.get_next_token();
        assert_eq!(lexer.get_position(), 2);
    }

    #[test]
    fn lexer_get_next_token_doesnt_return_assign_token_when_input_is_only_colon() {
        let lexer = PascalLexer::new(":");
        let next_token = lexer.get_next_token().unwrap();
        assert!(next_token.token_type != TokenType::Assign);
    }

    #[test]
    fn lexer_get_next_token_doesnt_ret_assign_tok_when_input_is_colon_not_followed_by_eq_sign() {
        let lexer = PascalLexer::new(":?");
        let next_token = lexer.get_next_token().unwrap();
        assert!(next_token.token_type != TokenType::Assign);
    }

    #[test]
    fn lexer_get_next_token_returns_comma_token_when_input_is_comma() {
        assert_input_generates_token(",", TokenType::Comma);
    }

    #[test]
    fn lexer_get_next_token_returns_begin_token_when_input_is_begin_keyword_uppercase() {
        assert_input_generates_token("BEGIN", TokenType::Begin);
    }

    #[test]
    fn lexer_get_next_token_returns_begin_token_when_input_is_begin_keyword_mixed_case() {
        assert_input_generates_token("beGIN", TokenType::Begin);
    }

    #[test]
    fn lexer_get_next_token_returns_end_token_when_input_is_end_keyword_uppercase() {
        assert_input_generates_token("END", TokenType::End);
    }

    #[test]
    fn lexer_get_next_token_returns_end_token_when_input_is_end_keyword_lowercase() {
        assert_input_generates_token("end", TokenType::End);
    }

    #[test]
    fn lexer_get_next_token_returns_identifier_token_when_input_is_string() {
        assert_input_generates_token("number", TokenType::Identifier);
    }

    #[test]
    fn lexer_get_next_token_returns_identifier_token_with_id_value_when_input_is_string() {
        assert_input_generates_token_with_value!("number", TokenValue::Identifier, "number");
    }

    #[test]
    fn lexer_identifiers_are_case_insensitive() {
        assert_input_generates_token("nUmBeR", TokenType::Identifier);
        assert_input_generates_token_with_value!("nUmBeR", TokenValue::Identifier, "number");
    }

    #[test]
    fn lexer_get_next_token_returns_identifier_token_when_input_contains_digits() {
        assert_input_generates_token("numb3r", TokenType::Identifier);
        assert_input_generates_token_with_value!("numb3r", TokenValue::Identifier, "numb3r");
    }

    #[test]
    fn lexer_get_next_token_non_alphanumeric_characters_are_not_part_of_identifier() {
        assert_input_generates_token("number?123", TokenType::Identifier);
        assert_input_generates_token_with_value!("number?123", TokenValue::Identifier, "number");
    }

    #[test]
    fn lexer_get_next_token_identifiers_dont_start_with_digit() {
        let lexer = PascalLexer::new("1foo");
        let next_token = lexer.get_next_token().unwrap();
        match next_token.token_type {
            TokenType::Identifier => assert!(false),
            _ => assert!(true),
        }
    }

    #[test]
    fn lexer_get_next_token_identifiers_can_start_with_underscore() {
        assert_input_generates_token("_number", TokenType::Identifier);
        assert_input_generates_token_with_value!("_number", TokenValue::Identifier, "_number");
    }

    #[test]
    fn lexer_get_next_token_identifiers_dont_end_with_underscore() {
        assert_input_generates_token("num_", TokenType::Identifier);
        assert_input_generates_token_with_value!("num_", TokenValue::Identifier, "num");
    }

    #[test]
    fn lexer_get_next_token_returns_program_token_when_input_is_program_keyword() {
        assert_input_generates_token("PROGRAM", TokenType::Program);
    }

    #[test]
    fn lexer_get_next_token_returns_var_token_when_input_is_var_keyword() {
        assert_input_generates_token("VAR", TokenType::Var);
    }

    #[test]
    fn lexer_get_next_token_returns_type_specifier_token_when_input_is_integer_keyword() {
        assert_input_generates_token("INTEGER", TokenType::TypeSpecifier);
    }

    #[test]
    fn lexer_get_next_token_returns_type_integer_when_input_is_integer_keyword() {
        assert_input_generates_token_with_value!("integer", TokenValue::Type, Type::Integer);
    }

    #[test]
    fn lexer_get_next_token_returns_type_specifier_token_when_input_is_real_keyword() {
        assert_input_generates_token("REAL", TokenType::TypeSpecifier);
    }

    #[test]
    fn lexer_get_next_token_returns_type_real_when_input_is_real_keyword() {
        assert_input_generates_token_with_value!("real", TokenValue::Type, Type::Real);
    }

    #[bench]
    #[cfg(feature = "benchmarks")]
    fn lexer_overall(b: &mut Bencher) {
        b.iter(|| {
            let lexer = PascalLexer::new("BEGIN a := 3; b := 4; BEGIN c := a + b END END.");
            while let Ok(token) = lexer.get_next_token() {
                match token.token_type {
                    TokenType::Eof => break,
                    _ => {}
                }
            }
        })
    }

    #[bench]
    #[cfg(feature = "benchmarks")]
    fn lexer_constructor(b: &mut Bencher) {
        b.iter(|| { let _ = PascalLexer::new("BEGIN a := 3; b := 4; BEGIN c := a + b END END."); })
    }

    #[bench]
    #[cfg(feature = "benchmarks")]
    fn lexer_parse_integer(b: &mut Bencher) {
        b.iter(|| {
                   let lexer = PascalLexer::new("312645978");
                   let _ = lexer.get_next_token();
               })
    }

    #[bench]
    #[cfg(feature = "benchmarks")]
    fn lexer_parse_identifier(b: &mut Bencher) {
        b.iter(|| {
                   let lexer = PascalLexer::new("number");
                   let _ = lexer.get_next_token();
               })
    }
}
