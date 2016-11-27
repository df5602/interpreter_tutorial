use std::fmt;
use std::cell::{Cell, RefCell};
use std::io;
use std::io::{BufRead, Write};

#[derive(Clone, Debug, PartialEq)]
enum TokenType {
    Integer,
    Operator,
    Eof,
}

impl fmt::Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TokenType::Integer => write!(f, "INTEGER"),
            TokenType::Operator => write!(f, "OPERATOR"),
            TokenType::Eof => write!(f, "EOF"),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
enum OperatorType {
    Plus,
    Minus,
    Times,
    Division,
}

impl fmt::Display for OperatorType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            OperatorType::Plus => write!(f, "'+'"),
            OperatorType::Minus => write!(f, "'-'"),
            OperatorType::Times => write!(f, "'*'"),
            OperatorType::Division => write!(f, "'/'"),
        }
    }
}

#[derive(Clone, Debug)]
enum TokenValue {
    IntegerValue(u64),
    OperatorValue(OperatorType),
}

#[derive(Clone, Debug)]
struct Token {
    token_type: TokenType,
    value: Option<TokenValue>,
    position: (usize, usize),
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.value {
            Some(ref value) => {
                match *value {
                    TokenValue::IntegerValue(val) => {
                        write!(f, "Token({}, {})", self.token_type, val)
                    }
                    TokenValue::OperatorValue(ref val) => {
                        write!(f, "Token({}, {})", self.token_type, val)
                    }
                }
            }
            None => write!(f, "Token({})", self.token_type),
        }
    }
}

impl Token {
    fn new(token_type: TokenType, value: Option<TokenValue>, position: (usize, usize)) -> Token {
        Token {
            token_type: token_type,
            value: value,
            position: position,
        }
    }
}

#[derive(Debug)]
struct SyntaxError {
    msg: String,
    position: (usize, usize),
}

#[derive(Debug)]
struct Lexer {
    chars: Vec<char>,
    pos: Cell<usize>,
}

impl Lexer {
    fn new(text: &String) -> Lexer {
        Lexer {
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
                                 Some(TokenValue::IntegerValue(value)),
                                 (pos, self.pos.get())));
        }

        // Return PLUS when the next character is '+'
        if current_char == '+' {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::Operator,
                                 Some(TokenValue::OperatorValue(OperatorType::Plus)),
                                 (pos, pos + 1)));
        }

        // Return MINUS when the next character is '-'
        if current_char == '-' {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::Operator,
                                 Some(TokenValue::OperatorValue(OperatorType::Minus)),
                                 (pos, pos + 1)));
        }

        // Return TIMES when the next character is '*'
        if current_char == '*' {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::Operator,
                                 Some(TokenValue::OperatorValue(OperatorType::Times)),
                                 (pos, pos + 1)));
        }

        // Return DIVISION when the next character is '/'
        if current_char == '/' {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::Operator,
                                 Some(TokenValue::OperatorValue(OperatorType::Division)),
                                 (pos, pos + 1)));
        }

        // Current character didn't match any known token, return error
        Err(SyntaxError {
            msg: "Invalid token".to_string(),
            position: (pos, pos + 1),
        })
    }
}

#[derive(Debug)]
struct Interpreter {
    text: String,
    current_token: RefCell<Option<Token>>,
    lexer: Lexer,
}

impl Interpreter {
    fn new(text: String, lexer: Lexer) -> Interpreter {
        Interpreter {
            text: text,
            current_token: RefCell::new(None),
            lexer: lexer,
        }
    }

    // Prints error in the following format:
    // Error parsing input: msg
    // >>> 3?5
    // >>>  ^
    fn print_error(&self, e: SyntaxError) {
        let s = std::iter::repeat(" ").take(e.position.0).collect::<String>();
        let m = std::iter::repeat("^").take(e.position.1 - e.position.0).collect::<String>();

        println!("Error parsing input: {}", e.msg);
        println!(">>> {}", self.text);
        println!(">>> {}{}", s, m);
    }

    // Consumes current token if it is of the expected type
    fn eat(&self, token_type: TokenType) -> Result<(), SyntaxError> {
        let mut current_token = self.current_token.borrow_mut();

        // If token has expected type...
        if current_token.as_ref().unwrap().token_type == token_type {
            // ... consume token and set current token to the next token
            if token_type != TokenType::Eof {
                let next_token = self.lexer.get_next_token();
                match next_token {
                    Ok(token) => {
                        *current_token = Some(token);
                        Ok(())
                    }
                    Err(e) => Err(e),
                }
            } else {
                Ok(())
            }
        } else {
            let pos = current_token.as_ref().unwrap().position;
            Err(SyntaxError {
                msg: format!("Expected {}, got {}",
                             token_type,
                             current_token.as_ref().unwrap().token_type),
                position: pos,
            })
        }
    }

    // Loads first token
    fn load_first_token(&self) -> Result<(), SyntaxError> {
        let mut current_token = self.current_token.borrow_mut();
        let next_token = self.lexer.get_next_token();
        if next_token.is_err() {
            Err(next_token.unwrap_err())
        } else {
            *current_token = Some(next_token.unwrap());
            Ok(())
        }
    }

    // Evaluates an expression:
    // expr -> INTEGER
    //       | INTEGER OPERATOR EXPR
    //
    // Precondition: First token has been loaded
    fn expr(&self) -> Result<i64, SyntaxError> {
        let lhs: Option<TokenValue>;
        let mut rhs: Token;
        let mut op: Option<TokenValue>;
        let mut result: i64;

        // Precondition: First token has been loaded
        assert!(self.current_token.borrow().is_some());

        // First token should be an integer
        {
            lhs = self.current_token.borrow().clone().unwrap().value;
        }
        let mut eaten = self.eat(TokenType::Integer);
        if eaten.is_err() {
            return Err(eaten.unwrap_err());
        }

        // Extract value
        result = match lhs.unwrap() {
            TokenValue::IntegerValue(value) => value as i64,
            _ => panic!("Internal Error (Integer value has wrong type)"),
        };

        loop {
            // Return if next token is EOF
            if self.current_token.borrow().clone().unwrap().token_type == TokenType::Eof {
                return Ok(result);
            }

            // Otherwise, expect next token to be an operator
            {
                op = self.current_token.borrow().clone().unwrap().value;
            }
            eaten = self.eat(TokenType::Operator);
            if eaten.is_err() {
                return Err(eaten.unwrap_err());
            }

            // Extract value
            let op_type = match op.unwrap() {
                TokenValue::OperatorValue(value) => value,
                _ => panic!("Internal Error (Operator value has wrong type)"),
            };

            // Expect next token to be an integer
            {
                rhs = self.current_token.borrow().clone().unwrap();
            }
            eaten = self.eat(TokenType::Integer);
            if eaten.is_err() {
                return Err(eaten.unwrap_err());
            }

            // Extract value
            let rhs_val = match rhs.value.unwrap() {
                TokenValue::IntegerValue(value) => value as i64,
                _ => panic!("Internal Error (Integer value has wrong type)"),
            };

            // Update result of expression
            result = if op_type == OperatorType::Plus {
                result + rhs_val
            } else if op_type == OperatorType::Minus {
                result - rhs_val
            } else if op_type == OperatorType::Times {
                result * rhs_val
            } else if op_type == OperatorType::Division {
                if rhs_val == 0 {
                    return Err(SyntaxError {
                        msg: "Division by zero".to_string(),
                        position: rhs.position,
                    });
                } else {
                    result / rhs_val
                }
            } else {
                return Err(SyntaxError {
                    msg: "Internal Error (Unknown operator type)".to_string(),
                    position: (self.lexer.pos.get(), self.lexer.pos.get() + 1),
                });
            }
        }
    }
}

#[allow(unused_must_use)]
fn print_preamble() {
    let stdout = io::stdout();

    stdout.lock().write(b"interpreter> ");
    stdout.lock().flush();
}

fn main() {
    let stdin = io::stdin();

    print_preamble();
    for line in stdin.lock().lines() {
        match line {
            Ok(_) => {
                let input = line.unwrap();
                let lexer = Lexer::new(&input);
                let interpreter = Interpreter::new(input, lexer);
                let load_result = interpreter.load_first_token();
                match load_result {
                    Ok(()) => {
                        let result = interpreter.expr();
                        match result {
                            Ok(value) => println!("{}", value),
                            Err(e) => interpreter.print_error(e),
                        }
                    }
                    Err(e) => interpreter.print_error(e),
                }

            }
            Err(error) => {
                println!("error: {}", error);
                panic!();
            }
        }
        print_preamble();
    }
}

#[test]
fn lexer_get_next_token_returns_eof_when_input_is_empty() {
    let lexer = Lexer::new(&"".to_string());
    let next_token = lexer.get_next_token().unwrap();
    assert_eq!(TokenType::Eof, next_token.token_type);
}

#[test]
fn lexer_get_next_token_returns_token_or_error_when_input_is_not_empty() {
    let lexer = Lexer::new(&"3+5".to_string());
    let next_token = lexer.get_next_token();
    match next_token {
        Ok(token) => assert!(token.token_type != TokenType::Eof),
        Err(_) => assert!(true),
    }
}

#[test]
fn lexer_get_next_token_returns_integer_when_input_is_digit() {
    let lexer = Lexer::new(&"3".to_string());
    let next_token = lexer.get_next_token().unwrap();
    assert_eq!(TokenType::Integer, next_token.token_type);
}

#[test]
fn lexer_get_next_token_returns_integer_value_when_input_is_digit() {
    let lexer = Lexer::new(&"3".to_string());
    let next_token = lexer.get_next_token().unwrap();
    match next_token.value.unwrap() {
        TokenValue::IntegerValue(value) => assert_eq!(3, value),
        TokenValue::OperatorValue(_) => assert!(false),
    }
}

#[test]
fn lexer_get_next_token_returns_next_token_when_called_second_time() {
    let lexer = Lexer::new(&"+3".to_string());
    let next_token = lexer.get_next_token().unwrap();
    assert_eq!(TokenType::Operator, next_token.token_type);
    let next_token = lexer.get_next_token().unwrap();
    assert_eq!(TokenType::Integer, next_token.token_type);
}

#[test]
fn lexer_get_next_token_returns_plus_when_input_is_plus() {
    let lexer = Lexer::new(&"+".to_string());
    let next_token = lexer.get_next_token().unwrap();
    assert_eq!(TokenType::Operator, next_token.token_type);
}

#[test]
fn lexer_get_next_token_returns_operator_value_plus_when_input_is_operator_plus() {
    let lexer = Lexer::new(&"+".to_string());
    let next_token = lexer.get_next_token().unwrap();
    match next_token.value.unwrap() {
        TokenValue::IntegerValue(_) => assert!(false),
        TokenValue::OperatorValue(value) => assert_eq!(OperatorType::Plus, value),
    }
}

#[test]
fn lexer_get_next_token_returns_minus_when_input_is_minus() {
    let lexer = Lexer::new(&"-".to_string());
    let next_token = lexer.get_next_token().unwrap();
    assert_eq!(TokenType::Operator, next_token.token_type);
}

#[test]
fn lexer_get_next_token_returns_operator_value_minus_when_input_is_operator_minus() {
    let lexer = Lexer::new(&"-".to_string());
    let next_token = lexer.get_next_token().unwrap();
    match next_token.value.unwrap() {
        TokenValue::IntegerValue(_) => assert!(false),
        TokenValue::OperatorValue(value) => assert_eq!(OperatorType::Minus, value),
    }
}

#[test]
fn lexer_get_next_token_returns_times_when_input_is_times() {
    let lexer = Lexer::new(&"*".to_string());
    let next_token = lexer.get_next_token().unwrap();
    assert_eq!(TokenType::Operator, next_token.token_type);
}

#[test]
fn lexer_get_next_token_returns_operator_value_times_when_input_is_operator_times() {
    let lexer = Lexer::new(&"*".to_string());
    let next_token = lexer.get_next_token().unwrap();
    match next_token.value.unwrap() {
        TokenValue::IntegerValue(_) => assert!(false),
        TokenValue::OperatorValue(value) => assert_eq!(OperatorType::Times, value),
    }
}

#[test]
fn lexer_get_next_token_returns_division_when_input_is_division() {
    let lexer = Lexer::new(&"/".to_string());
    let next_token = lexer.get_next_token().unwrap();
    assert_eq!(TokenType::Operator, next_token.token_type);
}

#[test]
fn lexer_get_next_token_returns_operator_value_division_when_input_is_operator_division() {
    let lexer = Lexer::new(&"/".to_string());
    let next_token = lexer.get_next_token().unwrap();
    match next_token.value.unwrap() {
        TokenValue::IntegerValue(_) => assert!(false),
        TokenValue::OperatorValue(value) => assert_eq!(OperatorType::Division, value),
    }
}

#[test]
fn lexer_get_next_token_returns_error_when_input_is_letter() {
    let lexer = Lexer::new(&"a".to_string());
    let next_token = lexer.get_next_token();
    match next_token {
        Ok(_) => assert!(false),
        Err(_) => assert!(true),
    }
}

#[test]
fn interpreter_eat_should_consume_token_if_it_has_the_correct_type() {
    let input = "+4".to_string();
    let lexer = Lexer::new(&input);
    let interpreter = Interpreter::new(input, lexer);
    *interpreter.current_token.borrow_mut() = Some(interpreter.lexer.get_next_token().unwrap());
    let _op = interpreter.eat(TokenType::Operator);
    let current_token = interpreter.current_token.borrow();
    match *current_token {
        Some(ref token) => assert_eq!(TokenType::Integer, token.token_type),
        None => assert!(false),
    }
}

#[test]
fn interpreter_eat_should_not_consume_token_if_it_has_the_wrong_type() {
    let input = "+4".to_string();
    let lexer = Lexer::new(&input);
    let interpreter = Interpreter::new(input, lexer);
    *interpreter.current_token.borrow_mut() = Some(interpreter.lexer.get_next_token().unwrap());
    let result = interpreter.eat(TokenType::Integer);
    assert!(result.is_err());
}

#[test]
// expr -> INTEGER OPERATOR INTEGER
fn interpreter_expr_should_add_values_when_expression_is_addition() {
    let input = "3+4".to_string();
    let lexer = Lexer::new(&input);
    let interpreter = Interpreter::new(input, lexer);
    assert!(interpreter.load_first_token().is_ok());
    let result = interpreter.expr();
    assert_eq!(7, result.unwrap());
}

#[test]
// expr -> INTEGER OPERATOR INTEGER
fn interpreter_expr_should_subtract_values_when_expression_is_subtraction() {
    let input = "4-3".to_string();
    let lexer = Lexer::new(&input);
    let interpreter = Interpreter::new(input, lexer);
    assert!(interpreter.load_first_token().is_ok());
    let result = interpreter.expr();
    assert_eq!(1, result.unwrap());
}

#[test]
fn interpreter_expr_should_return_negative_number_when_result_of_subtraction_is_negative() {
    let input = "3-4".to_string();
    let lexer = Lexer::new(&input);
    let interpreter = Interpreter::new(input, lexer);
    assert!(interpreter.load_first_token().is_ok());
    let result = interpreter.expr();
    assert_eq!(-1, result.unwrap() as i64);
}

#[test]
fn interpreter_expr_should_multiply_values_when_expression_is_multiplication() {
    let input = "3*4".to_string();
    let lexer = Lexer::new(&input);
    let interpreter = Interpreter::new(input, lexer);
    assert!(interpreter.load_first_token().is_ok());
    let result = interpreter.expr();
    assert_eq!(12, result.unwrap());
}

#[test]
fn interpreter_expr_should_divide_values_when_expression_is_division() {
    let input = "4/2".to_string();
    let lexer = Lexer::new(&input);
    let interpreter = Interpreter::new(input, lexer);
    assert!(interpreter.load_first_token().is_ok());
    let result = interpreter.expr();
    assert_eq!(2, result.unwrap());
}

#[test]
fn interpreter_expr_should_return_error_when_division_by_zero() {
    let input = "1 / 0".to_string();
    let lexer = Lexer::new(&input);
    let interpreter = Interpreter::new(input, lexer);
    assert!(interpreter.load_first_token().is_ok());
    let result = interpreter.expr();
    assert!(result.is_err());
}

#[test]
fn interpreter_expr_should_not_parse_expressions_that_dont_begin_with_an_integer() {
    let input = "+4".to_string();
    let lexer = Lexer::new(&input);
    let interpreter = Interpreter::new(input, lexer);
    assert!(interpreter.load_first_token().is_ok());
    let result = interpreter.expr();
    assert!(result.is_err());
}

#[test]
fn interpreter_expr_should_parse_expressions_that_contain_multi_digit_integer() {
    let input = "44+3".to_string();
    let lexer = Lexer::new(&input);
    let interpreter = Interpreter::new(input, lexer);
    assert!(interpreter.load_first_token().is_ok());
    let result = interpreter.expr();
    assert_eq!(47, result.unwrap());
}

#[test]
fn interpreter_expr_should_not_parse_expressions_that_dont_have_operator_after_integer() {
    let input = "4?2".to_string();
    let lexer = Lexer::new(&input);
    let interpreter = Interpreter::new(input, lexer);
    assert!(interpreter.load_first_token().is_ok());
    let result = interpreter.expr();
    assert!(result.is_err());
}

#[test]
fn interpreter_expr_should_not_parse_expressions_that_dont_have_integer_after_operator() {
    let input = "4+a".to_string();
    let lexer = Lexer::new(&input);
    let interpreter = Interpreter::new(input, lexer);
    assert!(interpreter.load_first_token().is_ok());
    let result = interpreter.expr();
    assert!(result.is_err());
}

#[test]
fn interpreter_expr_should_not_parse_empty_string() {
    let input = "".to_string();
    let lexer = Lexer::new(&input);
    let interpreter = Interpreter::new(input, lexer);
    assert!(interpreter.load_first_token().is_ok());
    let result = interpreter.expr();
    assert!(result.is_err());
}

#[test]
fn interpreter_expr_should_not_parse_expressions_that_dont_terminate_with_eof() {
    let input = "1+3a".to_string();
    let lexer = Lexer::new(&input);
    let interpreter = Interpreter::new(input, lexer);
    assert!(interpreter.load_first_token().is_ok());
    let result = interpreter.expr();
    assert!(result.is_err());
}

#[test]
fn interpreter_expr_should_not_parse_expressions_that_dont_terminate_with_eof2() {
    let input = "1+3-".to_string();
    let lexer = Lexer::new(&input);
    let interpreter = Interpreter::new(input, lexer);
    assert!(interpreter.load_first_token().is_ok());
    let result = interpreter.expr();
    assert!(result.is_err());
}

#[test]
fn lexer_get_integer_returns_multi_digit_integer() {
    let lexer = Lexer::new(&"123".to_string());
    let result = lexer.get_integer();
    assert_eq!(123, result);
}

#[test]
fn lexer_get_integer_should_advance_position_correctly() {
    let lexer = Lexer::new(&"123".to_string());
    let _result = lexer.get_integer();
    assert_eq!(3, lexer.pos.get());
}

#[test]
fn lexer_get_integer_should_only_advance_as_long_as_there_are_more_digits() {
    let lexer = Lexer::new(&"12a".to_string());
    let result = lexer.get_integer();
    assert_eq!(12, result);
    assert_eq!(2, lexer.pos.get());
}

#[test]
fn lexer_skip_whitespace_should_skip_all_whitespaces_until_eof() {
    let lexer = Lexer::new(&"  \n".to_string());
    lexer.skip_whitespace();
    assert_eq!(3, lexer.pos.get());
}

#[test]
fn lexer_skip_whitespace_should_skip_all_whitespaces_until_first_non_whitespace_char() {
    let lexer = Lexer::new(&"  3".to_string());
    lexer.skip_whitespace();
    assert_eq!(2, lexer.pos.get());
}

#[test]
fn lexer_skip_whitespace_should_not_skip_non_whitespace_characters() {
    let lexer = Lexer::new(&"123".to_string());
    lexer.skip_whitespace();
    assert_eq!(0, lexer.pos.get());
}

#[test]
fn interpreter_expr_should_parse_expressions_that_contain_whitespace_characters() {
    let input = "2 + 3".to_string();
    let lexer = Lexer::new(&input);
    let interpreter = Interpreter::new(input, lexer);
    assert!(interpreter.load_first_token().is_ok());
    let result = interpreter.expr();
    assert_eq!(5, result.unwrap());
}

#[test]
fn interpreter_expr_should_parse_expressions_that_begin_with_whitespace_characters() {
    let input = " 2 + 3".to_string();
    let lexer = Lexer::new(&input);
    let interpreter = Interpreter::new(input, lexer);
    assert!(interpreter.load_first_token().is_ok());
    let result = interpreter.expr();
    assert_eq!(5, result.unwrap());
}

#[test]
fn interpreter_load_first_token_should_load_first_token() {
    let input = "2+3".to_string();
    let lexer = Lexer::new(&input);
    let interpreter = Interpreter::new(input, lexer);
    let _ = interpreter.load_first_token();
    assert_eq!(TokenType::Integer,
               interpreter.current_token.borrow().clone().unwrap().token_type);
    let val = interpreter.current_token.borrow().clone().unwrap().value.unwrap();
    match val {
        TokenValue::IntegerValue(val) => assert_eq!(2, val),
        _ => panic!(),
    }
}

#[test]
fn interpreter_expr_should_return_integer_value_if_input_consists_of_only_integer() {
    let input = "42".to_string();
    let lexer = Lexer::new(&input);
    let interpreter = Interpreter::new(input, lexer);
    assert!(interpreter.load_first_token().is_ok());
    let result = interpreter.expr();
    assert_eq!(42, result.unwrap());
}

#[test]
fn interpreter_expr_should_interpret_chained_expressions() {
    let input = "1+3+5".to_string();
    let lexer = Lexer::new(&input);
    let interpreter = Interpreter::new(input, lexer);
    assert!(interpreter.load_first_token().is_ok());
    let result = interpreter.expr();
    assert_eq!(9, result.unwrap());
}

#[test]
fn interpreter_expr_should_evaluate_chained_expressions_from_left_to_right() {
    let input = "1-2+3".to_string();
    let lexer = Lexer::new(&input);
    let interpreter = Interpreter::new(input, lexer);
    assert!(interpreter.load_first_token().is_ok());
    let result = interpreter.expr();
    assert_eq!(2, result.unwrap());
}
