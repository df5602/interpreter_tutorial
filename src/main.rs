use std::fmt;
use std::cell::{Cell, RefCell};
use std::io;
use std::io::{BufRead, Write};

#[derive(Debug, PartialEq, Clone)]
enum TokenType {
    Integer,
    Plus,
    Eof,
}

impl fmt::Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TokenType::Integer => write!(f, "INTEGER"),
            TokenType::Plus => write!(f, "'+'"),
            TokenType::Eof => write!(f, "EOF"),
        }
    }
}

#[derive(Debug, Clone)]
struct Token {
    token_type: TokenType,
    value: Option<u64>,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.value {
            Some(value) => write!(f, "Token({}, {})", self.token_type, value),
            None => write!(f, "Token({})", self.token_type),
        }
    }
}

impl Token {
    fn new(token_type: TokenType, value: Option<u64>) -> Token {
        Token {
            token_type: token_type,
            value: value,
        }
    }
}

#[derive(Debug)]
struct Interpreter {
    text: String,
    chars: Vec<char>,
    pos: Cell<usize>,
    current_token: RefCell<Option<Token>>,
}

impl Interpreter {
    fn new(text: String) -> Interpreter {
        Interpreter {
            text: text.clone(),
            chars: text.chars().collect(),
            pos: Cell::new(0),
            current_token: RefCell::new(None),
        }
    }

    fn print_error(&self, msg: String, offset: isize) {
        let mut s = "".to_string();
        for _ in 0..((self.pos.get() as isize + offset) as usize) {
            s = s + " ";
        }
        println!("Error parsing input: {}", msg);
        println!(">>> {}", self.text);
        println!(">>> {}^", s);
    }

    // Returns a multi-digit integer
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

    fn get_next_token(&self) -> Result<Token, String> {
        let pos = self.pos.get();

        // Return EOF when we have reached the end of the input
        if pos + 1 > self.chars.len() {
            return Ok(Token::new(TokenType::Eof, None));
        }

        let current_char = self.chars[pos];

        // Return INTEGER when the next character is a digit
        if current_char.is_digit(10) {
            let value = self.get_integer();
            return Ok(Token::new(TokenType::Integer, Some(value)));
        }

        // Return PLUS when the next character is '+'
        if current_char == '+' {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::Plus, None));
        }

        Err("Invalid token".to_string())
    }

    fn eat(&self, token_type: TokenType) -> Result<(), String> {
        let mut current_token = self.current_token.borrow_mut();
        if current_token.is_some() {
            if current_token.as_ref().unwrap().token_type == token_type {
                let next_token = self.get_next_token();
                match next_token {
                    Ok(token) => {
                        *current_token = Some(token);
                        Ok(())
                    }
                    Err(s) => Err(s),
                }
            } else {
                Err(format!("Expected {}, got {}",
                            token_type,
                            current_token.as_ref().unwrap().token_type))
            }
        } else {
            Err(("".to_string()))
        }
    }

    // Evaluates an expression:
    // expr -> INTEGER '+' INTEGER
    fn expr(&self) -> Result<u64, String> {
        let left: Token;
        let right: Token;

        // Get first token (return error if no valid token)
        {
            let mut current_token = self.current_token.borrow_mut();
            let next_token = self.get_next_token();
            if next_token.is_err() {
                return Err(next_token.unwrap_err());
            }
            *current_token = Some(next_token.unwrap());

            left = current_token.clone().unwrap();
        }
        // First token should be an integer
        let mut result = self.eat(TokenType::Integer);
        if result.is_err() {
            return Err(result.unwrap_err());
        }

        // Expect next token to be a '+'
        result = self.eat(TokenType::Plus);
        if result.is_err() {
            return Err(result.unwrap_err());
        }

        // Expect next token to be an integer
        {
            right = self.current_token.borrow().clone().unwrap();
        }
        result = self.eat(TokenType::Integer);
        if result.is_err() {
            return Err(result.unwrap_err());
        }

        // Expect next token to be EOF
        result = self.eat(TokenType::Eof);
        if result.is_err() {
            return Err(result.unwrap_err());
        }

        Ok(left.value.unwrap() + right.value.unwrap())
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
                let interpreter = Interpreter::new(line.unwrap());
                let result = interpreter.expr();
                match result {
                    Ok(value) => println!("{}", value),
                    Err(s) => interpreter.print_error(s, 0),
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
fn interpreter_get_next_token_returns_eof_when_input_is_empty() {
    let interpreter = Interpreter::new("".to_string());
    let next_token = interpreter.get_next_token().unwrap();
    assert_eq!(TokenType::Eof, next_token.token_type);
}

#[test]
fn interpreter_get_next_token_returns_token_or_error_when_input_is_not_empty() {
    let interpreter = Interpreter::new("3+5".to_string());
    let next_token = interpreter.get_next_token();
    match next_token {
        Ok(token) => assert!(token.token_type != TokenType::Eof),
        Err(_) => assert!(true),
    }
}

#[test]
fn interpreter_get_next_token_returns_integer_when_input_is_digit() {
    let interpreter = Interpreter::new("3".to_string());
    let next_token = interpreter.get_next_token().unwrap();
    assert_eq!(TokenType::Integer, next_token.token_type);
}

#[test]
fn interpreter_get_next_token_returns_integer_value_when_input_is_digit() {
    let interpreter = Interpreter::new("3".to_string());
    let next_token = interpreter.get_next_token().unwrap();
    assert_eq!(3, next_token.value.unwrap());
}

#[test]
fn interpreter_get_next_token_returns_next_token_when_called_second_time() {
    let interpreter = Interpreter::new("+3".to_string());
    let next_token = interpreter.get_next_token().unwrap();
    assert_eq!(TokenType::Plus, next_token.token_type);
    let next_token = interpreter.get_next_token().unwrap();
    assert_eq!(TokenType::Integer, next_token.token_type);
}

#[test]
fn interpreter_get_next_token_returns_plus_when_input_is_plus() {
    let interpreter = Interpreter::new("+".to_string());
    let next_token = interpreter.get_next_token().unwrap();
    assert_eq!(TokenType::Plus, next_token.token_type);
}

#[test]
fn interpreter_get_next_token_returns_error_when_input_is_letter() {
    let interpreter = Interpreter::new("a".to_string());
    let next_token = interpreter.get_next_token();
    match next_token {
        Ok(_) => assert!(false),
        Err(_) => assert!(true),
    }
}

#[test]
fn interpreter_eat_should_consume_token_if_it_has_the_correct_type() {
    let interpreter = Interpreter::new("+4".to_string());
    *interpreter.current_token.borrow_mut() = Some(interpreter.get_next_token().unwrap());
    let _op = interpreter.eat(TokenType::Plus);
    let current_token = interpreter.current_token.borrow();
    match *current_token {
        Some(ref token) => assert_eq!(TokenType::Integer, token.token_type),
        None => assert!(false),
    }
}

#[test]
fn interpreter_eat_should_not_consume_token_if_it_has_the_wrong_type() {
    let interpreter = Interpreter::new("+4".to_string());
    *interpreter.current_token.borrow_mut() = Some(interpreter.get_next_token().unwrap());
    let result = interpreter.eat(TokenType::Integer);
    assert!(result.is_err());
}

#[test]
// expr -> INTEGER '+' INTEGER
fn interpreter_expr_should_only_parse_valid_expressions() {
    let interpreter = Interpreter::new("3+4".to_string());
    let result = interpreter.expr();
    assert_eq!(7, result.unwrap());
}

#[test]
fn interpreter_expr_should_not_parse_expressions_that_dont_begin_with_an_integer() {
    let interpreter = Interpreter::new("+4".to_string());
    let result = interpreter.expr();
    assert!(result.is_err());
}

#[test]
fn interpreter_expr_should_parse_expressions_that_contain_multi_digit_integer() {
    let interpreter = Interpreter::new("44+3".to_string());
    let result = interpreter.expr();
    assert_eq!(47, result.unwrap());
}

#[test]
fn interpreter_expr_should_not_parse_expressions_that_dont_have_plus_after_integer() {
    let interpreter = Interpreter::new("4-2".to_string());
    let result = interpreter.expr();
    assert!(result.is_err());
}

#[test]
fn interpreter_expr_should_not_parse_expressions_that_dont_have_integer_after_plus() {
    let interpreter = Interpreter::new("4+a".to_string());
    let result = interpreter.expr();
    assert!(result.is_err());
}

#[test]
fn interpreter_expr_should_not_parse_empty_string() {
    let interpreter = Interpreter::new("".to_string());
    let result = interpreter.expr();
    assert!(result.is_err());
}

#[test]
fn interpreter_expr_should_not_parse_expressions_that_dont_terminate_with_eof() {
    let interpreter = Interpreter::new("1+3a".to_string());
    let result = interpreter.expr();
    assert!(result.is_err());
}

#[test]
fn interpreter_get_integer_returns_multi_digit_integer() {
    let interpreter = Interpreter::new("123".to_string());
    let result = interpreter.get_integer();
    assert_eq!(123, result);
}

#[test]
fn interpreter_get_integer_should_advance_position_correctly() {
    let interpreter = Interpreter::new("123".to_string());
    let _result = interpreter.get_integer();
    assert_eq!(3, interpreter.pos.get());
}

#[test]
fn interpreter_get_integer_should_only_advance_as_long_as_there_are_more_digits() {
    let interpreter = Interpreter::new("12a".to_string());
    let result = interpreter.get_integer();
    assert_eq!(12, result);
    assert_eq!(2, interpreter.pos.get());
}
