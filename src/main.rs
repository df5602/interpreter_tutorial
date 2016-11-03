use std::fmt;
use std::cell::{Cell, RefCell};

#[derive(Debug, PartialEq)]
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

#[derive(Debug)]
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

    fn get_next_token(&self) -> Result<Token, String> {
        let pos = self.pos.get();

        // Return EOF when we have reached the end of the input
        if pos + 1 > self.chars.len() {
            return Ok(Token::new(TokenType::Eof, None));
        }

        let current_char = self.chars[pos];

        // Return INTEGER when the next character is a digit
        if current_char.is_digit(10) {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::Integer,
                                 Some(current_char.to_digit(10).unwrap() as u64)));
        }

        // Return PLUS when the next character is '+'
        if current_char == '+' {
            self.pos.set(pos + 1);
            return Ok(Token::new(TokenType::Plus, None));
        }

        return Err("Invalid token".to_string());
    }

    fn eat(&self, token_type: TokenType) -> Result<(), String> {
        let mut current_token = self.current_token.borrow_mut();
        if current_token.is_some() {
            if current_token.as_ref().unwrap().token_type == token_type {
                *current_token = Some(self.get_next_token().unwrap());
                Ok(())
            } else {
                Err(format!("Expected {}, got {}",
                            token_type,
                            current_token.as_ref().unwrap().token_type))
            }
        } else {
            Err(("".to_string()))
        }
    }
}

fn main() {
    let interpreter = Interpreter::new("4+34".to_string());

    *interpreter.current_token.borrow_mut() = Some(interpreter.get_next_token().unwrap());
    let result = interpreter.eat(TokenType::Plus);
    match result {
        Ok(()) => println!("Got integer"),
        Err(s) => interpreter.print_error(s, -1),
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
fn interpreter_get_next_token_return_plus_when_input_is_plus() {
    let interpreter = Interpreter::new("+".to_string());
    let next_token = interpreter.get_next_token().unwrap();
    assert_eq!(TokenType::Plus, next_token.token_type);
}

#[test]
fn interpreter_get_next_token_return_error_when_input_is_letter() {
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
    interpreter.eat(TokenType::Plus);
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
