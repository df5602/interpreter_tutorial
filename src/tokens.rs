//! This module contains the token definitions.
use std::fmt;

/// Defines the type of a token.
#[derive(Clone, Debug, PartialEq)]
pub enum TokenType {
    /// A (multi-digit, base 10) unsigned integer
    Integer,
    /// One of the following operators: '+', '-', '*', '/'
    Operator,
    /// Variable name (must start with an alphabetic character,
    /// followed by any number of alphanumerical characters)
    Identifier,
    /// Opening parenthesis: '('
    LParen,
    /// Closing parenthesis: ')'
    RParen,
    /// Dot: '.'
    Dot,
    /// Semicolon: ';'
    Semicolon,
    /// Assignment operator: ':='
    Assign,
    /// 'BEGIN' (to mark the beginning of a compound statement)
    Begin,
    /// 'END' (to mark the end of a compound statement)
    End,
    /// End-of-file pseudo-token
    Eof,
}

impl fmt::Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TokenType::Integer => write!(f, "INTEGER"),
            TokenType::Operator => write!(f, "OPERATOR"),
            TokenType::Identifier => write!(f, "IDENTIFIER"),
            TokenType::LParen => write!(f, "LPAREN"),
            TokenType::RParen => write!(f, "RPAREN"),
            TokenType::Dot => write!(f, "DOT"),
            TokenType::Semicolon => write!(f, "SEMICOLON"),
            TokenType::Assign => write!(f, "ASSIGN"),
            TokenType::Begin => write!(f, "BEGIN"),
            TokenType::End => write!(f, "END"),
            TokenType::Eof => write!(f, "EOF"),
        }
    }
}

/// Defines the type of an operator.
#[derive(Clone, Debug, PartialEq)]
pub enum OperatorType {
    /// '+' (Addition)
    Plus,
    /// '-' (Subtraction)
    Minus,
    /// '*' (Multiplication)
    Times,
    /// '/' (Division)
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

/// Defines the value of the token (optional).
#[derive(Clone, Debug, PartialEq)]
pub enum TokenValue {
    /// Unsigned integer as u64
    Integer(u64),
    /// An operator
    Operator(OperatorType),
    /// An identifier name
    Identifier(String),
    #[cfg(test)]
    /// No value (for testing only)
    Empty,
}

impl TokenValue {
    /// Returns the inner value, if `self` is of variant `TokenValue::Integer`.
    ///
    /// # Panics
    ///
    /// This function will panic if `self` is not of variant `TokenValue::Integer`.
    pub fn extract_integer_value(&self) -> u64 {
        match *self {
            TokenValue::Integer(value) => value,
            _ => panic!("Internal Error (Integer value has wrong type)"),
        }
    }

    /// Returns a copy of the inner value, if `self` is of variant `TokenValue::Operator`.
    ///
    /// # Panics
    ///
    /// This function will panic if `self` is not of variant `TokenValue::Operator`.
    pub fn extract_operator_type(&self) -> OperatorType {
        match *self {
            TokenValue::Operator(ref value) => value.clone(),
            _ => panic!("Internal Error (Operator value has wrong type)"),
        }
    }

    /// Returns a copy of the inner value, if `self` is of variant `TokenValue::Identifier`.
    ///
    /// # Panics
    ///
    /// This function will panic if `self` is not of variant `TokenValue::Identifier`.
    pub fn extract_identifier_value(&self) -> String {
        match *self {
            TokenValue::Identifier(ref value) => value.clone(),
            _ => panic!("Internal Error (Identifier value has wrong type)"),
        }
    }
}

/// The `Token` type. Contains information about the recognized token.
#[derive(Clone, Debug)]
pub struct Token {
    /// The type of the token
    pub token_type: TokenType,
    /// An optional value
    pub value: Option<TokenValue>,
    /// The position in the input stream (for diagnostics reasons)
    pub position: (usize, usize),
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.value {
            Some(ref value) => {
                match *value {
                    TokenValue::Integer(val) => write!(f, "Token({}, {})", self.token_type, val),
                    TokenValue::Operator(ref val) => {
                        write!(f, "Token({}, {})", self.token_type, val)
                    }
                    TokenValue::Identifier(ref val) => {
                        write!(f, "Token({}, {})", self.token_type, val)
                    }
                    #[cfg(test)]
                    TokenValue::Empty => write!(f, "Token({})", self.token_type),
                }
            }
            None => write!(f, "Token({})", self.token_type),
        }
    }
}

impl Token {
    /// Constructs a new token.
    pub fn new(token_type: TokenType,
               value: Option<TokenValue>,
               position: (usize, usize))
               -> Token {
        Token {
            token_type: token_type,
            value: value,
            position: position,
        }
    }
}
