//! This module contains the token definitions.
use std::fmt;

/// Defines the type of a token.
#[derive(Clone, Debug, PartialEq)]
pub enum TokenType {
    /// A (multi-digit, base 10) unsigned integer
    IntegerLiteral,
    /// One of the following operators: '+', '-', '*', 'div' (integer division), '/' (float division)
    Operator,
    /// Variable name (must start with an alphabetic character,
    /// followed by any number of alphanumerical characters)
    Identifier,
    /// Type specifier
    TypeSpecifier,
    /// Opening parenthesis: '('
    LParen,
    /// Closing parenthesis: ')'
    RParen,
    /// Dot: '.'
    Dot,
    /// Semicolon: ';'
    Semicolon,
    /// Colon: ':'
    Colon,
    /// Comma: ','
    Comma,
    /// Assignment operator: ':='
    Assign,
    /// 'BEGIN' (to mark the beginning of a compound statement)
    Begin,
    /// 'END' (to mark the end of a compound statement)
    End,
    /// 'PROGRAM' (to mark the beginning of a program)
    Program,
    /// 'VAR' (to mark the beginning of a variable declarations block)
    Var,
    /// End-of-file pseudo-token
    Eof,
}

impl fmt::Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TokenType::IntegerLiteral => write!(f, "INTEGER LITERAL"),
            TokenType::Operator => write!(f, "OPERATOR"),
            TokenType::Identifier => write!(f, "IDENTIFIER"),
            TokenType::TypeSpecifier => write!(f, "TYPE SPECIFIER"),
            TokenType::LParen => write!(f, "LPAREN"),
            TokenType::RParen => write!(f, "RPAREN"),
            TokenType::Dot => write!(f, "DOT"),
            TokenType::Semicolon => write!(f, "SEMICOLON"),
            TokenType::Colon => write!(f, "COLON"),
            TokenType::Comma => write!(f, "COMMA"),
            TokenType::Assign => write!(f, "ASSIGN"),
            TokenType::Begin => write!(f, "BEGIN"),
            TokenType::End => write!(f, "END"),
            TokenType::Program => write!(f, "PROGRAM"),
            TokenType::Var => write!(f, "VAR"),
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
    /// 'div' (Integer Division)
    IntegerDivision,
    /// '/' (Float Division)
    FloatDivision,
}

impl fmt::Display for OperatorType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            OperatorType::Plus => write!(f, "'+'"),
            OperatorType::Minus => write!(f, "'-'"),
            OperatorType::Times => write!(f, "'*'"),
            OperatorType::IntegerDivision => write!(f, "'div'"),
            OperatorType::FloatDivision => write!(f, "'/'"),
        }
    }
}

// Defines the type of a variable
#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    /// Integer
    Integer,
    /// Real
    Real,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Type::Integer => write!(f, "INTEGER"),
            Type::Real => write!(f, "REAL"),
        }
    }
}

/// Defines the value of the token (optional).
#[derive(Clone, Debug, PartialEq)]
pub enum TokenValue {
    /// Signed integer as i64
    Integer(i64),
    /// An operator
    Operator(OperatorType),
    /// An identifier name
    Identifier(String),
    /// A type name
    Type(Type),
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
    pub fn extract_integer_value(&self) -> i64 {
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

/// Describes the span of a Token (position in input stream)
#[derive(Clone, Debug, Default)]
pub struct Span {
    /// Start of the span
    pub start: usize,
    /// End of the span
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Span {
            start: start,
            end: end,
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
    pub span: Span,
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
                    TokenValue::Type(ref type_name) => {
                        write!(f, "Token({}, {})", self.token_type, type_name)
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
    pub fn new(token_type: TokenType, value: Option<TokenValue>, span: Span) -> Token {
        Token {
            token_type: token_type,
            value: value,
            span: span,
        }
    }
}
