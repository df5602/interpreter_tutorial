use std::fmt;

//---------------------------------------------------------------------------//
//-TokenType:
//-Each token contains a TokenType, where
//-Integer      :   A (multi-digit, base 10) unsigned integer
//-Operator     :   '+' | '-' | '*' | '/'
//-LParen       :   '('
//-RParen       :   ')'
//-Eof          :   End of file
//---------------------------------------------------------------------------//

#[derive(Clone, Debug, PartialEq)]
pub enum TokenType {
    Integer,
    Operator,
    LParen,
    RParen,
    Eof,
}

impl fmt::Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TokenType::Integer => write!(f, "INTEGER"),
            TokenType::Operator => write!(f, "OPERATOR"),
            TokenType::LParen => write!(f, "LPAREN"),
            TokenType::RParen => write!(f, "RPAREN"),
            TokenType::Eof => write!(f, "EOF"),
        }
    }
}

//---------------------------------------------------------------------------//
//-OperatorType:
//-Each operator has one of the following values:
//-Plus       :   '+' (Addition)
//-Minus      :   '-' (Subtraction)
//-Times      :   '*' (Multiplication)
//-Division   :   '/' (Division)
//-Dummy      :   to get around some "use of possibly uninitialized variable" errors
//---------------------------------------------------------------------------//

#[derive(Clone, Debug, PartialEq)]
pub enum OperatorType {
    Plus,
    Minus,
    Times,
    Division,
    Dummy,
}

impl fmt::Display for OperatorType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            OperatorType::Plus => write!(f, "'+'"),
            OperatorType::Minus => write!(f, "'-'"),
            OperatorType::Times => write!(f, "'*'"),
            OperatorType::Division => write!(f, "'/'"),
            OperatorType::Dummy => write!(f, "DUMMY"),
        }
    }
}

//---------------------------------------------------------------------------//
//-TokenValue:
//-Each Token can have a value:
//-Integer      :   Unsigned integer as u64
//-Operator     :   An operator (see OperatorType)
//-Empty        :   No value (testing only)
//---------------------------------------------------------------------------//

#[derive(Clone, Debug)]
pub enum TokenValue {
    Integer(u64),
    Operator(OperatorType),
    Empty,
}

impl TokenValue {
    pub fn extract_integer_value(&self) -> u64 {
        match *self {
            TokenValue::Integer(value) => value,
            _ => panic!("Internal Error (Integer value has wrong type)"),
        }
    }

    pub fn extract_operator_type(&self) -> OperatorType {
        match *self {
            TokenValue::Operator(ref value) => value.clone(),
            _ => panic!("Internal Error (Operator value has wrong type)"),
        }
    }
}

//---------------------------------------------------------------------------//
//-Token:
//-Each Token consists of the following elements:
//-token_type :   The type of the token (see TokenType)
//-value      :   An optional value (see TokenValue)
//-position   :   A position in the input stream (for diagnostics reasons)
//---------------------------------------------------------------------------//

#[derive(Clone, Debug)]
pub struct Token {
    pub token_type: TokenType,
    pub value: Option<TokenValue>,
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
                    TokenValue::Empty => write!(f, "Token({})", self.token_type),
                }
            }
            None => write!(f, "Token({})", self.token_type),
        }
    }
}

impl Token {
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
