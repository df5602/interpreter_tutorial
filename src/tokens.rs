use std::fmt;

//---------------------------------------------------------------------------//
//-TokenType:
//-Each token contains a TokenType, where
//-- Integer    :   A (multi-digit, base 10) unsigned integer
//-- Operator   :   '+' | '-' | '*' | '/'
//-- Eof        :   End of file
//---------------------------------------------------------------------------//

#[derive(Clone, Debug, PartialEq)]
pub enum TokenType {
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

//---------------------------------------------------------------------------//
//-OperatorType:
//-Each operator has one of the following values:
//-- Plus       :   '+' (Addition)
//-- Minus      :   '-' (Subtraction)
//-- Times      :   '*' (Multiplication)
//-- Division   :   '/' (Division)
//---------------------------------------------------------------------------//

#[derive(Clone, Debug, PartialEq)]
pub enum OperatorType {
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

//---------------------------------------------------------------------------//
//-TokenValue:
//-Each Token can have a value:
//-- IntegerValue   :   Unsigned integer as u64
//-- OperatorValue  :   An operator (see OperatorType)
//---------------------------------------------------------------------------//

#[derive(Clone, Debug)]
pub enum TokenValue {
    IntegerValue(u64),
    OperatorValue(OperatorType),
}

//---------------------------------------------------------------------------//
//-Token:
//-Each Token consists of the following elements:
//-- token_type :   The type of the token (see TokenType)
//-- value      :   An optional value (see TokenValue)
//-- position   :   A position in the input stream (for diagnostics reasons)
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
