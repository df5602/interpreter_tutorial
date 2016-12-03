use tokens::*;
use errors::SyntaxError;

mod pascal_lexer;

pub use self::pascal_lexer::PascalLexer;

pub trait Lexer {
    fn get_next_token(&self) -> Result<Token, SyntaxError>;
    fn get_position(&self) -> usize;
}
