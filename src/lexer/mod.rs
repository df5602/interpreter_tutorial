//! This module contains the lexer.
//! Given an input string, it generates a stream of `Token`s.

use tokens::*;
use errors::SyntaxError;

mod pascal_lexer;
pub use self::pascal_lexer::PascalLexer;

#[cfg(test)]
#[macro_use]
mod mock_lexer;
#[cfg(test)]
pub use self::mock_lexer::MockLexer;

/// Public interface that a specific lexer needs to satisfy.
pub trait Lexer {
    /// Returns next `Token` in the input stream or a `SyntaxError` if
    /// no valid token can be recognized.
    fn get_next_token(&self) -> Result<Token, SyntaxError>;
    /// Returns the actual position in the input stream.
    fn get_position(&self) -> usize;
}
