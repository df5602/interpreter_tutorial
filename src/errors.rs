//! This module contains error definitions.

/// Defines a syntax error.
#[derive(Debug)]
pub struct SyntaxError {
    /// The error message
    pub msg: String,
    /// The position in the input stream where the error occurred
    pub position: (usize, usize),
}
