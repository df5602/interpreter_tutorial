use errors::SyntaxError;

pub trait NodeVisitor {
    fn visit(&self) -> Result<i64, SyntaxError>;
}
