use errors::SyntaxError;
use ast::Ast;

pub trait NodeVisitor {
    fn visit(&self, ast: &Ast) -> Result<i64, SyntaxError>;
}
