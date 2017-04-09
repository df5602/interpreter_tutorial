use std::fmt;

use ast::{Ast, AstIndex, AstNode};
use tokens::{Token, TokenValue, Span};
use symbol_table::SymbolTable;
use errors::SyntaxError;
use interpreter::{NodeVisitor, Value};

/// Represents an number.
#[derive(Debug)]
pub struct NumberNode {
    value: Value,
    parent: Option<AstIndex>,
    span: Span,
    token: Token,
}

impl fmt::Display for NumberNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let ty;
        match self.value {
            Value::Integer(_) => ty = "INTEGER",
            Value::Real(_) => ty = "REAL",
            _ => panic!("Internal Error (Number node doesn't contain number)"),
        }

        match self.parent {
            Some(ref i) => {
                write!(f,
                       "Number(parent: {}, value: {}, type: {})",
                       i,
                       self.value,
                       ty)
            }
            None => {
                write!(f,
                       "Number(parent: None, value: {}, type: {})",
                       self.value,
                       ty)
            }
        }
    }
}

impl AstNode for NumberNode {
    fn get_parent(&self) -> Option<AstIndex> {
        self.parent
    }

    fn set_parent(&mut self, parent: AstIndex) -> bool {
        if self.parent != None {
            return false;
        }
        self.parent = Some(parent);
        true
    }

    fn get_children(&self) -> Vec<AstIndex> {
        Vec::new()
    }

    fn get_value(&self) -> Option<TokenValue> {
        match self.value {
            Value::Integer(val) => Some(TokenValue::Integer(val)),
            Value::Real(val) => Some(TokenValue::Real(val)),
            _ => panic!("Internal Error (Number node doesn't contain number)"),
        }
    }

    fn get_span(&self) -> Span {
        self.span.clone()
    }

    fn set_span(&mut self, span: Span) {
        self.span = span;
    }
}

impl NodeVisitor for NumberNode {
    fn visit(&self, _ast: &Ast, _sym_tbl: &mut SymbolTable) -> Result<Value, SyntaxError> {
        Ok(self.value.clone())
    }
}

impl NumberNode {
    /// Constructs a new number node.
    pub fn new(value: Value, token: Token) -> Self {
        NumberNode {
            value: value,
            parent: None,
            span: token.span.clone(),
            token: token,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ast::{Ast, AstNode, AstIndex};
    use tokens::{Token, TokenType, TokenValue, Span};
    use interpreter::{NodeVisitor, Value};

    #[test]
    fn number_node_new_should_set_span_to_token_span() {
        let num_node = NumberNode::new(Value::Integer(42),
                                       Token::new(TokenType::IntegerLiteral,
                                                  Some(TokenValue::Integer(42)),
                                                  Span::new(3, 5)));
        assert_eq!(num_node.get_span(), Span::new(3, 5));
    }

    #[test]
    fn number_node_get_parent_returns_none_when_node_has_no_parent() {
        let num_node = NumberNode::new(Value::Integer(42),
                                       Token::new(TokenType::IntegerLiteral,
                                                  Some(TokenValue::Integer(42)),
                                                  Span::default()));
        assert_eq!(num_node.get_parent(), None);
    }

    #[test]
    fn number_node_set_parent_sets_parent_node() {
        let mut num_node = NumberNode::new(Value::Integer(42),
                                           Token::new(TokenType::IntegerLiteral,
                                                      Some(TokenValue::Integer(42)),
                                                      Span::default()));
        assert!(num_node.set_parent(AstIndex(3)));
        assert_eq!(num_node.get_parent(), Some(AstIndex(3)));
    }

    #[test]
    fn number_node_set_parent_fails_when_node_already_has_parent() {
        let mut num_node = NumberNode::new(Value::Integer(42),
                                           Token::new(TokenType::IntegerLiteral,
                                                      Some(TokenValue::Integer(42)),
                                                      Span::default()));
        assert!(num_node.set_parent(AstIndex(3)));
        assert!(!num_node.set_parent(AstIndex(4)));
    }

    #[test]
    fn number_node_get_children_returns_no_children() {
        let num_node = NumberNode::new(Value::Integer(42),
                                       Token::new(TokenType::IntegerLiteral,
                                                  Some(TokenValue::Integer(42)),
                                                  Span::default()));
        let children = num_node.get_children();
        assert!(children.is_empty());
    }

    #[test]
    fn number_node_get_value_returns_integer_value_if_it_contains_integer_value() {
        let num_node = NumberNode::new(Value::Integer(42),
                                       Token::new(TokenType::IntegerLiteral,
                                                  Some(TokenValue::Integer(42)),
                                                  Span::default()));
        assert_eq!(num_node.get_value().unwrap(), TokenValue::Integer(42));
    }

    #[test]
    fn number_node_get_value_returns_real_value_if_it_contains_real_value() {
        let num_node = NumberNode::new(Value::Real(3.1415),
                                       Token::new(TokenType::RealLiteral,
                                                  Some(TokenValue::Real(3.1415)),
                                                  Span::default()));
        assert_eq!(num_node.get_value().unwrap(), TokenValue::Real(3.1415));
    }

    #[test]
    fn number_node_get_span_returns_span() {
        let num_node = NumberNode::new(Value::Integer(42),
                                       Token::new(TokenType::IntegerLiteral,
                                                  Some(TokenValue::Integer(42)),
                                                  Span::new(3, 5)));
        assert_eq!(num_node.get_span(), Span::new(3, 5));
    }

    #[test]
    fn number_node_visit_returns_integer_value_if_node_contains_integer_value() {
        let num_node = NumberNode::new(Value::Integer(42),
                                       Token::new(TokenType::IntegerLiteral,
                                                  Some(TokenValue::Integer(42)),
                                                  Span::default()));
        let ast = Ast::new();
        let mut sym_tbl = SymbolTable::new();
        assert_eq!(num_node
                       .visit(&ast, &mut sym_tbl)
                       .unwrap()
                       .extract_integer_value(),
                   42);
    }

    #[test]
    fn number_node_visit_returns_real_value_if_node_contains_real_value() {
        let num_node = NumberNode::new(Value::Real(3.1415),
                                       Token::new(TokenType::RealLiteral,
                                                  Some(TokenValue::Real(3.1415)),
                                                  Span::default()));
        let ast = Ast::new();
        let mut sym_tbl = SymbolTable::new();
        assert_eq!(num_node
                       .visit(&ast, &mut sym_tbl)
                       .unwrap()
                       .extract_real_value(),
                   3.1415);
    }
}
