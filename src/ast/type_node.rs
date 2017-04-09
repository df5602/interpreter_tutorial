use std::fmt;

use ast::{Ast, AstIndex, AstNode};
use tokens::{Token, TokenValue, Span, Type};
use symbol_table::SymbolTable;
use errors::SyntaxError;
use interpreter::{NodeVisitor, Value};

/// Represents an type specifier.
#[derive(Debug)]
pub struct TypeNode {
    value: Type,
    parent: Option<AstIndex>,
    span: Span,
    token: Token,
}

impl fmt::Display for TypeNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.parent {
            Some(ref i) => write!(f, "Type Specifier(parent: {}, value: {})", i, self.value),
            None => write!(f, "Type Specifier(parent: None, value: {})", self.value),
        }
    }
}

impl AstNode for TypeNode {
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
        Some(TokenValue::Type(self.value.clone()))
    }

    fn get_span(&self) -> Span {
        self.span.clone()
    }

    fn set_span(&mut self, span: Span) {
        self.span = span;
    }
}

impl NodeVisitor for TypeNode {
    fn visit(&self, _ast: &Ast, _sym_tbl: &mut SymbolTable) -> Result<Value, SyntaxError> {
        Ok(Value::Void)
    }
}

impl TypeNode {
    /// Constructs a new type node.
    pub fn new(value: Type, token: Token) -> Self {
        TypeNode {
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
    use ast::{AstNode, AstIndex};
    use tokens::{Token, TokenType, TokenValue, Span};

    #[test]
    fn type_node_new_should_set_span_to_token_span() {
        let type_node = TypeNode::new(Type::Integer,
                                      Token::new(TokenType::TypeSpecifier,
                                                 Some(TokenValue::Type(Type::Integer)),
                                                 Span::new(3, 5)));
        assert_eq!(type_node.get_span(), Span::new(3, 5));
    }

    #[test]
    fn type_node_get_parent_returns_none_when_node_has_no_parent() {
        let type_node = TypeNode::new(Type::Integer,
                                      Token::new(TokenType::TypeSpecifier,
                                                 Some(TokenValue::Type(Type::Integer)),
                                                 Span::default()));
        assert_eq!(type_node.get_parent(), None);
    }

    #[test]
    fn type_node_set_parent_sets_parent_node() {
        let mut type_node = TypeNode::new(Type::Integer,
                                          Token::new(TokenType::TypeSpecifier,
                                                     Some(TokenValue::Type(Type::Integer)),
                                                     Span::default()));
        assert!(type_node.set_parent(AstIndex(3)));
        assert_eq!(type_node.get_parent(), Some(AstIndex(3)));
    }

    #[test]
    fn type_node_set_parent_fails_when_node_already_has_parent() {
        let mut type_node = TypeNode::new(Type::Integer,
                                          Token::new(TokenType::TypeSpecifier,
                                                     Some(TokenValue::Type(Type::Integer)),
                                                     Span::default()));
        assert!(type_node.set_parent(AstIndex(3)));
        assert!(!type_node.set_parent(AstIndex(4)));
    }

    #[test]
    fn type_node_get_children_returns_no_children() {
        let type_node = TypeNode::new(Type::Integer,
                                      Token::new(TokenType::TypeSpecifier,
                                                 Some(TokenValue::Type(Type::Integer)),
                                                 Span::default()));
        let children = type_node.get_children();
        assert!(children.is_empty());
    }

    #[test]
    fn type_node_get_value_returns_type() {
        let type_node = TypeNode::new(Type::Integer,
                                      Token::new(TokenType::TypeSpecifier,
                                                 Some(TokenValue::Type(Type::Integer)),
                                                 Span::default()));
        assert_eq!(type_node.get_value().unwrap(),
                   TokenValue::Type(Type::Integer));
    }

    #[test]
    fn type_node_get_span_returns_span() {
        let type_node = TypeNode::new(Type::Integer,
                                      Token::new(TokenType::TypeSpecifier,
                                                 Some(TokenValue::Type(Type::Integer)),
                                                 Span::new(3, 5)));
        assert_eq!(type_node.get_span(), Span::new(3, 5));
    }

    #[test]
    fn type_node_set_span_sets_span() {
        let mut type_node = TypeNode::new(Type::Integer,
                                          Token::new(TokenType::TypeSpecifier,
                                                     Some(TokenValue::Type(Type::Integer)),
                                                     Span::new(3, 5)));
        type_node.set_span(Span::new(2, 5));
        assert_eq!(type_node.get_span(), Span::new(2, 5));
    }

    #[test]
    fn type_node_visit_returns_void() {
        let mut ast = Ast::new();

        let type_node = type_node!(ast, Type::Integer);

        let mut sym_tbl = SymbolTable::new();
        assert_eq!(ast.get_node(type_node)
                       .visit(&ast, &mut sym_tbl)
                       .unwrap(),
                   Value::Void);
    }
}
