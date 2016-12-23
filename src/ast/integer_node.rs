use std::fmt;

use ast::{AstIndex, AstNode};
use tokens::{Token, TokenValue};
use errors::SyntaxError;
use interpreter::NodeVisitor;

#[derive(Debug)]
pub struct IntegerNode {
    value: u64,
    parent: Option<AstIndex>,
    token: Token,
}

impl fmt::Display for IntegerNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.parent {
            Some(ref i) => write!(f, "Integer(parent: {}, value: {})", i, self.value),
            None => write!(f, "Integer(parent: None, value: {})", self.value),
        }
    }
}

impl AstNode for IntegerNode {
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

    fn get_value(&self) -> TokenValue {
        TokenValue::Integer(self.value)
    }

    fn print(&self) -> String {
        match self.parent {
            Some(ref i) => format!("Integer(parent: {}, value: {})", i, self.value),
            None => format!("Integer(parent: None, value: {})", self.value),
        }
    }
}

impl NodeVisitor for IntegerNode {
    fn visit(&self) -> Result<i64, SyntaxError> {
        unimplemented!();
    }
}

impl IntegerNode {
    pub fn new(value: u64, token: Token) -> Self {
        IntegerNode {
            value: value,
            parent: None,
            token: token,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ast::{AstNode, AstIndex};
    use tokens::{Token, TokenType, TokenValue};

    #[test]
    fn integer_node_get_parent_returns_none_when_node_has_no_parent() {
        let int_node =
            IntegerNode::new(42,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(42)), (0, 0)));
        assert_eq!(int_node.get_parent(), None);
    }

    #[test]
    fn integer_node_set_parent_sets_parent_node() {
        let mut int_node =
            IntegerNode::new(42,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(42)), (0, 0)));
        assert!(int_node.set_parent(AstIndex(3)));
        assert_eq!(int_node.get_parent(), Some(AstIndex(3)));
    }

    #[test]
    fn integer_node_set_parent_fails_when_node_already_has_parent() {
        let mut int_node =
            IntegerNode::new(42,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(42)), (0, 0)));
        assert!(int_node.set_parent(AstIndex(3)));
        assert!(!int_node.set_parent(AstIndex(4)));
    }

    #[test]
    fn integer_node_get_children_returns_no_children() {
        let int_node =
            IntegerNode::new(42,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(42)), (0, 0)));
        let children = int_node.get_children();
        assert!(children.is_empty());
    }

    #[test]
    fn integer_node_get_value_returns_integer_value() {
        let int_node =
            IntegerNode::new(42,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(42)), (0, 0)));
        assert_eq!(int_node.get_value(), TokenValue::Integer(42));
    }
}
