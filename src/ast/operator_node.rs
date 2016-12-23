use std::fmt;

use ast::{AstNode, AstIndex};
use tokens::{Token, TokenValue, OperatorType};
use errors::SyntaxError;
use interpreter::NodeVisitor;

#[derive(Debug)]
pub struct OperatorNode {
    left: AstIndex,
    right: AstIndex,
    operator: OperatorType,
    parent: Option<AstIndex>,
    token: Token,
}

impl fmt::Display for OperatorNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.parent {
            Some(ref i) => {
                write!(f,
                       "Operator(left: {}, right: {}, parent: {}, op: {})",
                       self.left,
                       self.right,
                       i,
                       self.operator)
            }
            None => {
                write!(f,
                       "Operator(left: {}, right: {}, parent: None, op: {})",
                       self.left,
                       self.right,
                       self.operator)
            }
        }
    }
}

impl AstNode for OperatorNode {
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
        vec![self.left, self.right]
    }

    fn get_value(&self) -> TokenValue {
        TokenValue::Operator(self.operator.clone())
    }

    fn print(&self) -> String {
        match self.parent {
            Some(ref i) => {
                format!("Operator(left: {}, right: {}, parent: {}, op: {})",
                        self.left,
                        self.right,
                        i,
                        self.operator)
            }
            None => {
                format!("Operator(left: {}, right: {}, parent: None, op: {})",
                        self.left,
                        self.right,
                        self.operator)
            }
        }
    }
}

impl NodeVisitor for OperatorNode {
    fn visit(&self) -> Result<i64, SyntaxError> {
        unimplemented!();
    }
}

impl OperatorNode {
    pub fn new(left: AstIndex, right: AstIndex, operator: OperatorType, token: Token) -> Self {
        OperatorNode {
            left: left,
            right: right,
            operator: operator,
            parent: None,
            token: token,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ast::{AstNode, AstIndex};
    use tokens::{Token, TokenType, TokenValue, OperatorType};

    #[test]
    fn operator_node_get_parent_returns_none_when_node_has_no_parent() {
        let op_node = OperatorNode::new(AstIndex(0),
                                        AstIndex(1),
                                        OperatorType::Plus,
                                        Token::new(TokenType::Operator,
                                                   Some(TokenValue::Operator(OperatorType::Plus)),
                                                   (0, 0)));
        assert_eq!(op_node.get_parent(), None);
    }

    #[test]
    fn operator_node_set_parent_sets_parent_node() {
        let mut op_node =
            OperatorNode::new(AstIndex(0),
                              AstIndex(1),
                              OperatorType::Plus,
                              Token::new(TokenType::Operator,
                                         Some(TokenValue::Operator(OperatorType::Plus)),
                                         (0, 0)));
        assert!(op_node.set_parent(AstIndex(3)));
        assert_eq!(op_node.get_parent(), Some(AstIndex(3)));
    }

    #[test]
    fn operator_node_set_parent_fails_when_node_already_has_parent() {
        let mut op_node =
            OperatorNode::new(AstIndex(0),
                              AstIndex(1),
                              OperatorType::Plus,
                              Token::new(TokenType::Operator,
                                         Some(TokenValue::Operator(OperatorType::Plus)),
                                         (0, 0)));
        assert!(op_node.set_parent(AstIndex(3)));
        assert!(!op_node.set_parent(AstIndex(4)));
    }

    #[test]
    fn operator_node_get_children_returns_left_and_right_children() {
        let op_node = OperatorNode::new(AstIndex(0),
                                        AstIndex(1),
                                        OperatorType::Plus,
                                        Token::new(TokenType::Operator,
                                                   Some(TokenValue::Operator(OperatorType::Plus)),
                                                   (0, 0)));
        let children = op_node.get_children();
        assert_eq!(children[0], AstIndex(0));
        assert_eq!(children[1], AstIndex(1));
    }

    #[test]
    fn operator_node_get_value_returns_operator_value() {
        let op_node = OperatorNode::new(AstIndex(0),
                                        AstIndex(1),
                                        OperatorType::Plus,
                                        Token::new(TokenType::Operator,
                                                   Some(TokenValue::Operator(OperatorType::Plus)),
                                                   (0, 0)));
        assert_eq!(op_node.get_value(),
                   TokenValue::Operator(OperatorType::Plus));
    }
}
