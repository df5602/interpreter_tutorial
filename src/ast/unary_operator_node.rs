use std::fmt;

use tokens::{Token, OperatorType, TokenValue};
use ast::{Ast, AstNode, AstIndex};
use errors::SyntaxError;
use interpreter::NodeVisitor;

/// Unary operator node.
/// Unary operators are '+' and '-' in front of expressions.
#[derive(Debug)]
pub struct UnaryOperatorNode {
    operand: AstIndex,
    operator: OperatorType,
    parent: Option<AstIndex>,
    position: (usize, usize),
    token: Token,
}

impl fmt::Display for UnaryOperatorNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.parent {
            Some(ref i) => {
                write!(f,
                       "UnaryOperator(operand: {}, parent: {}, op: {})",
                       self.operand,
                       i,
                       self.operator)
            }
            None => {
                write!(f,
                       "UnaryOperator(operand: {}, parent: None, op: {})",
                       self.operand,
                       self.operator)
            }
        }
    }
}

impl AstNode for UnaryOperatorNode {
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
        vec![self.operand]
    }

    fn get_value(&self) -> Option<TokenValue> {
        Some(TokenValue::Operator(self.operator.clone()))
    }

    fn get_position(&self) -> (usize, usize) {
        self.position
    }

    fn set_position(&mut self, position: (usize, usize)) {
        self.position = position;
    }

    fn print(&self) -> String {
        match self.parent {
            Some(ref i) => {
                format!("UnaryOperator(operand: {}, parent: {}, op: {})",
                        self.operand,
                        i,
                        self.operator)
            }
            None => {
                format!("UnaryOperator(operand: {}, parent: None, op: {})",
                        self.operand,
                        self.operator)
            }
        }
    }
}

impl NodeVisitor for UnaryOperatorNode {
    fn visit(&self, ast: &Ast) -> Result<i64, SyntaxError> {
        let operand = ast.get_node(self.operand).visit(ast)?;

        match self.operator {
            OperatorType::Plus => Ok(operand),
            OperatorType::Minus => Ok(-operand),
            _ => panic!("Internal error (Unsupported operator type for unary operator)"),
        }
    }
}

impl UnaryOperatorNode {
    /// Constructs a new unary operator node.
    pub fn new(operand: AstIndex, operator: OperatorType, token: Token) -> Self {
        UnaryOperatorNode {
            operand: operand,
            operator: operator,
            parent: None,
            position: (0, 0),
            token: token,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokens::{Token, TokenType, OperatorType, TokenValue};
    use ast::{Ast, AstNode, AstIndex, IntegerNode};

    #[test]
    fn unary_operator_node_get_parent_returns_none_when_node_has_no_parent() {
        let op_node =
            UnaryOperatorNode::new(AstIndex(0),
                                   OperatorType::Minus,
                                   Token::new(TokenType::Operator,
                                              Some(TokenValue::Operator(OperatorType::Minus)),
                                              (0, 0)));
        assert_eq!(op_node.get_parent(), None);
    }

    #[test]
    fn unary_operator_node_set_parent_sets_parent_node() {
        let mut op_node =
            UnaryOperatorNode::new(AstIndex(0),
                                   OperatorType::Minus,
                                   Token::new(TokenType::Operator,
                                              Some(TokenValue::Operator(OperatorType::Minus)),
                                              (0, 0)));
        assert!(op_node.set_parent(AstIndex(2)));
        assert_eq!(op_node.get_parent(), Some(AstIndex(2)));
    }

    #[test]
    fn unary_operator_node_set_parent_fails_when_node_already_has_parent() {
        let mut op_node =
            UnaryOperatorNode::new(AstIndex(0),
                                   OperatorType::Minus,
                                   Token::new(TokenType::Operator,
                                              Some(TokenValue::Operator(OperatorType::Minus)),
                                              (0, 0)));
        assert!(op_node.set_parent(AstIndex(2)));
        assert!(!op_node.set_parent(AstIndex(3)));
    }

    #[test]
    fn unary_operator_node_get_children_returns_operand() {
        let op_node =
            UnaryOperatorNode::new(AstIndex(0),
                                   OperatorType::Minus,
                                   Token::new(TokenType::Operator,
                                              Some(TokenValue::Operator(OperatorType::Minus)),
                                              (0, 0)));
        let children = op_node.get_children();
        assert_eq!(children[0], AstIndex(0));
        assert_eq!(children.len(), 1);
    }

    #[test]
    fn unary_operator_node_get_value_returns_operator_value() {
        let op_node =
            UnaryOperatorNode::new(AstIndex(0),
                                   OperatorType::Minus,
                                   Token::new(TokenType::Operator,
                                              Some(TokenValue::Operator(OperatorType::Minus)),
                                              (0, 0)));
        assert_eq!(op_node.get_value().unwrap(),
                   TokenValue::Operator(OperatorType::Minus));
    }

    #[test]
    fn unary_operator_node_get_position_returns_position() {
        let mut op_node =
            UnaryOperatorNode::new(AstIndex(0),
                                   OperatorType::Minus,
                                   Token::new(TokenType::Operator,
                                              Some(TokenValue::Operator(OperatorType::Minus)),
                                              (3, 5)));
        op_node.set_position((4, 5));
        assert_eq!(op_node.get_position(), (4, 5));
    }

    #[test]
    fn unary_operator_node_visit_returns_operand_when_op_is_addition() {
        let operand =
            IntegerNode::new(2,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(2)), (0, 0)));

        let mut ast = Ast::new();
        let index_operand = ast.add_node(operand);

        let op_node =
            UnaryOperatorNode::new(index_operand,
                                   OperatorType::Plus,
                                   Token::new(TokenType::Operator,
                                              Some(TokenValue::Operator(OperatorType::Plus)),
                                              (0, 0)));
        let index_op = ast.add_node(op_node);
        assert_eq!(ast.get_node(index_op).visit(&ast).unwrap(), 2);
    }

    #[test]
    fn unary_operator_node_visit_returns_negative_operand_when_op_is_subtraction() {
        let operand =
            IntegerNode::new(4,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(4)), (0, 0)));

        let mut ast = Ast::new();
        let index_operand = ast.add_node(operand);

        let op_node =
            UnaryOperatorNode::new(index_operand,
                                   OperatorType::Minus,
                                   Token::new(TokenType::Operator,
                                              Some(TokenValue::Operator(OperatorType::Minus)),
                                              (0, 0)));
        let index_op = ast.add_node(op_node);
        assert_eq!(ast.get_node(index_op).visit(&ast).unwrap(), -4);
    }
}
