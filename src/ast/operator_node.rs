use std::fmt;

use ast::{Ast, AstNode, AstIndex};
use tokens::{Token, TokenValue, OperatorType};
use errors::SyntaxError;
use interpreter::NodeVisitor;

#[derive(Debug)]
pub struct OperatorNode {
    left: AstIndex,
    right: AstIndex,
    operator: OperatorType,
    parent: Option<AstIndex>,
    position: (usize, usize),
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

    fn get_position(&self) -> (usize, usize) {
        self.position
    }

    fn set_position(&mut self, position: (usize, usize)) {
        self.position = position;
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
    fn visit(&self, ast: &Ast) -> Result<i64, SyntaxError> {
        let lhs = ast.get_node(self.left).visit(ast)?;
        let rhs = ast.get_node(self.right).visit(ast)?;

        match self.operator {
            OperatorType::Plus => Ok(lhs + rhs),
            OperatorType::Minus => Ok(lhs - rhs),
            OperatorType::Times => Ok(lhs * rhs),
            OperatorType::Division => {
                if rhs == 0 {
                    Err(SyntaxError {
                        msg: "Division by zero".to_string(),
                        position: self.position,
                    })
                } else {
                    Ok(lhs / rhs)
                }
            }
        }
    }
}

impl OperatorNode {
    pub fn new(left: AstIndex, right: AstIndex, operator: OperatorType, token: Token) -> Self {
        OperatorNode {
            left: left,
            right: right,
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
    use ast::{Ast, AstNode, AstIndex, IntegerNode};
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

    #[test]
    fn operator_node_get_position_returns_position() {
        let mut op_node =
            OperatorNode::new(AstIndex(0),
                              AstIndex(1),
                              OperatorType::Plus,
                              Token::new(TokenType::Operator,
                                         Some(TokenValue::Operator(OperatorType::Plus)),
                                         (3, 5)));
        op_node.set_position((4, 5));
        assert_eq!(op_node.get_position(), (4, 5));
    }

    #[test]
    fn operator_node_visit_returns_sum_of_integer_nodes_when_op_is_addition() {
        let int_node_left =
            IntegerNode::new(2,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(2)), (0, 0)));
        let int_node_right =
            IntegerNode::new(4,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(4)), (0, 0)));
        let mut ast = Ast::new();
        let index_left = ast.add_node(int_node_left);
        let index_right = ast.add_node(int_node_right);

        let op_node = OperatorNode::new(index_left,
                                        index_right,
                                        OperatorType::Plus,
                                        Token::new(TokenType::Operator,
                                                   Some(TokenValue::Operator(OperatorType::Plus)),
                                                   (0, 0)));
        let index_op = ast.add_node(op_node);
        assert_eq!(ast.get_node(index_op).visit(&ast).unwrap(), 6);
    }

    #[test]
    fn operator_node_visit_returns_difference_of_integer_nodes_when_op_is_subtraction() {
        let int_node_left =
            IntegerNode::new(4,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(4)), (0, 0)));
        let int_node_right =
            IntegerNode::new(2,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(2)), (0, 0)));
        let mut ast = Ast::new();
        let index_left = ast.add_node(int_node_left);
        let index_right = ast.add_node(int_node_right);

        let op_node =
            OperatorNode::new(index_left,
                              index_right,
                              OperatorType::Minus,
                              Token::new(TokenType::Operator,
                                         Some(TokenValue::Operator(OperatorType::Minus)),
                                         (0, 0)));
        let index_op = ast.add_node(op_node);
        assert_eq!(ast.get_node(index_op).visit(&ast).unwrap(), 2);
    }

    #[test]
    fn operator_node_visit_returns_product_of_integer_nodes_when_op_is_multiplication() {
        let int_node_left =
            IntegerNode::new(4,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(4)), (0, 0)));
        let int_node_right =
            IntegerNode::new(2,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(2)), (0, 0)));
        let mut ast = Ast::new();
        let index_left = ast.add_node(int_node_left);
        let index_right = ast.add_node(int_node_right);

        let op_node =
            OperatorNode::new(index_left,
                              index_right,
                              OperatorType::Times,
                              Token::new(TokenType::Operator,
                                         Some(TokenValue::Operator(OperatorType::Times)),
                                         (0, 0)));
        let index_op = ast.add_node(op_node);
        assert_eq!(ast.get_node(index_op).visit(&ast).unwrap(), 8);
    }

    #[test]
    fn operator_node_visit_returns_quotient_of_integer_nodes_when_op_is_division() {
        let int_node_left =
            IntegerNode::new(4,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(4)), (0, 0)));
        let int_node_right =
            IntegerNode::new(2,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(2)), (0, 0)));
        let mut ast = Ast::new();
        let index_left = ast.add_node(int_node_left);
        let index_right = ast.add_node(int_node_right);

        let op_node =
            OperatorNode::new(index_left,
                              index_right,
                              OperatorType::Division,
                              Token::new(TokenType::Operator,
                                         Some(TokenValue::Operator(OperatorType::Division)),
                                         (0, 0)));
        let index_op = ast.add_node(op_node);
        assert_eq!(ast.get_node(index_op).visit(&ast).unwrap(), 2);
    }

    #[test]
    fn operator_node_visit_returns_error_when_op_is_division_and_rhs_is_zero() {
        let int_node_left =
            IntegerNode::new(4,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(4)), (0, 0)));
        let int_node_right =
            IntegerNode::new(0,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(0)), (0, 0)));
        let mut ast = Ast::new();
        let index_left = ast.add_node(int_node_left);
        let index_right = ast.add_node(int_node_right);

        let op_node =
            OperatorNode::new(index_left,
                              index_right,
                              OperatorType::Division,
                              Token::new(TokenType::Operator,
                                         Some(TokenValue::Operator(OperatorType::Division)),
                                         (0, 0)));
        let index_op = ast.add_node(op_node);
        assert!(ast.get_node(index_op).visit(&ast).is_err());
    }
}
