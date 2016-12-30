use std::fmt;
use std::collections::HashMap;

use ast::{Ast, AstNode, AstIndex};
use tokens::{Token, TokenValue, OperatorType};
use errors::SyntaxError;
use interpreter::{NodeVisitor, ReturnValue};

/// Binary Operator node.
/// Binary operators are '+', '-', '*' and '/'.
#[derive(Debug)]
pub struct BinaryOperatorNode {
    left: AstIndex,
    right: AstIndex,
    operator: OperatorType,
    parent: Option<AstIndex>,
    position: (usize, usize),
    token: Token,
}

impl fmt::Display for BinaryOperatorNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.parent {
            Some(ref i) => {
                write!(f,
                       "BinaryOperator(left: {}, right: {}, parent: {}, op: {})",
                       self.left,
                       self.right,
                       i,
                       self.operator)
            }
            None => {
                write!(f,
                       "BinaryOperator(left: {}, right: {}, parent: None, op: {})",
                       self.left,
                       self.right,
                       self.operator)
            }
        }
    }
}

impl AstNode for BinaryOperatorNode {
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
                format!("BinaryOperator(left: {}, right: {}, parent: {}, op: {})",
                        self.left,
                        self.right,
                        i,
                        self.operator)
            }
            None => {
                format!("BinaryOperator(left: {}, right: {}, parent: None, op: {})",
                        self.left,
                        self.right,
                        self.operator)
            }
        }
    }
}

impl NodeVisitor for BinaryOperatorNode {
    fn visit(&self,
             ast: &Ast,
             sym_tbl: &mut HashMap<String, i64>)
             -> Result<ReturnValue, SyntaxError> {
        let lhs = ast.get_node(self.left).visit(ast, sym_tbl)?.extract_integer_value();
        let rhs = ast.get_node(self.right).visit(ast, sym_tbl)?.extract_integer_value();

        match self.operator {
            OperatorType::Plus => Ok(ReturnValue::Integer(lhs + rhs)),
            OperatorType::Minus => Ok(ReturnValue::Integer(lhs - rhs)),
            OperatorType::Times => Ok(ReturnValue::Integer(lhs * rhs)),
            OperatorType::Division => {
                if rhs == 0 {
                    Err(SyntaxError {
                        msg: "Division by zero".to_string(),
                        position: self.position,
                    })
                } else {
                    Ok(ReturnValue::Integer(lhs / rhs))
                }
            }
        }
    }
}

impl BinaryOperatorNode {
    /// Constructs a new binary operator node.
    pub fn new(left: AstIndex, right: AstIndex, operator: OperatorType, token: Token) -> Self {
        BinaryOperatorNode {
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
    use std::collections::HashMap;

    use super::*;
    use ast::{Ast, AstNode, AstIndex, IntegerNode};
    use tokens::{Token, TokenType, TokenValue, OperatorType};

    #[test]
    fn binary_operator_node_get_parent_returns_none_when_node_has_no_parent() {
        let op_node =
            BinaryOperatorNode::new(AstIndex(0),
                                    AstIndex(1),
                                    OperatorType::Plus,
                                    Token::new(TokenType::Operator,
                                               Some(TokenValue::Operator(OperatorType::Plus)),
                                               (0, 0)));
        assert_eq!(op_node.get_parent(), None);
    }

    #[test]
    fn binary_operator_node_set_parent_sets_parent_node() {
        let mut op_node =
            BinaryOperatorNode::new(AstIndex(0),
                                    AstIndex(1),
                                    OperatorType::Plus,
                                    Token::new(TokenType::Operator,
                                               Some(TokenValue::Operator(OperatorType::Plus)),
                                               (0, 0)));
        assert!(op_node.set_parent(AstIndex(3)));
        assert_eq!(op_node.get_parent(), Some(AstIndex(3)));
    }

    #[test]
    fn binary_operator_node_set_parent_fails_when_node_already_has_parent() {
        let mut op_node =
            BinaryOperatorNode::new(AstIndex(0),
                                    AstIndex(1),
                                    OperatorType::Plus,
                                    Token::new(TokenType::Operator,
                                               Some(TokenValue::Operator(OperatorType::Plus)),
                                               (0, 0)));
        assert!(op_node.set_parent(AstIndex(3)));
        assert!(!op_node.set_parent(AstIndex(4)));
    }

    #[test]
    fn binary_operator_node_get_children_returns_left_and_right_children() {
        let op_node =
            BinaryOperatorNode::new(AstIndex(0),
                                    AstIndex(1),
                                    OperatorType::Plus,
                                    Token::new(TokenType::Operator,
                                               Some(TokenValue::Operator(OperatorType::Plus)),
                                               (0, 0)));
        let children = op_node.get_children();
        assert_eq!(children[0], AstIndex(0));
        assert_eq!(children[1], AstIndex(1));
        assert_eq!(children.len(), 2);
    }

    #[test]
    fn binary_operator_node_get_value_returns_operator_value() {
        let op_node =
            BinaryOperatorNode::new(AstIndex(0),
                                    AstIndex(1),
                                    OperatorType::Plus,
                                    Token::new(TokenType::Operator,
                                               Some(TokenValue::Operator(OperatorType::Plus)),
                                               (0, 0)));
        assert_eq!(op_node.get_value().unwrap(),
                   TokenValue::Operator(OperatorType::Plus));
    }

    #[test]
    fn binary_operator_node_get_position_returns_position() {
        let mut op_node =
            BinaryOperatorNode::new(AstIndex(0),
                                    AstIndex(1),
                                    OperatorType::Plus,
                                    Token::new(TokenType::Operator,
                                               Some(TokenValue::Operator(OperatorType::Plus)),
                                               (3, 5)));
        op_node.set_position((4, 5));
        assert_eq!(op_node.get_position(), (4, 5));
    }

    #[test]
    fn binary_operator_node_visit_returns_sum_of_integer_nodes_when_op_is_addition() {
        let int_node_left =
            IntegerNode::new(2,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(2)), (0, 0)));
        let int_node_right =
            IntegerNode::new(4,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(4)), (0, 0)));
        let mut ast = Ast::new();
        let index_left = ast.add_node(int_node_left);
        let index_right = ast.add_node(int_node_right);

        let op_node =
            BinaryOperatorNode::new(index_left,
                                    index_right,
                                    OperatorType::Plus,
                                    Token::new(TokenType::Operator,
                                               Some(TokenValue::Operator(OperatorType::Plus)),
                                               (0, 0)));
        let index_op = ast.add_node(op_node);
        let mut sym_tbl = HashMap::new();
        assert_eq!(ast.get_node(index_op)
                       .visit(&ast, &mut sym_tbl)
                       .unwrap()
                       .extract_integer_value(),
                   6);
    }

    #[test]
    fn binary_operator_node_visit_returns_difference_of_integer_nodes_when_op_is_subtraction() {
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
            BinaryOperatorNode::new(index_left,
                                    index_right,
                                    OperatorType::Minus,
                                    Token::new(TokenType::Operator,
                                               Some(TokenValue::Operator(OperatorType::Minus)),
                                               (0, 0)));
        let index_op = ast.add_node(op_node);
        let mut sym_tbl = HashMap::new();
        assert_eq!(ast.get_node(index_op)
                       .visit(&ast, &mut sym_tbl)
                       .unwrap()
                       .extract_integer_value(),
                   2);
    }

    #[test]
    fn binary_operator_node_visit_returns_product_of_integer_nodes_when_op_is_multiplication() {
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
            BinaryOperatorNode::new(index_left,
                                    index_right,
                                    OperatorType::Times,
                                    Token::new(TokenType::Operator,
                                               Some(TokenValue::Operator(OperatorType::Times)),
                                               (0, 0)));
        let index_op = ast.add_node(op_node);
        let mut sym_tbl = HashMap::new();
        assert_eq!(ast.get_node(index_op)
                       .visit(&ast, &mut sym_tbl)
                       .unwrap()
                       .extract_integer_value(),
                   8);
    }

    #[test]
    fn binary_operator_node_visit_returns_quotient_of_integer_nodes_when_op_is_division() {
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
            BinaryOperatorNode::new(index_left,
                                    index_right,
                                    OperatorType::Division,
                                    Token::new(TokenType::Operator,
                                               Some(TokenValue::Operator(OperatorType::Division)),
                                               (0, 0)));
        let index_op = ast.add_node(op_node);
        let mut sym_tbl = HashMap::new();
        assert_eq!(ast.get_node(index_op)
                       .visit(&ast, &mut sym_tbl)
                       .unwrap()
                       .extract_integer_value(),
                   2);
    }

    #[test]
    fn binary_operator_node_visit_returns_error_when_op_is_division_and_rhs_is_zero() {
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
            BinaryOperatorNode::new(index_left,
                                    index_right,
                                    OperatorType::Division,
                                    Token::new(TokenType::Operator,
                                               Some(TokenValue::Operator(OperatorType::Division)),
                                               (0, 0)));
        let index_op = ast.add_node(op_node);
        let mut sym_tbl = HashMap::new();
        assert!(ast.get_node(index_op).visit(&ast, &mut sym_tbl).is_err());
    }
}
