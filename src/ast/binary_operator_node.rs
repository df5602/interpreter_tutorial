use std::fmt;

use ast::{Ast, AstNode, AstIndex};
use symbol_table::SymbolTable;
use tokens::{Token, TokenValue, OperatorType, Span};
use errors::SyntaxError;
use interpreter::{NodeVisitor, Value};

/// Binary Operator node.
/// Binary operators are '+', '-', '*' and '/'.
#[derive(Debug)]
pub struct BinaryOperatorNode {
    left: AstIndex,
    right: AstIndex,
    operator: OperatorType,
    parent: Option<AstIndex>,
    span: Span,
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

    fn get_span(&self) -> Span {
        self.span.clone()
    }

    fn set_span(&mut self, span: Span) {
        self.span = span;
    }
}

#[allow(unknown_lints)]
#[allow(op_ref)] // rust-clippy Issue #1662 ("false positive on op_ref lint")
impl NodeVisitor for BinaryOperatorNode {
    fn visit(&self, ast: &Ast, sym_tbl: &mut SymbolTable) -> Result<Value, SyntaxError> {
        let lhs = ast.get_node(self.left).visit(ast, sym_tbl)?;
        let rhs = ast.get_node(self.right).visit(ast, sym_tbl)?;

        // Use std::ops::{Add, Sub, Mul, Div} traits implemented for &Value to
        // perform calculations
        let result = match self.operator {
            OperatorType::Plus => &lhs + &rhs,
            OperatorType::Minus => &lhs - &rhs,
            OperatorType::Times => &lhs * &rhs,
            OperatorType::IntegerDivision |
            OperatorType::FloatDivision => {
                if rhs.is_zero() {
                    return Err(SyntaxError {
                                   msg: "Division by zero".to_string(),
                                   span: self.span.clone(),
                               });
                } else {
                    match &lhs / &rhs {
                        Some(Value::Real(value)) if self.operator ==
                                                    OperatorType::IntegerDivision => {
                            // Truncate, since we are performing an integer division
                            Some(Value::Real(value.floor()))
                        }
                        value => value,
                    }
                }
            }
        };

        match result {
            Some(value) => Ok(value),
            None => {
                let left = match ast.get_node(self.left).get_value() {
                    Some(value) => {
                        match value {
                            TokenValue::Identifier(name) => format!("`{}`", name),
                            _ => "left".to_string(),
                        }
                    }
                    None => "left".to_string(),
                };

                let right = match ast.get_node(self.right).get_value() {
                    Some(value) => {
                        match value {
                            TokenValue::Identifier(name) => format!("`{}`", name),
                            _ => "right".to_string(),
                        }
                    }
                    None => "right".to_string(),
                };

                Err(SyntaxError {
                        msg: format!("Integer overflow [{}: {}; {}: {}]", left, lhs, right, rhs),
                        span: self.span.clone(),
                    })
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
            span: Span::new(0, 0),
            token: token,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::i64;

    use super::*;
    use ast::{Ast, AstNode, AstIndex, NumberNode};
    use tokens::{Token, TokenType, TokenValue, OperatorType, Span};

    #[test]
    fn binary_operator_node_get_parent_returns_none_when_node_has_no_parent() {
        let op_node =
            BinaryOperatorNode::new(AstIndex(0),
                                    AstIndex(1),
                                    OperatorType::Plus,
                                    Token::new(TokenType::Operator,
                                               Some(TokenValue::Operator(OperatorType::Plus)),
                                               Span::default()));
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
                                               Span::default()));
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
                                               Span::default()));
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
                                               Span::default()));
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
                                               Span::default()));
        assert_eq!(op_node.get_value().unwrap(),
                   TokenValue::Operator(OperatorType::Plus));
    }

    #[test]
    fn binary_operator_node_get_span_returns_span() {
        let mut op_node =
            BinaryOperatorNode::new(AstIndex(0),
                                    AstIndex(1),
                                    OperatorType::Plus,
                                    Token::new(TokenType::Operator,
                                               Some(TokenValue::Operator(OperatorType::Plus)),
                                               Span::new(3, 5)));
        op_node.set_span(Span::new(4, 5));
        assert_eq!(op_node.get_span(), Span::new(4, 5));
    }

    #[test]
    fn binary_operator_node_visit_returns_sum_of_integer_nodes_when_op_is_addition() {
        let mut ast = Ast::new();
        let index_op = binop_node!(ast,
                                   int_node!(ast, 2),
                                   int_node!(ast, 4),
                                   OperatorType::Plus);
        let mut sym_tbl = SymbolTable::new();
        assert_eq!(ast.get_node(index_op)
                       .visit(&ast, &mut sym_tbl)
                       .unwrap()
                       .extract_integer_value(),
                   6);
    }

    #[test]
    fn binary_operator_node_visit_returns_real_sum_if_at_least_one_operand_is_a_real() {
        let mut ast = Ast::new();
        let index_op = binop_node!(ast,
                                   int_node!(ast, 2),
                                   real_node!(ast, 2.4),
                                   OperatorType::Plus);
        let mut sym_tbl = SymbolTable::new();
        assert_eq!(ast.get_node(index_op)
                       .visit(&ast, &mut sym_tbl)
                       .unwrap()
                       .extract_real_value(),
                   4.4);
    }

    #[test]
    fn binary_operator_node_visit_returns_error_when_addition_overflows() {
        let mut ast = Ast::new();
        let index_op = binop_node!(ast,
                                   int_node!(ast, i64::MAX),
                                   int_node!(ast, 1),
                                   OperatorType::Plus);
        let mut sym_tbl = SymbolTable::new();
        assert!(ast.get_node(index_op)
                    .visit(&ast, &mut sym_tbl)
                    .is_err());
    }

    #[test]
    fn binary_operator_node_visit_returns_real_difference_if_at_least_one_operand_is_real() {
        let mut ast = Ast::new();
        let index_op = binop_node!(ast,
                                   real_node!(ast, 4.76),
                                   int_node!(ast, 2),
                                   OperatorType::Minus);
        let mut sym_tbl = SymbolTable::new();
        assert_eq!(ast.get_node(index_op)
                       .visit(&ast, &mut sym_tbl)
                       .unwrap()
                       .extract_real_value(),
                   2.76);
    }

    #[test]
    fn binary_operator_node_visit_returns_difference_of_integer_nodes_when_op_is_subtraction() {
        let mut ast = Ast::new();
        let index_op = binop_node!(ast,
                                   int_node!(ast, 4),
                                   int_node!(ast, 2),
                                   OperatorType::Minus);
        let mut sym_tbl = SymbolTable::new();
        assert_eq!(ast.get_node(index_op)
                       .visit(&ast, &mut sym_tbl)
                       .unwrap()
                       .extract_integer_value(),
                   2);
    }

    #[test]
    fn binary_operator_node_visit_returns_error_when_subtraction_overflows() {
        let mut ast = Ast::new();
        let index_op = binop_node!(ast,
                                   int_node!(ast, -2),
                                   int_node!(ast, i64::MAX),
                                   OperatorType::Minus);
        let mut sym_tbl = SymbolTable::new();
        assert!(ast.get_node(index_op)
                    .visit(&ast, &mut sym_tbl)
                    .is_err());
    }

    #[test]
    fn binary_operator_node_visit_returns_product_of_integer_nodes_when_op_is_multiplication() {
        let mut ast = Ast::new();
        let index_op = binop_node!(ast,
                                   int_node!(ast, 4),
                                   int_node!(ast, 2),
                                   OperatorType::Times);
        let mut sym_tbl = SymbolTable::new();
        assert_eq!(ast.get_node(index_op)
                       .visit(&ast, &mut sym_tbl)
                       .unwrap()
                       .extract_integer_value(),
                   8);
    }

    #[test]
    fn binary_operator_node_visit_returns_real_product_if_at_least_one_operand_is_real() {
        let mut ast = Ast::new();
        let index_op = binop_node!(ast,
                                   real_node!(ast, 1.5),
                                   real_node!(ast, 2.5),
                                   OperatorType::Times);
        let mut sym_tbl = SymbolTable::new();
        assert_eq!(ast.get_node(index_op)
                       .visit(&ast, &mut sym_tbl)
                       .unwrap()
                       .extract_real_value(),
                   3.75);
    }

    #[test]
    fn binary_operator_node_visit_returns_error_when_multiplication_overflows() {
        let mut ast = Ast::new();
        let index_op = binop_node!(ast,
                                   int_node!(ast, 2),
                                   int_node!(ast, i64::MAX),
                                   OperatorType::Times);
        let mut sym_tbl = SymbolTable::new();
        assert!(ast.get_node(index_op)
                    .visit(&ast, &mut sym_tbl)
                    .is_err());
    }

    #[test]
    fn binary_operator_node_visit_returns_quotient_of_integer_nodes_when_op_is_int_division() {
        let mut ast = Ast::new();
        let index_op = binop_node!(ast,
                                   int_node!(ast, 5),
                                   int_node!(ast, 2),
                                   OperatorType::IntegerDivision);
        let mut sym_tbl = SymbolTable::new();
        assert_eq!(ast.get_node(index_op)
                       .visit(&ast, &mut sym_tbl)
                       .unwrap()
                       .extract_integer_value(),
                   2);
    }

    #[test]
    fn binary_operator_node_visit_returns_quotient_of_nodes_when_op_is_float_division() {
        let mut ast = Ast::new();
        let index_op = binop_node!(ast,
                                   real_node!(ast, 5.0),
                                   int_node!(ast, 2),
                                   OperatorType::FloatDivision);
        let mut sym_tbl = SymbolTable::new();
        assert_eq!(ast.get_node(index_op)
                       .visit(&ast, &mut sym_tbl)
                       .unwrap()
                       .extract_real_value(),
                   2.5);
    }

    #[test]
    fn binary_operator_node_visit_integer_div_gives_floored_quotient_if_one_operand_is_real() {
        let mut ast = Ast::new();
        let index_op = binop_node!(ast,
                                   int_node!(ast, 5),
                                   real_node!(ast, 2.0),
                                   OperatorType::IntegerDivision);
        let mut sym_tbl = SymbolTable::new();
        assert_eq!(ast.get_node(index_op)
                       .visit(&ast, &mut sym_tbl)
                       .unwrap()
                       .extract_real_value(),
                   2.0);
    }

    #[test]
    fn binary_operator_node_visit_returns_error_when_division_overflows() {
        let mut ast = Ast::new();
        let index_op = binop_node!(ast,
                                   int_node!(ast, i64::MIN),
                                   int_node!(ast, -1),
                                   OperatorType::IntegerDivision);
        let mut sym_tbl = SymbolTable::new();
        assert!(ast.get_node(index_op)
                    .visit(&ast, &mut sym_tbl)
                    .is_err());
    }

    #[test]
    fn binary_operator_node_visit_returns_error_when_op_is_division_and_rhs_is_zero() {
        let mut ast = Ast::new();
        let index_op = binop_node!(ast,
                                   int_node!(ast, 4),
                                   int_node!(ast, 0),
                                   OperatorType::IntegerDivision);
        let mut sym_tbl = SymbolTable::new();
        assert!(ast.get_node(index_op)
                    .visit(&ast, &mut sym_tbl)
                    .is_err());
    }
}
