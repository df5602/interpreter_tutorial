use std::fmt;

use tokens::{Token, OperatorType, TokenValue, Span};
use symbol_table::SymbolTable;
use ast::{Ast, AstNode, AstIndex};
use errors::SyntaxError;
use interpreter::{NodeVisitor, Value};

/// Unary operator node.
/// Unary operators are '+' and '-' in front of expressions.
#[derive(Debug)]
pub struct UnaryOperatorNode {
    operand: AstIndex,
    operator: OperatorType,
    parent: Option<AstIndex>,
    span: Span,
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

    fn get_span(&self) -> Span {
        self.span.clone()
    }

    fn set_span(&mut self, span: Span) {
        self.span = span;
    }
}

impl NodeVisitor for UnaryOperatorNode {
    fn visit(&self, ast: &Ast, sym_tbl: &mut SymbolTable) -> Result<Value, SyntaxError> {
        let operand = ast.get_node(self.operand)
            .visit(ast, sym_tbl)?
            .extract_integer_value();

        match self.operator {
            OperatorType::Plus => Ok(Value::Integer(operand)),
            OperatorType::Minus => {
                match operand.checked_neg() {
                    Some(value) => Ok(Value::Integer(value)),
                    None => {
                        let rhs = match ast.get_node(self.operand).get_value() {
                            Some(value) => {
                                match value {
                                    TokenValue::Identifier(name) => format!("`{}`", name),
                                    _ => "operand".to_string(),
                                }
                            }
                            None => "operand".to_string(),
                        };

                        Err(SyntaxError {
                                msg: format!("Integer overflow [{}: {}]", rhs, operand),
                                span: self.span.clone(),
                            })
                    }
                }
            }
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
            span: token.span.clone(),
            token: token,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::i64;

    use super::*;
    use tokens::{Token, TokenType, OperatorType, TokenValue, Span};
    use ast::{Ast, AstNode, AstIndex, IntegerNode};

    #[test]
    fn unary_operator_node_get_parent_returns_none_when_node_has_no_parent() {
        let op_node =
            UnaryOperatorNode::new(AstIndex(0),
                                   OperatorType::Minus,
                                   Token::new(TokenType::Operator,
                                              Some(TokenValue::Operator(OperatorType::Minus)),
                                              Span::default()));
        assert_eq!(op_node.get_parent(), None);
    }

    #[test]
    fn unary_operator_node_set_parent_sets_parent_node() {
        let mut op_node =
            UnaryOperatorNode::new(AstIndex(0),
                                   OperatorType::Minus,
                                   Token::new(TokenType::Operator,
                                              Some(TokenValue::Operator(OperatorType::Minus)),
                                              Span::default()));
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
                                              Span::default()));
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
                                              Span::default()));
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
                                              Span::default()));
        assert_eq!(op_node.get_value().unwrap(),
                   TokenValue::Operator(OperatorType::Minus));
    }

    #[test]
    fn unary_operator_node_get_span_returns_span() {
        let mut op_node =
            UnaryOperatorNode::new(AstIndex(0),
                                   OperatorType::Minus,
                                   Token::new(TokenType::Operator,
                                              Some(TokenValue::Operator(OperatorType::Minus)),
                                              Span::new(3, 5)));
        op_node.set_span(Span::new(4, 5));
        assert_eq!(op_node.get_span(), Span::new(4, 5));
    }

    #[test]
    fn unary_operator_node_visit_returns_operand_when_op_is_addition() {
        let mut ast = Ast::new();
        let index_op = unop_node!(ast, int_node!(ast, 2), OperatorType::Plus);
        let mut sym_tbl = SymbolTable::new();
        assert_eq!(ast.get_node(index_op)
                       .visit(&ast, &mut sym_tbl)
                       .unwrap()
                       .extract_integer_value(),
                   2);
    }

    #[test]
    fn unary_operator_node_visit_returns_negative_operand_when_op_is_subtraction() {
        let mut ast = Ast::new();
        let index_op = unop_node!(ast, int_node!(ast, 4), OperatorType::Minus);
        let mut sym_tbl = SymbolTable::new();
        assert_eq!(ast.get_node(index_op)
                       .visit(&ast, &mut sym_tbl)
                       .unwrap()
                       .extract_integer_value(),
                   -4);
    }

    #[test]
    fn unary_operator_node_visit_returns_error_when_subtraction_overflows() {
        let mut ast = Ast::new();
        let index_op = unop_node!(ast, int_node!(ast, i64::MIN), OperatorType::Minus);
        let mut sym_tbl = SymbolTable::new();
        assert!(ast.get_node(index_op)
                    .visit(&ast, &mut sym_tbl)
                    .is_err());
    }
}
