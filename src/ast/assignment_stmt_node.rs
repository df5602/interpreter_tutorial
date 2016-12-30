use std::fmt;

use tokens::{Token, TokenValue};
use errors::SyntaxError;
use ast::{Ast, AstNode, AstIndex};
use interpreter::{NodeVisitor, ReturnValue};

/// Assignment statement. It consists of the following form:
/// VARIABLE := EXPRESSION
#[derive(Debug)]
pub struct AssignmentStmtNode {
    variable: AstIndex,
    expression: AstIndex,
    parent: Option<AstIndex>,
    position: (usize, usize),
    token: Token,
}

impl fmt::Display for AssignmentStmtNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.parent {
            Some(ref i) => {
                write!(f,
                       "AssignmentStatement(variable: {}, expression: {}, parent: {})",
                       self.variable,
                       self.expression,
                       i)
            }
            None => {
                write!(f,
                       "AssignmentStatement(variable: {}, expression: {}, parent: None)",
                       self.variable,
                       self.expression)
            }
        }
    }
}

impl AstNode for AssignmentStmtNode {
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
        vec![self.variable, self.expression]
    }

    fn get_value(&self) -> Option<TokenValue> {
        None
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
                format!("AssignmentStatement(variable: {}, expression: {}, parent: {})",
                        self.variable,
                        self.expression,
                        i)
            }
            None => {
                format!("AssignmentStatement(variable: {}, expression: {}, parent: None)",
                        self.variable,
                        self.expression)
            }
        }
    }
}

impl NodeVisitor for AssignmentStmtNode {
    fn visit(&self, ast: &Ast) -> Result<ReturnValue, SyntaxError> {
        unimplemented!();
        // let operand = ast.get_node(self.operand).visit(ast)?;

        // match self.operator {
        //     OperatorType::Plus => Ok(operand),
        //     OperatorType::Minus => Ok(-operand),
        //     _ => panic!("Internal error (Unsupported operator type for unary operator)"),
        // }
    }
}

impl AssignmentStmtNode {
    /// Constructs a new assignment statement node.
    pub fn new(variable: AstIndex, expression: AstIndex, token: Token) -> Self {
        AssignmentStmtNode {
            variable: variable,
            expression: expression,
            parent: None,
            position: (0, 0),
            token: token,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokens::{Token, TokenType};
    use ast::{AstNode, AstIndex};

    #[test]
    fn assignment_statement_node_get_parent_returns_none_when_node_has_no_parent() {
        let node = AssignmentStmtNode::new(AstIndex(0),
                                           AstIndex(1),
                                           Token::new(TokenType::Assign, None, (0, 2)));
        assert_eq!(node.get_parent(), None);
    }

    #[test]
    fn assignment_statement_node_set_parent_sets_parent_node() {
        let mut node = AssignmentStmtNode::new(AstIndex(0),
                                               AstIndex(1),
                                               Token::new(TokenType::Assign, None, (0, 2)));
        assert!(node.set_parent(AstIndex(2)));
        assert_eq!(node.get_parent(), Some(AstIndex(2)));
    }

    #[test]
    fn assignment_statement_node_set_parent_fails_when_node_already_has_parent() {
        let mut node = AssignmentStmtNode::new(AstIndex(0),
                                               AstIndex(1),
                                               Token::new(TokenType::Assign, None, (0, 2)));
        assert!(node.set_parent(AstIndex(2)));
        assert!(!node.set_parent(AstIndex(3)));
    }

    #[test]
    fn assignment_statement_node_get_children_returns_operand() {
        let node = AssignmentStmtNode::new(AstIndex(0),
                                           AstIndex(1),
                                           Token::new(TokenType::Assign, None, (0, 2)));
        let children = node.get_children();
        assert_eq!(children[0], AstIndex(0));
        assert_eq!(children[1], AstIndex(1));
        assert_eq!(children.len(), 2);
    }

    #[test]
    fn assignment_statement_node_get_value_returns_none() {
        let node = AssignmentStmtNode::new(AstIndex(0),
                                           AstIndex(1),
                                           Token::new(TokenType::Assign, None, (0, 2)));
        assert_eq!(node.get_value(), None);
    }

    #[test]
    fn assignment_statement_node_get_position_returns_position() {
        let mut node = AssignmentStmtNode::new(AstIndex(0),
                                               AstIndex(1),
                                               Token::new(TokenType::Assign, None, (0, 2)));
        node.set_position((4, 5));
        assert_eq!(node.get_position(), (4, 5));
    }
}
