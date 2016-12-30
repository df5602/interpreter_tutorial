use std::fmt;

use tokens::{Token, TokenValue};
use errors::SyntaxError;
use ast::{Ast, AstNode, AstIndex};
use interpreter::{NodeVisitor, ReturnValue};

/// Represents an identifier.
#[derive(Debug)]
pub struct VariableNode {
    name: String,
    parent: Option<AstIndex>,
    position: (usize, usize),
    token: Token,
}

impl fmt::Display for VariableNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.parent {
            Some(ref i) => write!(f, "Variable(name: {}, parent: {})", self.name, i),
            None => write!(f, "Variable(name: {}, parent: None)", self.name),
        }
    }
}

impl AstNode for VariableNode {
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
        Some(TokenValue::Identifier(self.name.clone()))
    }

    fn get_position(&self) -> (usize, usize) {
        self.position
    }

    fn set_position(&mut self, position: (usize, usize)) {
        self.position = position;
    }

    fn print(&self) -> String {
        match self.parent {
            Some(ref i) => format!("Variable(name: {}, parent: {})", self.name, i),
            None => format!("Variable(name: {}, parent: None)", self.name),
        }
    }
}

impl NodeVisitor for VariableNode {
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

impl VariableNode {
    /// Constructs a new variable node.
    pub fn new(name: String, token: Token) -> Self {
        VariableNode {
            name: name,
            parent: None,
            position: (0, 0),
            token: token,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use tokens::{Token, TokenType, TokenValue};
    use ast::{AstNode, AstIndex};

    #[test]
    fn variable_node_get_parent_returns_none_when_node_has_no_parent() {
        let var_node = VariableNode::new("foo".to_string(),
                                         Token::new(TokenType::Identifier,
                                                    Some(TokenValue::Identifier("foo"
                                                        .to_string())),
                                                    (0, 4)));
        assert_eq!(var_node.get_parent(), None);
    }

    #[test]
    fn variable_node_set_parent_sets_parent_node() {
        let mut var_node = VariableNode::new("foo".to_string(),
                                             Token::new(TokenType::Identifier,
                                                        Some(TokenValue::Identifier("foo"
                                                            .to_string())),
                                                        (0, 4)));
        assert!(var_node.set_parent(AstIndex(2)));
        assert_eq!(var_node.get_parent(), Some(AstIndex(2)));
    }

    #[test]
    fn variable_node_set_parent_fails_when_node_already_has_parent() {
        let mut var_node = VariableNode::new("foo".to_string(),
                                             Token::new(TokenType::Identifier,
                                                        Some(TokenValue::Identifier("foo"
                                                            .to_string())),
                                                        (0, 4)));
        assert!(var_node.set_parent(AstIndex(2)));
        assert!(!var_node.set_parent(AstIndex(3)));
    }

    #[test]
    fn variable_node_get_children_returns_no_children() {
        let var_node = VariableNode::new("foo".to_string(),
                                         Token::new(TokenType::Identifier,
                                                    Some(TokenValue::Identifier("foo"
                                                        .to_string())),
                                                    (0, 4)));
        let children = var_node.get_children();
        assert!(children.is_empty());
    }

    #[test]
    fn variable_node_get_value_returns_variable_name() {
        let var_node = VariableNode::new("foo".to_string(),
                                         Token::new(TokenType::Identifier,
                                                    Some(TokenValue::Identifier("foo"
                                                        .to_string())),
                                                    (0, 4)));
        assert_eq!(var_node.get_value().unwrap(),
                   TokenValue::Identifier("foo".to_string()));
    }

    #[test]
    fn variable_node_get_position_returns_position() {
        let mut var_node = VariableNode::new("foo".to_string(),
                                             Token::new(TokenType::Identifier,
                                                        Some(TokenValue::Identifier("foo"
                                                            .to_string())),
                                                        (0, 4)));
        var_node.set_position((4, 5));
        assert_eq!(var_node.get_position(), (4, 5));
    }
}
