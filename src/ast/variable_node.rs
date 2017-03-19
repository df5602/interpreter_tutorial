use std::fmt;
use std::collections::HashMap;

use tokens::{Token, TokenValue, Span};
use errors::SyntaxError;
use ast::{Ast, AstNode, AstIndex};
use interpreter::{NodeVisitor, ReturnValue};

/// Represents an identifier.
#[derive(Debug)]
pub struct VariableNode {
    name: String,
    parent: Option<AstIndex>,
    span: Span,
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

    fn get_span(&self) -> Span {
        self.span.clone()
    }

    fn set_span(&mut self, span: Span) {
        self.span = span;
    }
}

impl NodeVisitor for VariableNode {
    fn visit(&self,
             _ast: &Ast,
             sym_tbl: &mut HashMap<String, i64>)
             -> Result<ReturnValue, SyntaxError> {
        match sym_tbl.get(&self.name) {
            Some(value) => Ok(ReturnValue::Integer(*value)),
            None => {
                Err(SyntaxError {
                        msg: format!("No variable named `{}` in scope.", self.name),
                        span: self.token.span.clone(),
                    })
            }
        }
    }
}

impl VariableNode {
    /// Constructs a new variable node.
    pub fn new(name: String, token: Token) -> Self {
        VariableNode {
            name: name,
            parent: None,
            span: token.span.clone(),
            token: token,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;
    use tokens::{Token, TokenType, TokenValue, Span};
    use ast::{Ast, AstNode, AstIndex, IntegerNode, AssignmentStmtNode};
    use interpreter::ReturnValue;

    #[test]
    fn variable_node_get_parent_returns_none_when_node_has_no_parent() {
        let var_node =
            VariableNode::new("foo".to_string(),
                              Token::new(TokenType::Identifier,
                                         Some(TokenValue::Identifier("foo".to_string())),
                                         Span::new(0, 4)));
        assert_eq!(var_node.get_parent(), None);
    }

    #[test]
    fn variable_node_set_parent_sets_parent_node() {
        let mut var_node =
            VariableNode::new("foo".to_string(),
                              Token::new(TokenType::Identifier,
                                         Some(TokenValue::Identifier("foo".to_string())),
                                         Span::new(0, 4)));
        assert!(var_node.set_parent(AstIndex(2)));
        assert_eq!(var_node.get_parent(), Some(AstIndex(2)));
    }

    #[test]
    fn variable_node_set_parent_fails_when_node_already_has_parent() {
        let mut var_node =
            VariableNode::new("foo".to_string(),
                              Token::new(TokenType::Identifier,
                                         Some(TokenValue::Identifier("foo".to_string())),
                                         Span::new(0, 4)));
        assert!(var_node.set_parent(AstIndex(2)));
        assert!(!var_node.set_parent(AstIndex(3)));
    }

    #[test]
    fn variable_node_get_children_returns_no_children() {
        let var_node =
            VariableNode::new("foo".to_string(),
                              Token::new(TokenType::Identifier,
                                         Some(TokenValue::Identifier("foo".to_string())),
                                         Span::new(0, 4)));
        let children = var_node.get_children();
        assert!(children.is_empty());
    }

    #[test]
    fn variable_node_get_value_returns_variable_name() {
        let var_node =
            VariableNode::new("foo".to_string(),
                              Token::new(TokenType::Identifier,
                                         Some(TokenValue::Identifier("foo".to_string())),
                                         Span::new(0, 4)));
        assert_eq!(var_node.get_value().unwrap(),
                   TokenValue::Identifier("foo".to_string()));
    }

    #[test]
    fn variable_node_get_span_returns_span() {
        let mut var_node =
            VariableNode::new("foo".to_string(),
                              Token::new(TokenType::Identifier,
                                         Some(TokenValue::Identifier("foo".to_string())),
                                         Span::new(0, 4)));
        var_node.set_span(Span::new(4, 5));
        assert_eq!(var_node.get_span(), Span::new(4, 5));
    }

    #[test]
    fn variable_node_visit_returns_value_if_variable_exists() {
        let mut ast = Ast::new();
        let mut sym_tbl = HashMap::new();

        let index_var_a = var_node!(ast, "a");
        let index_ass_1 = assign_node!(ast, index_var_a, int_node!(ast, 42));

        assert!(ast.get_node(index_ass_1).visit(&ast, &mut sym_tbl).is_ok());
        assert_eq!(sym_tbl.get(&"a".to_string()), Some(&42));
        assert_eq!(ast.get_node(index_var_a).visit(&ast, &mut sym_tbl).unwrap(),
                   ReturnValue::Integer(42));
    }

    #[test]
    fn variable_node_visit_returns_error_if_variable_doesnt_exist() {
        let mut ast = Ast::new();
        let mut sym_tbl = HashMap::new();

        let index_var_a = var_node!(ast, "a");

        assert_eq!(sym_tbl.get(&"a".to_string()), None);
        assert!(ast.get_node(index_var_a).visit(&ast, &mut sym_tbl).is_err());
    }
}
