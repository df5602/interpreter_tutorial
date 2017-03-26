use std::fmt;
use std::collections::HashMap;

use tokens::{TokenValue, Span};
use errors::SyntaxError;
use ast::{Ast, AstNode, AstIndex};
use interpreter::{NodeVisitor, ReturnValue};

/// Variable declaration. It consists of the following form:
/// a : INTEGER;
#[derive(Debug)]
pub struct VariableDeclNode {
    variable: AstIndex,
    type_spec: AstIndex,
    parent: Option<AstIndex>,
    span: Span,
}

impl fmt::Display for VariableDeclNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.parent {
            Some(ref i) => {
                write!(f,
                       "Variable declaration(variable: {}, type: {}, parent: {})",
                       self.variable,
                       self.type_spec,
                       i)
            }
            None => {
                write!(f,
                       "Variable declaration(variable: {}, type: {}, parent: None)",
                       self.variable,
                       self.type_spec)
            }
        }
    }
}

impl AstNode for VariableDeclNode {
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
        vec![self.variable, self.type_spec]
    }

    fn get_value(&self) -> Option<TokenValue> {
        None
    }

    fn get_span(&self) -> Span {
        self.span.clone()
    }

    fn set_span(&mut self, span: Span) {
        self.span = span;
    }
}

impl NodeVisitor for VariableDeclNode {
    fn visit(&self,
             _ast: &Ast,
             _sym_tbl: &mut HashMap<String, i64>)
             -> Result<ReturnValue, SyntaxError> {
        unimplemented!();
    }
}

impl VariableDeclNode {
    /// Constructs a new variable declaration node.
    pub fn new(variable: AstIndex, type_spec: AstIndex) -> Self {
        Self {
            variable: variable,
            type_spec: type_spec,
            parent: None,
            span: Span::new(0, 0),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokens::Span;
    use ast::{AstNode, AstIndex};

    #[test]
    fn variable_decl_node_get_parent_returns_none_when_node_has_no_parent() {
        let node = VariableDeclNode::new(AstIndex(0), AstIndex(1));
        assert_eq!(node.get_parent(), None);
    }

    #[test]
    fn variable_decl_node_set_parent_sets_parent_node() {
        let mut node = VariableDeclNode::new(AstIndex(0), AstIndex(1));
        assert!(node.set_parent(AstIndex(2)));
        assert_eq!(node.get_parent(), Some(AstIndex(2)));
    }

    #[test]
    fn variable_decl_node_set_parent_fails_when_node_already_has_parent() {
        let mut node = VariableDeclNode::new(AstIndex(0), AstIndex(1));
        assert!(node.set_parent(AstIndex(2)));
        assert!(!node.set_parent(AstIndex(3)));
    }

    #[test]
    fn variable_decl_node_get_children_returns_variable_and_type() {
        let node = VariableDeclNode::new(AstIndex(0), AstIndex(1));
        let children = node.get_children();
        assert_eq!(children[0], AstIndex(0));
        assert_eq!(children[1], AstIndex(1));
        assert_eq!(children.len(), 2);
    }

    #[test]
    fn variable_decl_node_get_value_returns_none() {
        let node = VariableDeclNode::new(AstIndex(0), AstIndex(1));
        assert_eq!(node.get_value(), None);
    }

    #[test]
    fn variable_decl_node_get_span_returns_span() {
        let mut node = VariableDeclNode::new(AstIndex(0), AstIndex(1));
        node.set_span(Span::new(4, 5));
        assert_eq!(node.get_span(), Span::new(4, 5));
    }
}
