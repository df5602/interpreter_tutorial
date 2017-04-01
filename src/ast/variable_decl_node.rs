use std::fmt;

use tokens::{TokenValue, Span};
use symbol_table::SymbolTable;
use errors::SyntaxError;
use ast::{Ast, AstNode, AstIndex};
use interpreter::{NodeVisitor, Value};

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
    fn visit(&self, ast: &Ast, sym_tbl: &mut SymbolTable) -> Result<Value, SyntaxError> {
        // Retrieve variable name from variable node
        let variable_node = ast.get_node(self.variable);
        let name = variable_node
            .get_value()
            .unwrap()
            .extract_identifier_value();

        let type_node = ast.get_node(self.type_spec);
        let type_spec = type_node.get_value().unwrap().extract_type_specifier();

        // Only add variable to symbol table, if it doesn't exist yet.
        match sym_tbl.insert(name, type_spec) {
            Ok(_) => Ok(Value::Void),
            Err(msg) => {
                Err(SyntaxError {
                        msg: msg,
                        span: variable_node.get_span(),
                    })
            }
        }
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
    use tokens::{Token, TokenType, Span, Type};
    use ast::{AstNode, AstIndex, VariableNode, TypeNode};

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

    #[test]
    fn variable_decl_node_visit_adds_entry_to_symbol_table() {
        let mut ast = Ast::new();
        let mut sym_tbl = SymbolTable::new();

        let index = var_decl_node!(ast, var_node!(ast, "a"), type_node!(ast, Type::Integer));

        assert_eq!(sym_tbl.value(&"a".to_string()), None);
        assert_eq!(ast.get_node(index).visit(&ast, &mut sym_tbl).unwrap(),
                   Value::Void);
        assert_eq!(sym_tbl.value(&"a".to_string()), Some(Value::NotInitialized));
    }

    #[test]
    fn variable_decl_node_visit_returns_error_if_entry_already_exists() {
        let mut ast = Ast::new();
        let mut sym_tbl = SymbolTable::new();

        let decl = var_decl_node!(ast, var_node!(ast, "a"), type_node!(ast, Type::Integer));

        assert_eq!(sym_tbl.value(&"a".to_string()), None);
        assert_eq!(ast.get_node(decl).visit(&ast, &mut sym_tbl).unwrap(),
                   Value::Void);
        assert_eq!(sym_tbl.value(&"a".to_string()), Some(Value::NotInitialized));

        assert!(ast.get_node(decl).visit(&ast, &mut sym_tbl).is_err());
    }

    #[test]
    fn variable_decl_node_visit_added_entry_has_correct_type() {
        let mut ast = Ast::new();
        let mut sym_tbl = SymbolTable::new();

        let decl = var_decl_node!(ast, var_node!(ast, "a"), type_node!(ast, Type::Real));

        assert_eq!(sym_tbl.value(&"a".to_string()), None);
        assert_eq!(ast.get_node(decl).visit(&ast, &mut sym_tbl).unwrap(),
                   Value::Void);
        assert_eq!(sym_tbl.symbol_type(&"a".to_string()), Some(Type::Real));
    }
}