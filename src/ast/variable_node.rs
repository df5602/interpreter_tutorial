use std::fmt;

use tokens::{Token, TokenValue, Span};
use symbol_table::SymbolTable;
use errors::SyntaxError;
use ast::{Ast, AstNode, AstIndex};
use interpreter::{NodeVisitor, Value};

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
    fn visit(&self, _ast: &Ast, sym_tbl: &mut SymbolTable) -> Result<Value, SyntaxError> {
        match sym_tbl.value(&self.name) {
            Some(value) => {
                match value {
                    Value::NotInitialized => {
                        Err(SyntaxError {
                                msg: format!("Use of uninitialized variable `{}`.", self.name),
                                span: self.token.span.clone(),
                            })
                    }
                    value => Ok(value),
                }
            }
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
    use super::*;
    use tokens::{Token, TokenType, TokenValue, Span, Type};
    use ast::{Ast, AstNode, AstIndex, NumberNode, AssignmentStmtNode};
    use interpreter::Value;

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
        let mut sym_tbl = SymbolTable::new();
        assert!(sym_tbl.insert("a".to_string(), Type::Integer).is_ok());

        let index_var_a = var_node!(ast, "a");
        let index_ass_1 = assign_node!(ast, index_var_a, int_node!(ast, 42));

        assert!(ast.get_node(index_ass_1)
                    .visit(&ast, &mut sym_tbl)
                    .is_ok());
        assert_eq!(sym_tbl.value(&"a".to_string()), Some(Value::Integer(42)));
        assert_eq!(ast.get_node(index_var_a)
                       .visit(&ast, &mut sym_tbl)
                       .unwrap(),
                   Value::Integer(42));
    }

    #[test]
    fn variable_node_visit_returns_error_if_variable_doesnt_exist() {
        let mut ast = Ast::new();
        let mut sym_tbl = SymbolTable::new();

        let index_var_a = var_node!(ast, "a");

        assert_eq!(sym_tbl.value(&"a".to_string()), None);
        assert!(ast.get_node(index_var_a)
                    .visit(&ast, &mut sym_tbl)
                    .is_err());
    }

    #[test]
    fn variable_node_visit_returns_error_if_variable_is_uninitialized() {
        let mut ast = Ast::new();
        let mut sym_tbl = SymbolTable::new();
        assert!(sym_tbl.insert("a".to_string(), Type::Integer).is_ok());

        let index_var_a = var_node!(ast, "a");

        assert!(ast.get_node(index_var_a)
                    .visit(&ast, &mut sym_tbl)
                    .is_err());
    }
}