use std::fmt;

use tokens::{Token, TokenValue, Span};
use symbol_table::SymbolTable;
use errors::SyntaxError;
use ast::{Ast, AstNode, AstIndex};
use interpreter::{NodeVisitor, Value};

/// Assignment statement. It consists of the following form:
/// VARIABLE := EXPRESSION
#[derive(Debug)]
pub struct AssignmentStmtNode {
    variable: AstIndex,
    expression: AstIndex,
    parent: Option<AstIndex>,
    span: Span,
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

    fn get_span(&self) -> Span {
        self.span.clone()
    }

    fn set_span(&mut self, span: Span) {
        self.span = span;
    }
}

impl NodeVisitor for AssignmentStmtNode {
    fn visit(&self, ast: &Ast, sym_tbl: &mut SymbolTable) -> Result<Value, SyntaxError> {
        let name = ast.get_node(self.variable)
            .get_value()
            .unwrap()
            .extract_identifier_value();
        let expression = ast.get_node(self.expression).visit(ast, sym_tbl)?;

        // Try to update value in symbol table, return error, if no entry exists
        match sym_tbl.update(name, expression) {
            Ok(_) => Ok(Value::Void),
            Err(msg) => {
                Err(SyntaxError {
                        msg: msg,
                        span: self.span.clone(),
                    })
            }
        }
    }
}

impl AssignmentStmtNode {
    /// Constructs a new assignment statement node.
    pub fn new(variable: AstIndex, expression: AstIndex, token: Token) -> Self {
        AssignmentStmtNode {
            variable: variable,
            expression: expression,
            parent: None,
            span: Span::new(0, 0),
            token: token,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokens::{Token, TokenType, TokenValue, Span, Type};
    use ast::{Ast, AstNode, AstIndex, VariableNode, NumberNode, CompoundStmtNode};
    use interpreter::Value;

    #[test]
    fn assignment_statement_node_get_parent_returns_none_when_node_has_no_parent() {
        let node = AssignmentStmtNode::new(AstIndex(0),
                                           AstIndex(1),
                                           Token::new(TokenType::Assign, None, Span::new(0, 2)));
        assert_eq!(node.get_parent(), None);
    }

    #[test]
    fn assignment_statement_node_set_parent_sets_parent_node() {
        let mut node =
            AssignmentStmtNode::new(AstIndex(0),
                                    AstIndex(1),
                                    Token::new(TokenType::Assign, None, Span::new(0, 2)));
        assert!(node.set_parent(AstIndex(2)));
        assert_eq!(node.get_parent(), Some(AstIndex(2)));
    }

    #[test]
    fn assignment_statement_node_set_parent_fails_when_node_already_has_parent() {
        let mut node =
            AssignmentStmtNode::new(AstIndex(0),
                                    AstIndex(1),
                                    Token::new(TokenType::Assign, None, Span::new(0, 2)));
        assert!(node.set_parent(AstIndex(2)));
        assert!(!node.set_parent(AstIndex(3)));
    }

    #[test]
    fn assignment_statement_node_get_children_returns_variable_and_expression() {
        let node = AssignmentStmtNode::new(AstIndex(0),
                                           AstIndex(1),
                                           Token::new(TokenType::Assign, None, Span::new(0, 2)));
        let children = node.get_children();
        assert_eq!(children[0], AstIndex(0));
        assert_eq!(children[1], AstIndex(1));
        assert_eq!(children.len(), 2);
    }

    #[test]
    fn assignment_statement_node_get_value_returns_none() {
        let node = AssignmentStmtNode::new(AstIndex(0),
                                           AstIndex(1),
                                           Token::new(TokenType::Assign, None, Span::new(0, 2)));
        assert_eq!(node.get_value(), None);
    }

    #[test]
    fn assignment_statement_node_get_span_returns_span() {
        let mut node =
            AssignmentStmtNode::new(AstIndex(0),
                                    AstIndex(1),
                                    Token::new(TokenType::Assign, None, Span::new(0, 2)));
        node.set_span(Span::new(4, 5));
        assert_eq!(node.get_span(), Span::new(4, 5));
    }

    #[test]
    fn assignment_statement_node_visit_updates_entry_in_symbol_table_1() {
        let mut ast = Ast::new();
        let mut sym_tbl = SymbolTable::new();
        assert!(sym_tbl.insert("a".to_string(), Type::Integer).is_ok());

        let index = assign_node!(ast, var_node!(ast, "a"), int_node!(ast, 42));

        assert_eq!(sym_tbl.value(&"a".to_string()), Some(Value::NotInitialized));
        assert_eq!(ast.get_node(index).visit(&ast, &mut sym_tbl).unwrap(),
                   Value::Void);
        assert_eq!(sym_tbl.value(&"a".to_string()), Some(Value::Integer(42)));
    }

    #[test]
    fn assignment_statement_node_visit_updates_entry_in_symbol_table_2() {
        let mut ast = Ast::new();
        let mut sym_tbl = SymbolTable::new();
        assert!(sym_tbl.insert("a".to_string(), Type::Integer).is_ok());

        let index_stmt =
            cmpd_stmt_node!(ast,
                            vec![assign_node!(ast, var_node!(ast, "a"), int_node!(ast, 42)),
                                 assign_node!(ast, var_node!(ast, "a"), int_node!(ast, 24))]);

        assert_eq!(sym_tbl.value(&"a".to_string()), Some(Value::NotInitialized));

        assert!(ast.get_node(index_stmt)
                    .visit(&ast, &mut sym_tbl)
                    .is_ok());

        assert_eq!(sym_tbl.value(&"a".to_string()), Some(Value::Integer(24)));
    }
}