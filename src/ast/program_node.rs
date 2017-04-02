use std::fmt;

use tokens::{TokenValue, Span};
use symbol_table::SymbolTable;
use errors::SyntaxError;
use ast::{Ast, AstNode, AstIndex};
use interpreter::{NodeVisitor, Value};

/// Program node. A program declaration consists of a program name and a block:
/// program : PROGRAM variable SEMICOLON block DOT
#[derive(Debug)]
pub struct ProgramNode {
    name: String,
    variable: AstIndex,
    block: AstIndex,
    parent: Option<AstIndex>,
    span: Span,
}

impl fmt::Display for ProgramNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.parent {
            Some(ref i) => {
                write!(f,
                       "Program(name: {}, variable: {}, block: {}, parent: {})",
                       self.name,
                       self.variable,
                       self.block,
                       i)
            }
            None => {
                write!(f,
                       "Program(name: {}, variable: {}, block: {}, parent: None)",
                       self.name,
                       self.variable,
                       self.block)
            }
        }
    }
}

impl AstNode for ProgramNode {
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
        vec![self.variable, self.block]
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

impl NodeVisitor for ProgramNode {
    fn visit(&self, ast: &Ast, sym_tbl: &mut SymbolTable) -> Result<Value, SyntaxError> {
        ast.get_node(self.block).visit(ast, sym_tbl)
    }
}

impl ProgramNode {
    /// Constructs a new program node.
    ///
    /// * `name`: the name of the program,
    /// * `variable`: the indice into the AST of the variable,
    /// * `block`: the indice into the AST of the block,
    pub fn new(name: String, variable: AstIndex, block: AstIndex) -> Self {
        Self {
            name: name,
            variable: variable,
            block: block,
            parent: None,
            span: Span::new(0, 0),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokens::{Token, TokenType, OperatorType, Type};
    use ast::{AstNode, AstIndex, VariableNode, BlockNode, CompoundStmtNode, BinaryOperatorNode,
              IntegerNode, AssignmentStmtNode, VariableDeclNode, TypeNode};

    #[test]
    fn program_node_get_parent_returns_none_when_node_has_no_parent() {
        let node = ProgramNode::new("Test".to_string(), AstIndex(0), AstIndex(1));
        assert_eq!(node.get_parent(), None);
    }

    #[test]
    fn program_node_set_parent_sets_parent_node() {
        let mut node = ProgramNode::new("Test".to_string(), AstIndex(0), AstIndex(1));
        assert!(node.set_parent(AstIndex(2)));
        assert_eq!(node.get_parent(), Some(AstIndex(2)));
    }

    #[test]
    fn program_node_set_parent_fails_when_node_already_has_parent() {
        let mut node = ProgramNode::new("Test".to_string(), AstIndex(0), AstIndex(1));
        assert!(node.set_parent(AstIndex(2)));
        assert!(!node.set_parent(AstIndex(3)));
    }

    #[test]
    fn program_node_get_children_returns_variable_and_block_nodes() {
        let node = ProgramNode::new("Test".to_string(), AstIndex(0), AstIndex(1));
        let children = node.get_children();
        assert_eq!(children[0], AstIndex(0));
        assert_eq!(children[1], AstIndex(1));
        assert_eq!(children.len(), 2);
    }

    #[test]
    fn program_node_get_value_returns_name() {
        let node = ProgramNode::new("Test".to_string(), AstIndex(0), AstIndex(1));
        assert_eq!(node.get_value().unwrap(),
                   TokenValue::Identifier("Test".to_string()));
    }

    #[test]
    fn program_node_get_span_returns_span() {
        let mut node = ProgramNode::new("Test".to_string(), AstIndex(0), AstIndex(1));
        node.set_span(Span::new(2, 3));
        assert_eq!(node.get_span(), Span::new(2, 3));
    }

    #[test]
    fn program_node_visit_returns_void() {
        let mut ast = Ast::new();

        let index = program_node!(ast,
                                  "Test",
                                  var_node!(ast, "Test"),
                                  block_node!(ast,
                                              vec![],
                                              cmpd_stmt_node!(ast,
                                                              vec![binop_node!(ast,
                                                                 int_node!(ast, 2),
                                                                 int_node!(ast, 4),
                                                                 OperatorType::Plus)])));

        let mut sym_tbl = SymbolTable::new();
        assert_eq!(ast.get_node(index).visit(&ast, &mut sym_tbl).unwrap(),
                   Value::Void);
    }

    #[test]
    fn program_node_visit_visits_block() {
        let mut ast = Ast::new();

        let index =
            program_node!(ast,
                          "Test",
                          var_node!(ast, "Test"),
                          block_node!(ast,
                                      vec![var_decl_node!(ast,
                                                          var_node!(ast, "a"),
                                                          type_node!(ast, Type::Integer))],
                                      cmpd_stmt_node!(ast,
                                                      vec![assign_node!(ast,
                                                                        var_node!(ast, "a"),
                                                                        int_node!(ast, 2))])));

        let mut sym_tbl = SymbolTable::new();
        assert_eq!(sym_tbl.value(&"a".to_string()), None);
        assert!(ast.get_node(index).visit(&ast, &mut sym_tbl).is_ok());
        assert_eq!(sym_tbl.value(&"a".to_string()), Some(Value::Integer(2)));
    }
}