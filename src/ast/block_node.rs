use std::fmt;
use std::collections::HashMap;

use tokens::{TokenValue, Span};
use errors::SyntaxError;
use ast::{Ast, AstNode, AstIndex};
use interpreter::{NodeVisitor, ReturnValue};

/// Block node. A block consists of a list of declarations followed
/// by a compound statement.
#[derive(Debug)]
pub struct BlockNode {
    declarations: Vec<AstIndex>,
    compound_statement: AstIndex,
    parent: Option<AstIndex>,
    span: Span,
}

impl fmt::Display for BlockNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.parent {
            Some(ref i) => {
                write!(f,
                       "Block(declarations: {:?}, compound statement: {}, parent: {})",
                       self.declarations,
                       self.compound_statement,
                       i)
            }
            None => {
                write!(f,
                       "Block(declarations: {:?}, compound statement: {}, parent: None)",
                       self.declarations,
                       self.compound_statement)
            }
        }
    }
}

impl AstNode for BlockNode {
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
        let mut children = self.declarations.clone();
        children.push(self.compound_statement);
        children
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

impl NodeVisitor for BlockNode {
    fn visit(&self,
             ast: &Ast,
             sym_tbl: &mut HashMap<String, i64>)
             -> Result<ReturnValue, SyntaxError> {
        if !self.declarations.is_empty() {
            unimplemented!();
        }
        ast.get_node(self.compound_statement).visit(ast, sym_tbl)
    }
}

impl BlockNode {
    /// Constructs a new block node.
    ///
    /// * `declarations`: a vector of indices into the AST representing all declarations,
    /// * `compound_statement`: the indice into the AST of the compound statement,
    pub fn new(declarations: Vec<AstIndex>, compound_statement: AstIndex) -> Self {
        BlockNode {
            declarations: declarations,
            compound_statement: compound_statement,
            parent: None,
            span: Span::new(0, 0),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokens::{Token, TokenType, OperatorType};
    use ast::{AstNode, AstIndex, CompoundStmtNode, BinaryOperatorNode, IntegerNode,
              AssignmentStmtNode, VariableNode};

    #[test]
    fn block_node_get_parent_returns_none_when_node_has_no_parent() {
        let node = BlockNode::new(vec![AstIndex(0), AstIndex(1)], AstIndex(2));
        assert_eq!(node.get_parent(), None);
    }

    #[test]
    fn block_node_set_parent_sets_parent_node() {
        let mut node = BlockNode::new(vec![AstIndex(0), AstIndex(1)], AstIndex(2));
        assert!(node.set_parent(AstIndex(3)));
        assert_eq!(node.get_parent(), Some(AstIndex(3)));
    }

    #[test]
    fn block_node_set_parent_fails_when_node_already_has_parent() {
        let mut node = BlockNode::new(vec![AstIndex(0), AstIndex(1)], AstIndex(2));
        assert!(node.set_parent(AstIndex(3)));
        assert!(!node.set_parent(AstIndex(4)));
    }

    #[test]
    fn block_node_get_children_returns_declarations_and_compound_statement() {
        let node = BlockNode::new(vec![AstIndex(0), AstIndex(1)], AstIndex(2));
        let children = node.get_children();
        assert_eq!(children[0], AstIndex(0));
        assert_eq!(children[1], AstIndex(1));
        assert_eq!(children[2], AstIndex(2));
        assert_eq!(children.len(), 3);
    }

    #[test]
    fn block_node_get_value_returns_none() {
        let node = BlockNode::new(vec![AstIndex(0), AstIndex(1)], AstIndex(2));
        assert_eq!(node.get_value(), None);
    }

    #[test]
    fn block_node_get_span_returns_span() {
        let mut node = BlockNode::new(vec![AstIndex(0), AstIndex(1)], AstIndex(2));
        node.set_span(Span::new(2, 3));
        assert_eq!(node.get_span(), Span::new(2, 3));
    }

    #[test]
    fn block_node_visit_returns_void() {
        let mut ast = Ast::new();

        let index = block_node!(ast,
                                vec![],
                                cmpd_stmt_node!(ast,
                                                vec![binop_node!(ast,
                                                                 int_node!(ast, 2),
                                                                 int_node!(ast, 4),
                                                                 OperatorType::Plus)]));

        let mut sym_tbl = HashMap::new();
        assert_eq!(ast.get_node(index).visit(&ast, &mut sym_tbl).unwrap(),
                   ReturnValue::Void);
    }

    #[test]
    fn block_node_visit_visits_compound_statement() {
        let mut ast = Ast::new();

        let index = block_node!(ast,
                                vec![],
                                cmpd_stmt_node!(ast,
                                                vec![assign_node!(ast,
                                                                  var_node!(ast, "a"),
                                                                  int_node!(ast, 2))]));

        let mut sym_tbl = HashMap::new();
        assert_eq!(sym_tbl.get(&"a".to_string()), None);
        assert!(ast.get_node(index).visit(&ast, &mut sym_tbl).is_ok());
        assert_eq!(sym_tbl.get(&"a".to_string()), Some(&2));
    }
}
