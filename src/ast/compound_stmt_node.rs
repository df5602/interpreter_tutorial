use std::fmt;

use tokens::{Token, TokenValue, Span};
use symbol_table::SymbolTable;
use errors::SyntaxError;
use ast::{Ast, AstNode, AstIndex};
use interpreter::{NodeVisitor, Value};

/// Compound statement node. A compound statement consists of
/// a 'BEGIN' keyword, followed by a list of statements and the
/// 'END' keyword.
#[derive(Debug)]
pub struct CompoundStmtNode {
    statement_list: Vec<AstIndex>,
    parent: Option<AstIndex>,
    span: Span,
    token_begin: Token,
    token_end: Token,
}

impl fmt::Display for CompoundStmtNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.parent {
            Some(ref i) => {
                write!(f,
                       "CompoundStatement(statements: {:?}, parent: {})",
                       self.statement_list,
                       i)
            }
            None => {
                write!(f,
                       "CompoundStatement(statements: {:?}, parent: None)",
                       self.statement_list)
            }
        }
    }
}

impl AstNode for CompoundStmtNode {
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
        self.statement_list.clone()
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

impl NodeVisitor for CompoundStmtNode {
    fn visit(&self, ast: &Ast, sym_tbl: &mut SymbolTable) -> Result<Value, SyntaxError> {
        for statement in &self.statement_list {
            ast.get_node(*statement).visit(ast, sym_tbl)?;
        }
        Ok(Value::Void)
    }
}

impl CompoundStmtNode {
    /// Constructs a new compound statement node.
    ///
    /// * `statements`: a vector of indices into the AST representing all statements,
    /// * `token_begin`: the 'BEGIN' token,
    /// * `token_end`: the 'END' token
    pub fn new(statements: Vec<AstIndex>, token_begin: Token, token_end: Token) -> Self {
        CompoundStmtNode {
            statement_list: statements,
            parent: None,
            span: Span::new(0, 0),
            token_begin: token_begin,
            token_end: token_end,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ast::{Ast, AstNode, AstIndex, IntegerNode, BinaryOperatorNode};
    use tokens::{Token, TokenType, TokenValue, OperatorType, Span};
    use interpreter::Value;

    #[test]
    fn compound_statement_node_get_parent_returns_none_when_node_has_no_parent() {
        let node = CompoundStmtNode::new(vec![AstIndex(0), AstIndex(1)],
                                         Token::new(TokenType::Begin, None, Span::new(0, 1)),
                                         Token::new(TokenType::End, None, Span::new(3, 4)));
        assert_eq!(node.get_parent(), None);
    }

    #[test]
    fn compound_statement_node_set_parent_sets_parent_node() {
        let mut node = CompoundStmtNode::new(vec![AstIndex(0), AstIndex(1)],
                                             Token::new(TokenType::Begin, None, Span::new(0, 1)),
                                             Token::new(TokenType::End, None, Span::new(3, 4)));
        assert!(node.set_parent(AstIndex(2)));
        assert_eq!(node.get_parent(), Some(AstIndex(2)));
    }

    #[test]
    fn compound_statement_node_set_parent_fails_when_node_already_has_parent() {
        let mut node = CompoundStmtNode::new(vec![AstIndex(0), AstIndex(1)],
                                             Token::new(TokenType::Begin, None, Span::new(0, 1)),
                                             Token::new(TokenType::End, None, Span::new(3, 4)));
        assert!(node.set_parent(AstIndex(2)));
        assert!(!node.set_parent(AstIndex(3)));
    }

    #[test]
    fn compound_statement_node_get_children_returns_statements() {
        let node = CompoundStmtNode::new(vec![AstIndex(0), AstIndex(1)],
                                         Token::new(TokenType::Begin, None, Span::new(0, 1)),
                                         Token::new(TokenType::End, None, Span::new(3, 4)));
        let children = node.get_children();
        assert_eq!(children[0], AstIndex(0));
        assert_eq!(children[1], AstIndex(1));
        assert_eq!(children.len(), 2);
    }

    #[test]
    fn compound_statement_node_get_value_returns_none() {
        let node = CompoundStmtNode::new(vec![AstIndex(0), AstIndex(1)],
                                         Token::new(TokenType::Begin, None, Span::new(0, 1)),
                                         Token::new(TokenType::End, None, Span::new(3, 4)));
        assert_eq!(node.get_value(), None);
    }

    #[test]
    fn compound_statement_node_get_span_returns_span() {
        let mut node = CompoundStmtNode::new(vec![AstIndex(0), AstIndex(1)],
                                             Token::new(TokenType::Begin, None, Span::new(0, 1)),
                                             Token::new(TokenType::End, None, Span::new(3, 4)));
        node.set_span(Span::new(2, 3));
        assert_eq!(node.get_span(), Span::new(2, 3));
    }

    #[test]
    fn compound_statement_node_visit_returns_void() {
        let mut ast = Ast::new();

        let index_stmt = cmpd_stmt_node!(ast,
                                         vec![binop_node!(ast,
                                                          int_node!(ast, 2),
                                                          int_node!(ast, 4),
                                                          OperatorType::Plus)]);
        let mut sym_tbl = SymbolTable::new();
        assert_eq!(ast.get_node(index_stmt)
                       .visit(&ast, &mut sym_tbl)
                       .unwrap(),
                   Value::Void);
    }
}
