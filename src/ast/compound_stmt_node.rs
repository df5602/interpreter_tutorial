use std::fmt;
use std::collections::HashMap;

use tokens::{Token, TokenValue};
use errors::SyntaxError;
use ast::{Ast, AstNode, AstIndex};
use interpreter::{NodeVisitor, ReturnValue};

/// Compound statement node. A compound statement consists of
/// a 'BEGIN' keyword, followed by a list of statements and the
/// 'END' keyword.
#[derive(Debug)]
pub struct CompoundStmtNode {
    statement_list: Vec<AstIndex>,
    parent: Option<AstIndex>,
    position: (usize, usize),
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

    fn get_position(&self) -> (usize, usize) {
        self.position
    }

    fn set_position(&mut self, position: (usize, usize)) {
        self.position = position;
    }
}

impl NodeVisitor for CompoundStmtNode {
    fn visit(&self,
             ast: &Ast,
             sym_tbl: &mut HashMap<String, i64>)
             -> Result<ReturnValue, SyntaxError> {
        for statement in &self.statement_list {
            ast.get_node(*statement).visit(ast, sym_tbl)?;
        }
        Ok(ReturnValue::Void)
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
            position: (0, 0),
            token_begin: token_begin,
            token_end: token_end,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;
    use ast::{Ast, AstNode, AstIndex, IntegerNode, BinaryOperatorNode};
    use tokens::{Token, TokenType, TokenValue, OperatorType};
    use interpreter::ReturnValue;

    #[test]
    fn compound_statement_node_get_parent_returns_none_when_node_has_no_parent() {
        let node = CompoundStmtNode::new(vec![AstIndex(0), AstIndex(1)],
                                         Token::new(TokenType::Begin, None, (0, 1)),
                                         Token::new(TokenType::End, None, (3, 4)));
        assert_eq!(node.get_parent(), None);
    }

    #[test]
    fn compound_statement_node_set_parent_sets_parent_node() {
        let mut node = CompoundStmtNode::new(vec![AstIndex(0), AstIndex(1)],
                                             Token::new(TokenType::Begin, None, (0, 1)),
                                             Token::new(TokenType::End, None, (3, 4)));
        assert!(node.set_parent(AstIndex(2)));
        assert_eq!(node.get_parent(), Some(AstIndex(2)));
    }

    #[test]
    fn compound_statement_node_set_parent_fails_when_node_already_has_parent() {
        let mut node = CompoundStmtNode::new(vec![AstIndex(0), AstIndex(1)],
                                             Token::new(TokenType::Begin, None, (0, 1)),
                                             Token::new(TokenType::End, None, (3, 4)));
        assert!(node.set_parent(AstIndex(2)));
        assert!(!node.set_parent(AstIndex(3)));
    }

    #[test]
    fn compound_statement_node_get_children_returns_statements() {
        let node = CompoundStmtNode::new(vec![AstIndex(0), AstIndex(1)],
                                         Token::new(TokenType::Begin, None, (0, 1)),
                                         Token::new(TokenType::End, None, (3, 4)));
        let children = node.get_children();
        assert_eq!(children[0], AstIndex(0));
        assert_eq!(children[1], AstIndex(1));
        assert_eq!(children.len(), 2);
    }

    #[test]
    fn compound_statement_node_get_value_returns_none() {
        let node = CompoundStmtNode::new(vec![AstIndex(0), AstIndex(1)],
                                         Token::new(TokenType::Begin, None, (0, 1)),
                                         Token::new(TokenType::End, None, (3, 4)));
        assert_eq!(node.get_value(), None);
    }

    #[test]
    fn compound_statement_node_get_position_returns_position() {
        let mut node = CompoundStmtNode::new(vec![AstIndex(0), AstIndex(1)],
                                             Token::new(TokenType::Begin, None, (0, 1)),
                                             Token::new(TokenType::End, None, (3, 4)));
        node.set_position((2, 3));
        assert_eq!(node.get_position(), (2, 3));
    }

    #[test]
    fn compound_statement_node_visit_returns_void() {
        let mut ast = Ast::new();
        let lhs_1 =
            IntegerNode::new(2,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(2)), (0, 0)));
        let index_lhs_1 = ast.add_node(lhs_1);
        let lhs_2 =
            IntegerNode::new(4,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(4)), (0, 0)));
        let index_lhs_2 = ast.add_node(lhs_2);

        let op_node_1 =
            BinaryOperatorNode::new(index_lhs_1,
                                    index_lhs_2,
                                    OperatorType::Plus,
                                    Token::new(TokenType::Operator,
                                               Some(TokenValue::Operator(OperatorType::Plus)),
                                               (0, 0)));
        let index_op_1 = ast.add_node(op_node_1);

        let stmt_node = CompoundStmtNode::new(vec![index_op_1],
                                              Token::new(TokenType::Begin, None, (0, 1)),
                                              Token::new(TokenType::End, None, (3, 4)));
        let index_stmt = ast.add_node(stmt_node);
        let mut sym_tbl = HashMap::new();
        assert_eq!(ast.get_node(index_stmt).visit(&ast, &mut sym_tbl).unwrap(),
                   ReturnValue::Void);
    }
}
