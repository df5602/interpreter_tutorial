use std::fmt;
use std::collections::HashMap;

use tokens::{Token, TokenValue};
use errors::SyntaxError;
use ast::{Ast, AstNode, AstIndex};
use interpreter::{NodeVisitor, ReturnValue};

/// Assignment statement. It consists of the following form:
/// VARIABLE := EXPRESSION
#[derive(Debug)]
pub struct AssignmentStmtNode {
    variable: AstIndex,
    expression: AstIndex,
    parent: Option<AstIndex>,
    position: (usize, usize),
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

    fn get_position(&self) -> (usize, usize) {
        self.position
    }

    fn set_position(&mut self, position: (usize, usize)) {
        self.position = position;
    }
}

impl NodeVisitor for AssignmentStmtNode {
    fn visit(&self,
             ast: &Ast,
             sym_tbl: &mut HashMap<String, i64>)
             -> Result<ReturnValue, SyntaxError> {
        let name = ast.get_node(self.variable).get_value().unwrap().extract_identifier_value();
        let expression = ast.get_node(self.expression).visit(ast, sym_tbl)?.extract_integer_value();
        sym_tbl.insert(name, expression);
        Ok(ReturnValue::Void)
    }
}

impl AssignmentStmtNode {
    /// Constructs a new assignment statement node.
    pub fn new(variable: AstIndex, expression: AstIndex, token: Token) -> Self {
        AssignmentStmtNode {
            variable: variable,
            expression: expression,
            parent: None,
            position: (0, 0),
            token: token,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;
    use tokens::{Token, TokenType, TokenValue};
    use ast::{Ast, AstNode, AstIndex, VariableNode, IntegerNode, CompoundStmtNode};
    use interpreter::ReturnValue;

    #[test]
    fn assignment_statement_node_get_parent_returns_none_when_node_has_no_parent() {
        let node = AssignmentStmtNode::new(AstIndex(0),
                                           AstIndex(1),
                                           Token::new(TokenType::Assign, None, (0, 2)));
        assert_eq!(node.get_parent(), None);
    }

    #[test]
    fn assignment_statement_node_set_parent_sets_parent_node() {
        let mut node = AssignmentStmtNode::new(AstIndex(0),
                                               AstIndex(1),
                                               Token::new(TokenType::Assign, None, (0, 2)));
        assert!(node.set_parent(AstIndex(2)));
        assert_eq!(node.get_parent(), Some(AstIndex(2)));
    }

    #[test]
    fn assignment_statement_node_set_parent_fails_when_node_already_has_parent() {
        let mut node = AssignmentStmtNode::new(AstIndex(0),
                                               AstIndex(1),
                                               Token::new(TokenType::Assign, None, (0, 2)));
        assert!(node.set_parent(AstIndex(2)));
        assert!(!node.set_parent(AstIndex(3)));
    }

    #[test]
    fn assignment_statement_node_get_children_returns_operand() {
        let node = AssignmentStmtNode::new(AstIndex(0),
                                           AstIndex(1),
                                           Token::new(TokenType::Assign, None, (0, 2)));
        let children = node.get_children();
        assert_eq!(children[0], AstIndex(0));
        assert_eq!(children[1], AstIndex(1));
        assert_eq!(children.len(), 2);
    }

    #[test]
    fn assignment_statement_node_get_value_returns_none() {
        let node = AssignmentStmtNode::new(AstIndex(0),
                                           AstIndex(1),
                                           Token::new(TokenType::Assign, None, (0, 2)));
        assert_eq!(node.get_value(), None);
    }

    #[test]
    fn assignment_statement_node_get_position_returns_position() {
        let mut node = AssignmentStmtNode::new(AstIndex(0),
                                               AstIndex(1),
                                               Token::new(TokenType::Assign, None, (0, 2)));
        node.set_position((4, 5));
        assert_eq!(node.get_position(), (4, 5));
    }

    #[test]
    fn assignment_statement_node_visit_adds_entry_to_symbol_table() {
        let mut ast = Ast::new();
        let mut sym_tbl = HashMap::new();

        let var_node = VariableNode::new("a".to_string(),
                                         Token::new(TokenType::Identifier,
                                                    Some(TokenValue::Identifier("a".to_string())),
                                                    (0, 1)));
        let int_node =
            IntegerNode::new(42,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(42)), (3, 5)));

        let index_var = ast.add_node(var_node);
        let index_int = ast.add_node(int_node);

        let ass_node = AssignmentStmtNode::new(index_var,
                                               index_int,
                                               Token::new(TokenType::Assign, None, (1, 3)));
        let index_ass = ast.add_node(ass_node);

        assert_eq!(sym_tbl.get(&"a".to_string()), None);
        assert_eq!(ast.get_node(index_ass).visit(&ast, &mut sym_tbl).unwrap(),
                   ReturnValue::Void);
        assert_eq!(sym_tbl.get(&"a".to_string()), Some(&42));
    }

    #[test]
    fn assignment_statement_node_visit_updates_entry_in_symbol_table_if_exists() {
        let mut ast = Ast::new();
        let mut sym_tbl = HashMap::new();

        let var_node_1 =
            VariableNode::new("a".to_string(),
                              Token::new(TokenType::Identifier,
                                         Some(TokenValue::Identifier("a".to_string())),
                                         (0, 1)));
        let int_node_42 =
            IntegerNode::new(42,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(42)), (3, 5)));

        let index_var_1 = ast.add_node(var_node_1);
        let index_int_42 = ast.add_node(int_node_42);

        let ass_node_1 = AssignmentStmtNode::new(index_var_1,
                                                 index_int_42,
                                                 Token::new(TokenType::Assign, None, (1, 3)));
        let index_ass_1 = ast.add_node(ass_node_1);

        let var_node_2 =
            VariableNode::new("a".to_string(),
                              Token::new(TokenType::Identifier,
                                         Some(TokenValue::Identifier("a".to_string())),
                                         (0, 1)));
        let int_node_24 =
            IntegerNode::new(24,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(24)), (3, 5)));

        let index_var_2 = ast.add_node(var_node_2);
        let index_int_24 = ast.add_node(int_node_24);

        let ass_node_2 = AssignmentStmtNode::new(index_var_2,
                                                 index_int_24,
                                                 Token::new(TokenType::Assign, None, (1, 3)));
        let index_ass_2 = ast.add_node(ass_node_2);

        let stmt_node = CompoundStmtNode::new(vec![index_ass_1, index_ass_2],
                                              Token::new(TokenType::Begin, None, (0, 1)),
                                              Token::new(TokenType::End, None, (3, 4)));
        let index_stmt = ast.add_node(stmt_node);

        assert_eq!(sym_tbl.get(&"a".to_string()), None);

        assert!(ast.get_node(index_stmt).visit(&ast, &mut sym_tbl).is_ok());

        assert_eq!(sym_tbl.get(&"a".to_string()), Some(&24));
    }
}
