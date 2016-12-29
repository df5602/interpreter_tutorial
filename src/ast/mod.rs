//! This module contains all definitions required for building an
//! Abstract Syntax Tree (AST).

use std::fmt;
use std::{usize, cmp};

use tokens::TokenValue;
use interpreter::NodeVisitor;

/// The `AstNode` trait. Nodes implementing the `AstNode` trait must
/// also implement the `NodeVisitor` trait.
pub trait AstNode: NodeVisitor {
    /// Returns the index of the parent node of `self`, if present, or `None`
    fn get_parent(&self) -> Option<AstIndex>;
    /// Sets `parent` as parent node of `self`.
    /// Returns true, if it suceeds (`self` has no parent node yet).
    /// Returns false, if `self` already has a parent node.
    fn set_parent(&mut self, parent: AstIndex) -> bool;
    /// Returns a vector of indices of the children of `self`.
    fn get_children(&self) -> Vec<AstIndex>;
    /// Returns the value stored in `self`, if applicable, or `None`.
    fn get_value(&self) -> Option<TokenValue>;
    /// Returns the position in the input stream which correspond to `self`.
    fn get_position(&self) -> (usize, usize);
    /// Sets the position in the input stream which corresponds to `self`.
    fn set_position(&mut self, position: (usize, usize));
    /// Returns a `String` representing `self`.
    fn print(&self) -> String;
}

/// Index into the AST.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct AstIndex(pub usize);

impl fmt::Display for AstIndex {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

mod binary_operator_node;
pub use self::binary_operator_node::BinaryOperatorNode;

mod unary_operator_node;
pub use self::unary_operator_node::UnaryOperatorNode;

mod integer_node;
pub use self::integer_node::IntegerNode;

mod compound_stmt_node;
pub use self::compound_stmt_node::CompoundStmtNode;

/// AST graph. Nodes are stored in a vector. All references to nodes
/// go via the index into this vector.
pub struct Ast<'a> {
    nodes: Vec<Box<AstNode + 'a>>,
    root: Option<AstIndex>,
    non_connected_nodes: Vec<AstIndex>,
}

impl<'a> fmt::Display for Ast<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut result = writeln!(f,
                                  "AST: Number of nodes: {}, Root: {:?}, Number of non-connected \
                                   nodes: {}",
                                  self.nodes.len(),
                                  self.root,
                                  self.non_connected_nodes.len());
        for (i, node) in self.nodes.iter().enumerate() {
            result = writeln!(f, "{}: {}", i, (*node).print());
        }
        result
    }
}

impl<'a> Ast<'a> {
    /// Creates a new (empty) AST.
    pub fn new() -> Self {
        Ast {
            nodes: Vec::new(),
            root: None,
            non_connected_nodes: Vec::new(),
        }
    }

    /// Returns a reference to the node stored at `index`.
    ///
    /// # Panics
    ///
    /// This function will panic if `index` is no valid index of
    /// the AST.
    pub fn get_node(&self, index: AstIndex) -> &AstNode {
        &*self.nodes[index.0]
    }

    /// Returns a reference to the root node of the AST if available, `None` otherwise.
    pub fn get_root(&self) -> Option<&AstNode> {
        self.root.as_ref().map(|index| &*self.nodes[index.0])
    }

    /// Inserts a node into the AST and returns the index of the new node.
    pub fn add_node<N: AstNode + 'a>(&mut self, node: N) -> AstIndex {
        self.nodes.push(Box::new(node));

        let inserted_index = AstIndex(self.nodes.len() - 1);

        self.set_as_parent(inserted_index);

        if self.root.is_none() {
            self.root = Some(inserted_index);
        } else {
            loop {
                let root_node = &self.nodes[self.root.unwrap().0];
                match (*root_node).get_parent() {
                    Some(i) => self.root = Some(i),
                    None => break,
                }
            }
        }

        if !self.is_connected_to_root(inserted_index) {
            self.non_connected_nodes.push(inserted_index);
        }

        inserted_index
    }

    /// Sets the node stored at `index` as the parent node of its children.
    /// Updates the position of the node stored at `index` to encompass the
    /// positions of all child nodes.
    fn set_as_parent(&mut self, index: AstIndex) {
        let children = (*self.nodes[index.0]).get_children();
        if children.is_empty() {
            return;
        }

        let mut pos_min = usize::MAX;
        let mut pos_max = usize::MIN;

        for child in children {
            // Update parent links of child
            if !(*self.nodes[child.0]).set_parent(index) {
                panic!("Internal Error (cannot add multiple parents to AST node)");
            }
            if let Some(i) = self.non_connected_nodes.iter().position(|&n| n == child) {
                self.non_connected_nodes.remove(i);
            }
            // Get position of child
            let position = (*self.nodes[child.0]).get_position();
            pos_min = cmp::min(pos_min, position.0);
            pos_max = cmp::max(pos_max, position.1);
        }

        (*self.nodes[index.0]).set_position((pos_min, pos_max));
    }

    /// Checks whether the node stored at `index` is connected to the
    /// root node of the AST.
    fn is_connected_to_root(&self, index: AstIndex) -> bool {
        let mut current = index;

        loop {
            let parent = (*self.nodes[current.0]).get_parent();
            match parent {
                Some(i) => current = i,
                None => break,
            }
        }

        self.root == Some(current)
    }

    /// Returns true if the AST is contiguous, or false otherwise.
    pub fn is_contiguous(&self) -> bool {
        self.non_connected_nodes.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokens::*;

    #[test]
    fn ast_newly_created_graph_should_have_no_root() {
        let ast = Ast::new();
        assert!(ast.root.is_none());
    }

    #[test]
    fn ast_add_node_returns_zero_after_first_element_is_added() {
        let mut ast = Ast::new();
        let int_node =
            IntegerNode::new(42,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(42)), (0, 0)));
        let index = ast.add_node(int_node);
        assert_eq!(index, AstIndex(0));
    }

    #[test]
    fn ast_add_node_returns_one_after_second_element_is_added() {
        let mut ast = Ast::new();
        let int_node_1 =
            IntegerNode::new(42,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(42)), (0, 0)));
        let _i = ast.add_node(int_node_1);
        let int_node_2 =
            IntegerNode::new(24,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(24)), (0, 0)));
        let index_2 = ast.add_node(int_node_2);
        assert_eq!(index_2, AstIndex(1));
    }

    #[test]
    fn ast_add_node_sets_root_to_inserted_node_when_first_node_is_added() {
        let mut ast = Ast::new();
        let int_node =
            IntegerNode::new(42,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(42)), (0, 0)));
        let index = ast.add_node(int_node);
        assert_eq!(ast.root.unwrap(), index);
    }

    #[test]
    fn ast_add_node_creates_contiguous_graph_when_first_node_is_added() {
        let mut ast = Ast::new();
        let int_node =
            IntegerNode::new(42,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(42)), (0, 0)));
        let _index = ast.add_node(int_node);
        assert!(ast.is_contiguous());
    }

    #[test]
    fn ast_add_node_root_points_to_first_added_element_when_two_unrelated_nodes_are_added() {
        let mut ast = Ast::new();
        let int_node1 =
            IntegerNode::new(42,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(42)), (0, 0)));
        let index1 = ast.add_node(int_node1);
        let int_node2 =
            IntegerNode::new(24,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(24)), (0, 0)));
        let _index2 = ast.add_node(int_node2);
        assert_eq!(ast.root.unwrap(), index1);
    }

    #[test]
    fn ast_add_node_creates_non_contiguous_graph_when_two_unrelated_nodes_are_added() {
        let mut ast = Ast::new();
        let int_node1 =
            IntegerNode::new(42,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(42)), (0, 0)));
        let _index1 = ast.add_node(int_node1);
        let int_node2 =
            IntegerNode::new(24,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(24)), (0, 0)));
        let _index2 = ast.add_node(int_node2);
        assert!(!ast.is_contiguous());
    }

    #[test]
    fn ast_add_node_parent_links_are_updated_when_node_with_child_links_is_added() {
        let mut ast = Ast::new();
        let int_node1 =
            IntegerNode::new(2,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(2)), (0, 0)));
        let index1 = ast.add_node(int_node1);
        let int_node2 =
            IntegerNode::new(7,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(7)), (0, 0)));
        let index2 = ast.add_node(int_node2);
        let op_node =
            BinaryOperatorNode::new(index1,
                                    index2,
                                    OperatorType::Times,
                                    Token::new(TokenType::Operator,
                                               Some(TokenValue::Operator(OperatorType::Times)),
                                               (0, 0)));
        let index_op = ast.add_node(op_node);

        assert_eq!((*ast.nodes[index1.0]).get_parent().unwrap(), index_op);
        assert_eq!((*ast.nodes[index2.0]).get_parent().unwrap(), index_op);
    }

    #[test]
    fn ast_add_node_sets_root_to_parent_node_when_parent_of_root_is_set() {
        let mut ast = Ast::new();
        let int_node1 =
            IntegerNode::new(2,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(2)), (0, 0)));
        let index1 = ast.add_node(int_node1);
        let int_node2 =
            IntegerNode::new(7,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(7)), (0, 0)));
        let index2 = ast.add_node(int_node2);
        let op_node =
            BinaryOperatorNode::new(index1,
                                    index2,
                                    OperatorType::Times,
                                    Token::new(TokenType::Operator,
                                               Some(TokenValue::Operator(OperatorType::Times)),
                                               (0, 0)));
        let index_op = ast.add_node(op_node);

        assert_eq!(ast.root.unwrap(), index_op);
    }

    #[test]
    fn ast_add_node_creates_contiguous_graph_when_non_connected_node_is_child_of_connected_node
        () {
        let mut ast = Ast::new();
        let int_node1 =
            IntegerNode::new(2,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(2)), (0, 0)));
        let index1 = ast.add_node(int_node1);
        let int_node2 =
            IntegerNode::new(7,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(7)), (0, 0)));
        let index2 = ast.add_node(int_node2);
        let op_node =
            BinaryOperatorNode::new(index1,
                                    index2,
                                    OperatorType::Times,
                                    Token::new(TokenType::Operator,
                                               Some(TokenValue::Operator(OperatorType::Times)),
                                               (0, 0)));
        let _index_op = ast.add_node(op_node);

        assert!(ast.is_contiguous());
    }

    #[test]
    fn ast_graph_with_two_disconnected_graphs_is_not_contiguous() {
        let mut ast = Ast::new();
        let int_node1 =
            IntegerNode::new(2,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(2)), (0, 0)));
        let index1 = ast.add_node(int_node1);
        let int_node2 =
            IntegerNode::new(7,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(7)), (0, 0)));
        let index2 = ast.add_node(int_node2);
        let op_node1 =
            BinaryOperatorNode::new(index1,
                                    index2,
                                    OperatorType::Times,
                                    Token::new(TokenType::Operator,
                                               Some(TokenValue::Operator(OperatorType::Times)),
                                               (0, 0)));
        let _index_op1 = ast.add_node(op_node1);
        let int_node3 =
            IntegerNode::new(2,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(2)), (0, 0)));
        let index3 = ast.add_node(int_node3);
        let int_node4 =
            IntegerNode::new(7,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(7)), (0, 0)));
        let index4 = ast.add_node(int_node4);
        let op_node2 =
            BinaryOperatorNode::new(index3,
                                    index4,
                                    OperatorType::Times,
                                    Token::new(TokenType::Operator,
                                               Some(TokenValue::Operator(OperatorType::Times)),
                                               (0, 0)));
        let _index_op2 = ast.add_node(op_node2);

        assert!(!ast.is_contiguous());
    }

    #[test]
    #[should_panic]
    fn ast_add_node_cannot_set_parent_of_node_which_already_has_a_parent() {
        let mut ast = Ast::new();
        let int_node1 =
            IntegerNode::new(2,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(2)), (0, 0)));
        let index1 = ast.add_node(int_node1);
        let int_node2 =
            IntegerNode::new(7,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(7)), (0, 0)));
        let index2 = ast.add_node(int_node2);
        let op_node1 =
            BinaryOperatorNode::new(index1,
                                    index2,
                                    OperatorType::Times,
                                    Token::new(TokenType::Operator,
                                               Some(TokenValue::Operator(OperatorType::Times)),
                                               (0, 0)));
        let _index_op1 = ast.add_node(op_node1);
        let int_node3 =
            IntegerNode::new(3,
                             Token::new(TokenType::Integer, Some(TokenValue::Integer(3)), (0, 0)));
        let index3 = ast.add_node(int_node3);
        let op_node2 =
            BinaryOperatorNode::new(index2,
                                    index3,
                                    OperatorType::Plus,
                                    Token::new(TokenType::Operator,
                                               Some(TokenValue::Operator(OperatorType::Plus)),
                                               (0, 0)));
        let _index_op2 = ast.add_node(op_node2);
    }
}
