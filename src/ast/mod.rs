//! This module contains all definitions required for building an
//! Abstract Syntax Tree (AST).

use std::fmt;
use std::{usize, cmp};

use tokens::{TokenValue, Span};
use interpreter::NodeVisitor;

/// The `AstNode` trait. Nodes implementing the `AstNode` trait must
/// also implement the `NodeVisitor` trait.
pub trait AstNode: NodeVisitor + fmt::Display {
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
    /// Returns the span in the input stream which correspond to `self`.
    fn get_span(&self) -> Span;
    /// Sets the span in the input stream which corresponds to `self`.
    fn set_span(&mut self, span: Span);
}

/// Index into the AST.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct AstIndex(pub usize);

impl fmt::Display for AstIndex {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[macro_use]
mod macros;

mod integer_node;
pub use self::integer_node::IntegerNode;

mod binary_operator_node;
pub use self::binary_operator_node::BinaryOperatorNode;

mod unary_operator_node;
pub use self::unary_operator_node::UnaryOperatorNode;

mod compound_stmt_node;
pub use self::compound_stmt_node::CompoundStmtNode;

mod variable_node;
pub use self::variable_node::VariableNode;

mod assignment_stmt_node;
pub use self::assignment_stmt_node::AssignmentStmtNode;

mod block_node;
pub use self::block_node::BlockNode;

mod type_node;
pub use self::type_node::TypeNode;

mod variable_decl_node;
pub use self::variable_decl_node::VariableDeclNode;

mod program_node;
pub use self::program_node::ProgramNode;

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
            result = writeln!(f, "{}: {}", i, node);
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

    /// Returns a mutable reference to the node stored at `index`.
    ///
    /// # Panics
    ///
    /// This function will panic if `index` is no valid index of
    /// the AST.
    pub fn get_node_mut(&mut self, index: AstIndex) -> &mut AstNode {
        &mut *self.nodes[index.0]
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
    /// Updates the span of the node stored at `index` to encompass the
    /// spans of all child nodes.
    fn set_as_parent(&mut self, index: AstIndex) {
        let children = (*self.nodes[index.0]).get_children();
        if children.is_empty() {
            return;
        }

        let span = (*self.nodes[index.0]).get_span();

        // Take span of node into account, not just its children
        let (mut pos_min, mut pos_max) = if span.start == 0 && span.end == 0 {
            (usize::MAX, usize::MIN)
        } else {
            (span.start, span.end)
        };

        for child in children {
            // Update parent links of child
            if !(*self.nodes[child.0]).set_parent(index) {
                panic!("Internal Error (cannot add multiple parents to AST node)");
            }
            if let Some(i) = self.non_connected_nodes.iter().position(|&n| n == child) {
                self.non_connected_nodes.remove(i);
            }
            // Get span of child
            let span = (*self.nodes[child.0]).get_span();
            pos_min = cmp::min(pos_min, span.start);
            pos_max = cmp::max(pos_max, span.end);
        }

        (*self.nodes[index.0]).set_span(Span::new(pos_min, pos_max));
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
        let index = int_node!(ast, 42);
        assert_eq!(index, AstIndex(0));
    }

    #[test]
    fn ast_add_node_returns_one_after_second_element_is_added() {
        let mut ast = Ast::new();
        int_node!(ast, 42);
        let index = int_node!(ast, 24);
        assert_eq!(index, AstIndex(1));
    }

    #[test]
    fn ast_add_node_sets_root_to_inserted_node_when_first_node_is_added() {
        let mut ast = Ast::new();
        let index = int_node!(ast, 42);
        assert_eq!(ast.root.unwrap(), index);
    }

    #[test]
    fn ast_add_node_creates_contiguous_graph_when_first_node_is_added() {
        let mut ast = Ast::new();
        int_node!(ast, 42);
        assert!(ast.is_contiguous());
    }

    #[test]
    fn ast_add_node_root_points_to_first_added_element_when_two_unrelated_nodes_are_added() {
        let mut ast = Ast::new();
        let index = int_node!(ast, 42);
        int_node!(ast, 24);
        assert_eq!(ast.root.unwrap(), index);
    }

    #[test]
    fn ast_add_node_creates_non_contiguous_graph_when_two_unrelated_nodes_are_added() {
        let mut ast = Ast::new();
        int_node!(ast, 42);
        int_node!(ast, 24);
        assert!(!ast.is_contiguous());
    }

    #[test]
    fn ast_add_node_parent_links_are_updated_when_node_with_child_links_is_added() {
        let mut ast = Ast::new();
        let index1 = int_node!(ast, 2);
        let index2 = int_node!(ast, 7);
        let index_op = binop_node!(ast, index1, index2, OperatorType::Times);

        assert_eq!((*ast.nodes[index1.0]).get_parent().unwrap(), index_op);
        assert_eq!((*ast.nodes[index2.0]).get_parent().unwrap(), index_op);
    }

    #[test]
    fn ast_add_node_sets_root_to_parent_node_when_parent_of_root_is_set() {
        let mut ast = Ast::new();
        let index_op = binop_node!(ast,
                                   int_node!(ast, 2),
                                   int_node!(ast, 7),
                                   OperatorType::Times);

        assert_eq!(ast.root.unwrap(), index_op);
    }

    #[test]
    fn ast_add_node_create_contiguous_graph_when_non_connected_node_is_child_of_connected_node() {
        let mut ast = Ast::new();
        binop_node!(ast,
                    int_node!(ast, 2),
                    int_node!(ast, 7),
                    OperatorType::Times);

        assert!(ast.is_contiguous());
    }

    #[test]
    fn ast_graph_with_two_disconnected_graphs_is_not_contiguous() {
        let mut ast = Ast::new();
        binop_node!(ast,
                    int_node!(ast, 2),
                    int_node!(ast, 7),
                    OperatorType::Times);
        binop_node!(ast,
                    int_node!(ast, 2),
                    int_node!(ast, 7),
                    OperatorType::Times);

        assert!(!ast.is_contiguous());
    }

    #[test]
    #[should_panic]
    fn ast_add_node_cannot_set_parent_of_node_which_already_has_a_parent() {
        let mut ast = Ast::new();
        let index1 = int_node!(ast, 2);
        let index2 = int_node!(ast, 7);
        binop_node!(ast, index1, index2, OperatorType::Times);
        let index3 = int_node!(ast, 3);
        binop_node!(ast, index2, index3, OperatorType::Plus);
    }
}
