//! This module contains the interpreter.

use std::collections::HashMap;
use std::cell::RefCell;

use errors::SyntaxError;
use ast::Ast;

/// The `ReturnValue` type. Used as a generic return value.
#[derive(Debug, PartialEq)]
pub enum ReturnValue {
    /// Return type void
    Void,
    /// Return type integer
    Integer(i64),
}

impl ReturnValue {
    /// Returns the inner value, if `self` is of variant `ReturnValue::Integer`.
    ///
    /// # Panics
    ///
    /// This function will panic if `self` is not of variant `ReturnValue::Integer`.
    pub fn extract_integer_value(self) -> i64 {
        match self {
            ReturnValue::Integer(val) => val,
            _ => panic!("Internal error (ReturnValue is no Integer)"),
        }
    }
}

/// Node visitor trait. Each node in the Abstract Syntax Tree (AST)
/// must implement this trait to allow the interpreter to traverse the AST.
pub trait NodeVisitor {
    /// "Visit" the node and perform a node-specific action (e.g. add two integers
    /// for the binary operator node).
    /// Takes a reference to an `Ast` in order to get access to the nodes in the AST.
    /// Takes a mutable reference to a symbol table to update or access symbols.
    fn visit(&self,
             ast: &Ast,
             sym_tbl: &mut HashMap<String, i64>)
             -> Result<ReturnValue, SyntaxError>;
}

/// The `Interpreter` type. Traverses the given AST.
pub struct Interpreter<'a> {
    ast: &'a Ast<'a>,
    symbol_table: RefCell<HashMap<String, i64>>,
}

impl<'a> Interpreter<'a> {
    /// Constructs a new `Interpreter` that traverses a given AST.
    pub fn new(ast: &'a Ast<'a>) -> Self {
        Interpreter {
            ast: ast,
            symbol_table: RefCell::new(HashMap::new()),
        }
    }

    /// Interprets the given AST.
    pub fn interpret(&self) -> Result<(), SyntaxError> {
        let mut symbol_table = self.symbol_table.borrow_mut();

        match self.ast.get_root() {
            Some(node) => node.visit(self.ast, &mut symbol_table).map(|_| ()),
            None => panic!("Internal Error (AST has no root)"),
        }
    }

    /// Lookup symbol in symbol table
    #[cfg(test)]
    fn lookup(&self, name: &String) -> Option<i64> {
        self.symbol_table.borrow().get(name).map(|val| *val)
    }

    /// Print symbol table
    pub fn print_symbols(&self) {
        for (name, value) in &*self.symbol_table.borrow() {
            println!("{} = {}", name, value);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokens::{TokenType, TokenValue, OperatorType};
    use ast::Ast;
    use lexer::MockLexer;
    use parser::Parser;

    #[test]
    fn interpreter_can_evaluate_nested_expressions() {
        // Input: BEGIN a := 7+3*(10 div (12 div (3+1)-1)) END.
        let tokens =
            vec![(TokenType::Begin, TokenValue::Empty),
                 (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                 (TokenType::Assign, TokenValue::Empty),
                 (TokenType::IntegerLiteral, TokenValue::Integer(7)),
                 (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                 (TokenType::IntegerLiteral, TokenValue::Integer(3)),
                 (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                 (TokenType::LParen, TokenValue::Empty),
                 (TokenType::IntegerLiteral, TokenValue::Integer(10)),
                 (TokenType::Operator, TokenValue::Operator(OperatorType::IntegerDivision)),
                 (TokenType::LParen, TokenValue::Empty),
                 (TokenType::IntegerLiteral, TokenValue::Integer(12)),
                 (TokenType::Operator, TokenValue::Operator(OperatorType::IntegerDivision)),
                 (TokenType::LParen, TokenValue::Empty),
                 (TokenType::IntegerLiteral, TokenValue::Integer(3)),
                 (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                 (TokenType::IntegerLiteral, TokenValue::Integer(1)),
                 (TokenType::RParen, TokenValue::Empty),
                 (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                 (TokenType::IntegerLiteral, TokenValue::Integer(1)),
                 (TokenType::RParen, TokenValue::Empty),
                 (TokenType::RParen, TokenValue::Empty),
                 (TokenType::End, TokenValue::Empty),
                 (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(22, interpreter.lookup(&"a".to_string()).unwrap());
    }

    #[test]
    fn interpreter_should_add_values_when_expression_is_addition() {
        // Input: BEGIN a := 3+4 END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(4)),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(7, interpreter.lookup(&"a".to_string()).unwrap());
    }

    #[test]
    fn interpreter_should_evaluate_chained_additions_and_subtractions_from_left_to_right() {
        // Input: BEGIN a := 1-2+3 END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(1)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(2)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(3)),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(2, interpreter.lookup(&"a".to_string()).unwrap());
    }

    #[test]
    fn interpreter_should_give_precedence_to_multiplication_and_division() {
        // Input: BEGIN a := 14+2*3-6 div 2 END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(14)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(2)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(6)),
                          (TokenType::Operator,
                           TokenValue::Operator(OperatorType::IntegerDivision)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(2)),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(17, interpreter.lookup(&"a".to_string()).unwrap());
    }

    #[test]
    fn interpreter_should_interpret_chained_additions() {
        // Input: BEGIN a := 1+3+5 END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(1)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(5)),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(9, interpreter.lookup(&"a".to_string()).unwrap());
    }

    #[test]
    fn interpreter_should_return_integer_value_if_input_consists_of_only_integer() {
        // Input: BEGIN a := 42 END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(42)),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(42, interpreter.lookup(&"a".to_string()).unwrap());
    }

    #[test]
    fn interpreter_should_return_negative_number_when_result_of_subtraction_is_negative() {
        // Input: BEGIN a := 3-4 END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(4)),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(-1, interpreter.lookup(&"a".to_string()).unwrap());
    }

    #[test]
    fn interpreter_should_subtract_values_when_expression_is_subtraction() {
        // Input: BEGIN a := 4-3 END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(4)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(3)),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(1, interpreter.lookup(&"a".to_string()).unwrap());
    }

    #[test]
    fn interpreter_returns_integer_if_input_consists_of_integer_in_parentheses() {
        // Input: BEGIN a := (6) END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::LParen, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(6)),
                          (TokenType::RParen, TokenValue::Empty),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(6, interpreter.lookup(&"a".to_string()).unwrap());
    }

    #[test]
    fn interpreter_returns_result_of_expr_if_input_consists_of_expr_in_parentheses() {
        // Input: BEGIN a := (6+3) END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::LParen, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(6)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(3)),
                          (TokenType::RParen, TokenValue::Empty),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(9, interpreter.lookup(&"a".to_string()).unwrap());
    }

    #[test]
    fn interpreter_should_evaluate_chained_multiplications_and_divisions_from_left_to_right() {
        // Input: BEGIN a := 6 div 2*3 END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(6)),
                          (TokenType::Operator,
                           TokenValue::Operator(OperatorType::IntegerDivision)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(2)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(3)),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(9, interpreter.lookup(&"a".to_string()).unwrap());
    }

    #[test]
    fn interpreter_should_interpret_chained_multiplications() {
        // Input: BEGIN a := 1*3*5 END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(1)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(5)),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(15, interpreter.lookup(&"a".to_string()).unwrap());
    }

    #[test]
    fn interpreter_should_multiply_values_when_expression_is_multiplication() {
        // Input: BEGIN a := 3*4 END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(4)),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(12, interpreter.lookup(&"a".to_string()).unwrap());
    }

    #[test]
    fn interpreter_should_return_error_when_division_by_zero() {
        // Input: BEGIN a := 1 div 0 END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(1)),
                          (TokenType::Operator,
                           TokenValue::Operator(OperatorType::IntegerDivision)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(0)),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_err());
    }

    #[test]
    fn interpreter_should_divide_values_when_expression_is_division() {
        // Input: BEGIN a := 6 div 2 END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(6)),
                          (TokenType::Operator,
                           TokenValue::Operator(OperatorType::IntegerDivision)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(2)),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(3, interpreter.lookup(&"a".to_string()).unwrap());
    }

    #[test]
    fn interpreter_should_negate_integer_when_expression_is_unary_minus() {
        // Input: BEGIN a := -2 END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(2)),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(-2, interpreter.lookup(&"a".to_string()).unwrap());
    }

    #[test]
    fn interpreter_should_negate_expression_when_expression_is_prefixed_with_unary_minus() {
        // Input: BEGIN a := -(2+3) END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::LParen, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(2)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(3)),
                          (TokenType::RParen, TokenValue::Empty),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(-5, interpreter.lookup(&"a".to_string()).unwrap());
    }

    #[test]
    fn interpreter_should_return_integer_when_expression_is_unary_plus() {
        // Input: BEGIN a := +2 END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(2)),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(2, interpreter.lookup(&"a".to_string()).unwrap());
    }

    #[test]
    fn interpreter_should_evaluate_chained_unary_operators() {
        // Input: BEGIN a := 5 - - - + - 3 END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(5)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::IntegerLiteral, TokenValue::Integer(3)),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(8, interpreter.lookup(&"a".to_string()).unwrap());
    }

    #[test]
    fn interpreter_assigns_multiple_variables() {
        // Input: BEGIN a := 2; b := 5 END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(2)),
                          (TokenType::Semicolon, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("b".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(5)),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(2, interpreter.lookup(&"a".to_string()).unwrap());
        assert_eq!(5, interpreter.lookup(&"b".to_string()).unwrap());
    }

    #[test]
    fn interpreter_handles_nested_compound_statements() {
        // Input: BEGIN a := 2; BEGIN b := 5 END; END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(2)),
                          (TokenType::Semicolon, TokenValue::Empty),
                          (TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("b".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(5)),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Semicolon, TokenValue::Empty),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(2, interpreter.lookup(&"a".to_string()).unwrap());
        assert_eq!(5, interpreter.lookup(&"b".to_string()).unwrap());
    }

    #[test]
    fn interpreter_can_assign_value_of_variable_to_other_variable() {
        // Input: BEGIN a := 2; b := a END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(2)),
                          (TokenType::Semicolon, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("b".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(2, interpreter.lookup(&"a".to_string()).unwrap());
        assert_eq!(2, interpreter.lookup(&"b".to_string()).unwrap());
    }

    #[test]
    fn interpreter_can_assign_value_of_expression_with_variable_to_other_variable() {
        // Input: BEGIN a := 2; b := 1 + a END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(2)),
                          (TokenType::Semicolon, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("b".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::IntegerLiteral, TokenValue::Integer(1)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(2, interpreter.lookup(&"a".to_string()).unwrap());
        assert_eq!(3, interpreter.lookup(&"b".to_string()).unwrap());
    }

    #[test]
    fn interpreter_returns_error_when_assigning_unknown_variable_to_other_variable() {
        // Input: BEGIN a := b END.
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("b".to_string())),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::Dot, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_err());
    }
}
