//! This module contains the interpreter.
use std::fmt;
use std::cell::RefCell;

use errors::SyntaxError;
use symbol_table::SymbolTable;
use ast::Ast;

/// The `Value` type. Used as a generic value to use as return value or argument value.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    /// No value
    Void,
    /// Not initialized
    NotInitialized,
    /// Integer
    Integer(i64),
    /// Real
    Real(f64),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Value::Void => write!(f, "void"),
            Value::NotInitialized => write!(f, "not initialized"),
            Value::Integer(value) => write!(f, "{}", value),
            Value::Real(value) => write!(f, "{}", value),
        }
    }
}

impl Value {
    /// Returns the inner value, if `self` is of variant `Value::Integer`.
    ///
    /// # Panics
    ///
    /// This function will panic if `self` is not of variant `Value::Integer`.
    pub fn extract_integer_value(self) -> i64 {
        match self {
            Value::Integer(val) => val,
            _ => panic!("Internal error (Value is no Integer)"),
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
    fn visit(&self, ast: &Ast, sym_tbl: &mut SymbolTable) -> Result<Value, SyntaxError>;
}

/// The `Interpreter` type. Traverses the given AST.
pub struct Interpreter<'a> {
    ast: &'a Ast<'a>,
    symbol_table: RefCell<SymbolTable>,
}

impl<'a> Interpreter<'a> {
    /// Constructs a new `Interpreter` that traverses a given AST.
    pub fn new(ast: &'a Ast<'a>) -> Self {
        Interpreter {
            ast: ast,
            symbol_table: RefCell::new(SymbolTable::new()),
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
    fn lookup(&self, name: &String) -> Option<Value> {
        self.symbol_table.borrow().value(name)
    }

    /// Print symbol table
    pub fn print_symbols(&self) {
        self.symbol_table.borrow().print_symbols();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokens::{TokenType, TokenValue, OperatorType, Type};
    use ast::Ast;
    use lexer::MockLexer;
    use parser::Parser;

    fn parse_from<'a>(tokens: Vec<(TokenType, TokenValue)>) -> Ast<'a> {
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        ast
    }

    fn interpret_and_check_values(ast: &Ast, identifiers: Vec<&str>, values: Vec<Value>) {
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_ok());
        assert_eq!(identifiers.len(), values.len());
        for (i, identifier) in identifiers.iter().enumerate() {
            assert_eq!(interpreter.lookup(&identifier.to_string()).unwrap(),
                       values[i]);
        }
    }

    #[test]
    fn interpreter_can_evaluate_nested_expressions() {
        // Input: PROGRAM Test; VAR a: INTEGER; BEGIN a := 7+3*(10 div (12 div (3+1)-1)) END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(7),
                          plus!(),
                          integer_lit!(3),
                          times!(),
                          lparen!(),
                          integer_lit!(10),
                          int_div!(),
                          lparen!(),
                          integer_lit!(12),
                          int_div!(),
                          lparen!(),
                          integer_lit!(3),
                          plus!(),
                          integer_lit!(1),
                          rparen!(),
                          minus!(),
                          integer_lit!(1),
                          rparen!(),
                          rparen!(),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        interpret_and_check_values(&ast, vec!["a"], vec![Value::Integer(22)]);
    }

    #[test]
    fn interpreter_should_add_values_when_expression_is_addition() {
        // Input: PROGRAM Test; VAR a: INTEGER; BEGIN a := 3+4 END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(3),
                          plus!(),
                          integer_lit!(4),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        interpret_and_check_values(&ast, vec!["a"], vec![Value::Integer(7)]);
    }

    #[test]
    fn interpreter_should_evaluate_chained_additions_and_subtractions_from_left_to_right() {
        // Input: PROGRAM Test; VAR a: INTEGER; BEGIN a := 1-2+3 END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(1),
                          minus!(),
                          integer_lit!(2),
                          plus!(),
                          integer_lit!(3),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        interpret_and_check_values(&ast, vec!["a"], vec![Value::Integer(2)]);
    }

    #[test]
    fn interpreter_should_give_precedence_to_multiplication_and_division() {
        // Input: PROGRAM Test; VAR a: INTEGER; BEGIN a := 14+2*3-6 div 2 END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(14),
                          plus!(),
                          integer_lit!(2),
                          times!(),
                          integer_lit!(3),
                          minus!(),
                          integer_lit!(6),
                          int_div!(),
                          integer_lit!(2),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        interpret_and_check_values(&ast, vec!["a"], vec![Value::Integer(17)]);
    }

    #[test]
    fn interpreter_should_interpret_chained_additions() {
        // Input: PROGRAM Test; VAR a: INTEGER; BEGIN a := 1+3+5 END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(1),
                          plus!(),
                          integer_lit!(3),
                          plus!(),
                          integer_lit!(5),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        interpret_and_check_values(&ast, vec!["a"], vec![Value::Integer(9)]);
    }

    #[test]
    fn interpreter_should_return_integer_value_if_input_consists_of_only_integer() {
        // Input: PROGRAM Test; VAR a: INTEGER; BEGIN a := 42 END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(42),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        interpret_and_check_values(&ast, vec!["a"], vec![Value::Integer(42)]);
    }

    #[test]
    fn interpreter_should_return_negative_number_when_result_of_subtraction_is_negative() {
        // Input: PROGRAM Test; VAR a: INTEGER; BEGIN a := 3-4 END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(3),
                          minus!(),
                          integer_lit!(4),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        interpret_and_check_values(&ast, vec!["a"], vec![Value::Integer(-1)]);
    }

    #[test]
    fn interpreter_should_subtract_values_when_expression_is_subtraction() {
        // Input: PROGRAM Test; VAR a: INTEGER; BEGIN a := 4-3 END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(4),
                          minus!(),
                          integer_lit!(3),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        interpret_and_check_values(&ast, vec!["a"], vec![Value::Integer(1)]);
    }

    #[test]
    fn interpreter_returns_integer_if_input_consists_of_integer_in_parentheses() {
        // Input: PROGRAM Test; VAR a: INTEGER; BEGIN a := (6) END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          lparen!(),
                          integer_lit!(6),
                          rparen!(),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        interpret_and_check_values(&ast, vec!["a"], vec![Value::Integer(6)]);
    }

    #[test]
    fn interpreter_returns_result_of_expr_if_input_consists_of_expr_in_parentheses() {
        // Input: PROGRAM Test; VAR a: INTEGER; BEGIN a := (6+3) END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          lparen!(),
                          integer_lit!(6),
                          plus!(),
                          integer_lit!(3),
                          rparen!(),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        interpret_and_check_values(&ast, vec!["a"], vec![Value::Integer(9)]);
    }

    #[test]
    fn interpreter_should_evaluate_chained_multiplications_and_divisions_from_left_to_right() {
        // Input: PROGRAM Test; VAR a: INTEGER; BEGIN a := 6 div 2*3 END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(6),
                          int_div!(),
                          integer_lit!(2),
                          times!(),
                          integer_lit!(3),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        interpret_and_check_values(&ast, vec!["a"], vec![Value::Integer(9)]);
    }

    #[test]
    fn interpreter_should_interpret_chained_multiplications() {
        // Input: PROGRAM Test; VAR a: INTEGER; BEGIN a := 1*3*5 END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(1),
                          times!(),
                          integer_lit!(3),
                          times!(),
                          integer_lit!(5),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        interpret_and_check_values(&ast, vec!["a"], vec![Value::Integer(15)]);
    }

    #[test]
    fn interpreter_should_multiply_values_when_expression_is_multiplication() {
        // Input: PROGRAM Test; VAR a: INTEGER; BEGIN a := 3*4 END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(3),
                          times!(),
                          integer_lit!(4),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        interpret_and_check_values(&ast, vec!["a"], vec![Value::Integer(12)]);
    }

    #[test]
    fn interpreter_should_return_error_when_division_by_zero() {
        // Input: PROGRAM Test; VAR a: INTEGER; BEGIN a := 1 div 0 END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(1),
                          int_div!(),
                          integer_lit!(0),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_err());
    }

    #[test]
    fn interpreter_should_divide_values_when_expression_is_division() {
        // Input: PROGRAM Test; VAR a: INTEGER; BEGIN a := 6 div 2 END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(6),
                          int_div!(),
                          integer_lit!(2),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        interpret_and_check_values(&ast, vec!["a"], vec![Value::Integer(3)]);
    }

    #[test]
    fn interpreter_should_negate_integer_when_expression_is_unary_minus() {
        // Input: PROGRAM Test; VAR a: INTEGER; BEGIN a := -2 END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          minus!(),
                          integer_lit!(2),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        interpret_and_check_values(&ast, vec!["a"], vec![Value::Integer(-2)]);
    }

    #[test]
    fn interpreter_should_negate_expression_when_expression_is_prefixed_with_unary_minus() {
        // Input: PROGRAM Test; VAR a: INTEGER; BEGIN a := -(2+3) END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          minus!(),
                          lparen!(),
                          integer_lit!(2),
                          plus!(),
                          integer_lit!(3),
                          rparen!(),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        interpret_and_check_values(&ast, vec!["a"], vec![Value::Integer(-5)]);
    }

    #[test]
    fn interpreter_should_return_integer_when_expression_is_unary_plus() {
        // Input: PROGRAM Test; VAR a: INTEGER; BEGIN a := +2 END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          plus!(),
                          integer_lit!(2),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        interpret_and_check_values(&ast, vec!["a"], vec![Value::Integer(2)]);
    }

    #[test]
    fn interpreter_should_evaluate_chained_unary_operators() {
        // Input: PROGRAM Test; VAR a: INTEGER; BEGIN a := 5 - - - + - 3 END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(5),
                          minus!(),
                          minus!(),
                          minus!(),
                          plus!(),
                          minus!(),
                          integer_lit!(3),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        interpret_and_check_values(&ast, vec!["a"], vec![Value::Integer(8)]);
    }

    #[test]
    fn interpreter_assigns_multiple_variables() {
        // Input: PROGRAM Test; VAR a, b: INTEGER; BEGIN a := 2; b := 5 END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          comma!(),
                          identifier!("b"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(2),
                          semicolon!(),
                          identifier!("b"),
                          assign!(),
                          integer_lit!(5),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        interpret_and_check_values(&ast,
                                   vec!["a", "b"],
                                   vec![Value::Integer(2), Value::Integer(5)]);
    }

    #[test]
    fn interpreter_handles_nested_compound_statements() {
        // Input: PROGRAM Test; VAR a, b: INTEGER; BEGIN a := 2; BEGIN b := 5 END; END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          comma!(),
                          identifier!("b"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(2),
                          semicolon!(),
                          begin!(),
                          identifier!("b"),
                          assign!(),
                          integer_lit!(5),
                          end!(),
                          semicolon!(),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        interpret_and_check_values(&ast,
                                   vec!["a", "b"],
                                   vec![Value::Integer(2), Value::Integer(5)]);
    }

    #[test]
    fn interpreter_can_assign_value_of_variable_to_other_variable() {
        // Input: PROGRAM Test; VAR a, b: INTEGER; BEGIN a := 2; b := a END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          comma!(),
                          identifier!("b"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(2),
                          semicolon!(),
                          identifier!("b"),
                          assign!(),
                          identifier!("a"),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        interpret_and_check_values(&ast,
                                   vec!["a", "b"],
                                   vec![Value::Integer(2), Value::Integer(2)]);
    }

    #[test]
    fn interpreter_can_assign_value_of_expression_with_variable_to_other_variable() {
        // Input: PROGRAM Test; VAR a, b: INTEGER; BEGIN a := 2; b := 1 + a END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          comma!(),
                          identifier!("b"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(2),
                          semicolon!(),
                          identifier!("b"),
                          assign!(),
                          integer_lit!(1),
                          plus!(),
                          identifier!("a"),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        interpret_and_check_values(&ast,
                                   vec!["a", "b"],
                                   vec![Value::Integer(2), Value::Integer(3)]);
    }

    #[test]
    fn interpreter_returns_error_when_assigning_unknown_variable_to_other_variable() {
        // Input: PROGRAM Test; VAR a: INTEGER; BEGIN a := b END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          var!(),
                          identifier!("a"),
                          colon!(),
                          integer!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          identifier!("b"),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_err());
    }

    #[test]
    fn interpreter_returns_error_when_number_is_assigned_to_undeclared_variable() {
        // Input: PROGRAM Test; BEGIN a := 10 END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(10),
                          end!(),
                          dot!()];
        let ast = parse_from(tokens);
        let interpreter = Interpreter::new(&ast);
        assert!(interpreter.interpret().is_err());
    }
}
