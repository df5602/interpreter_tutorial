use errors::SyntaxError;
use ast::Ast;

pub trait NodeVisitor {
    fn visit(&self, ast: &Ast) -> Result<i64, SyntaxError>;
}

pub struct Interpreter<'a> {
    ast: &'a Ast<'a>,
}

impl<'a> Interpreter<'a> {
    pub fn new(ast: &'a Ast<'a>) -> Self {
        Interpreter { ast: ast }
    }

    pub fn interpret(&self) -> Result<i64, SyntaxError> {
        match self.ast.get_root() {
            Some(node) => node.visit(self.ast),
            None => {
                Err(SyntaxError {
                    msg: "Internal Error (AST has no root)".to_string(),
                    position: (0, 0),
                })
            }
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
        // Input: 7+3*(10/(12/(3+1)-1))
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(7)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::LParen, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(10)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Division)),
                          (TokenType::LParen, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(12)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Division)),
                          (TokenType::LParen, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(1)),
                          (TokenType::RParen, TokenValue::Empty),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::Integer, TokenValue::Integer(1)),
                          (TokenType::RParen, TokenValue::Empty),
                          (TokenType::RParen, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        let result = interpreter.interpret();
        assert_eq!(22, result.unwrap());
    }

    #[test]
    fn interpreter_should_add_values_when_expression_is_addition() {
        // Input: 3+4
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(4))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        let result = interpreter.interpret();
        assert_eq!(7, result.unwrap());
    }

    #[test]
    fn interpreter_should_evaluate_chained_additions_and_subtractions_from_left_to_right() {
        // Input: 1-2+3
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(1)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::Integer, TokenValue::Integer(2)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(3))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        let result = interpreter.interpret();
        assert_eq!(2, result.unwrap());
    }

    #[test]
    fn interpreter_should_give_precedence_to_multiplication_and_division() {
        // Input: 14+2*3-6/2
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(14)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(2)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::Integer, TokenValue::Integer(6)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Division)),
                          (TokenType::Integer, TokenValue::Integer(2))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        let result = interpreter.interpret();
        assert_eq!(17, result.unwrap());
    }

    #[test]
    fn interpreter_should_interpret_chained_additions() {
        // Input: 1+3+5
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(1)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(5))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        let result = interpreter.interpret();
        assert_eq!(9, result.unwrap());
    }

    #[test]
    fn interpreter_should_return_integer_value_if_input_consists_of_only_integer() {
        // Input: 42
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(42))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        let result = interpreter.interpret();
        assert_eq!(42, result.unwrap());
    }

    #[test]
    fn interpreter_should_return_negative_number_when_result_of_subtraction_is_negative() {
        // Input: 3-4
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::Integer, TokenValue::Integer(4))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        let result = interpreter.interpret();
        assert_eq!(-1, result.unwrap());
    }

    #[test]
    fn interpreter_should_subtract_values_when_expression_is_subtraction() {
        // Input: 4-3
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(4)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::Integer, TokenValue::Integer(3))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        let result = interpreter.interpret();
        assert_eq!(1, result.unwrap());
    }

    #[test]
    fn interpreter_returns_integer_if_input_consists_of_integer_in_parentheses() {
        // Input: (6)
        let tokens = vec![(TokenType::LParen, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(6)),
                          (TokenType::RParen, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        let result = interpreter.interpret();
        assert_eq!(6, result.unwrap());
    }

    #[test]
    fn interpreter_returns_result_of_expr_if_input_consists_of_expr_in_parentheses() {
        // Input: (6+3)
        let tokens = vec![(TokenType::LParen, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(6)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::RParen, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        let result = interpreter.interpret();
        assert_eq!(9, result.unwrap());
    }

    #[test]
    fn interpreter_should_evaluate_chained_multiplications_and_divisions_from_left_to_right() {
        // Input: 6/2*3
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(6)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Division)),
                          (TokenType::Integer, TokenValue::Integer(2)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::Integer, TokenValue::Integer(3))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        let result = interpreter.interpret();
        assert_eq!(9, result.unwrap());
    }

    #[test]
    fn interpreter_should_interpret_chained_multiplications() {
        // Input: 1*3*5
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(1)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::Integer, TokenValue::Integer(5))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        let result = interpreter.interpret();
        assert_eq!(15, result.unwrap());
    }

    #[test]
    fn interpreter_should_multiply_values_when_expression_is_multiplication() {
        // Input: 3*4
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::Integer, TokenValue::Integer(4))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        let result = interpreter.interpret();
        assert_eq!(12, result.unwrap());
    }

    #[test]
    fn interpreter_should_return_error_when_division_by_zero() {
        // Input: 1/0
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(1)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Division)),
                          (TokenType::Integer, TokenValue::Integer(0))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        let result = interpreter.interpret();
        assert!(result.is_err());
    }

    #[test]
    fn interpreter_should_divide_values_when_expression_is_division() {
        // Input: 6/2
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(6)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Division)),
                          (TokenType::Integer, TokenValue::Integer(2))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        let result = interpreter.interpret();
        assert_eq!(3, result.unwrap());
    }

    #[test]
    fn interpreter_should_negate_integer_when_expression_is_unary_minus() {
        // Input: -2
        let tokens = vec![(TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::Integer, TokenValue::Integer(2))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        let result = interpreter.interpret();
        assert_eq!(-2, result.unwrap());
    }

    #[test]
    fn interpreter_should_negate_expression_when_expression_is_prefixed_with_unary_minus() {
        // Input: -(2+3)
        let tokens = vec![(TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::LParen, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(2)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::RParen, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        let result = interpreter.interpret();
        assert_eq!(-5, result.unwrap());
    }

    #[test]
    fn interpreter_should_return_integer_when_expression_is_unary_plus() {
        // Input: +2
        let tokens = vec![(TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(2))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        let result = interpreter.interpret();
        assert_eq!(2, result.unwrap());
    }

    #[test]
    fn interpreter_should_evaluate_chained_unary_operators() {
        // Input: 5 - - - + - 3
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(5)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::Integer, TokenValue::Integer(3))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_ok());
        let interpreter = Interpreter::new(&ast);
        let result = interpreter.interpret();
        assert_eq!(8, result.unwrap());
    }
}
