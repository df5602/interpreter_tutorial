use std::cell::RefCell;
use std::io;
use std::io::{BufRead, Write};

mod tokens;
mod ast;
mod errors;
mod lexer;

use tokens::{TokenType, OperatorType, Token};
use errors::SyntaxError;
use lexer::{Lexer, PascalLexer};

#[derive(Debug)]
pub struct Interpreter<L> {
    text: String,
    current_token: RefCell<Option<Token>>,
    lexer: L,
}

impl<L: Lexer> Interpreter<L> {
    fn new(text: String, lexer: L) -> Interpreter<L> {
        Interpreter {
            text: text,
            current_token: RefCell::new(None),
            lexer: lexer,
        }
    }

    // Prints error in the following format:
    // Error parsing input: msg
    // >>> 3?5
    // >>>  ^
    fn print_error(&self, e: SyntaxError) {
        let s = std::iter::repeat(" ").take(e.position.0).collect::<String>();
        let m = std::iter::repeat("^").take(e.position.1 - e.position.0).collect::<String>();

        println!("Error parsing input: {}", e.msg);
        println!(">>> {}", self.text);
        println!(">>> {}{}", s, m);
    }

    // Consumes current token if it is of the expected type
    fn eat(&self, token_type: TokenType) -> Result<(), SyntaxError> {
        let mut current_token = self.current_token.borrow_mut();

        // If token has expected type...
        if current_token.as_ref().unwrap().token_type == token_type {
            // ... consume token and set current token to the next token
            if token_type != TokenType::Eof {
                let next_token = self.lexer.get_next_token();
                match next_token {
                    Ok(token) => {
                        *current_token = Some(token);
                        Ok(())
                    }
                    Err(e) => Err(e),
                }
            } else {
                Ok(())
            }
        } else {
            let pos = current_token.as_ref().unwrap().position;
            Err(SyntaxError {
                msg: format!("Expected {}, got {}",
                             token_type,
                             current_token.as_ref().unwrap().token_type),
                position: pos,
            })
        }
    }

    // Loads first token
    fn load_first_token(&self) -> Result<(), SyntaxError> {
        let mut current_token = self.current_token.borrow_mut();
        let next_token = self.lexer.get_next_token();
        if next_token.is_err() {
            Err(next_token.unwrap_err())
        } else {
            *current_token = Some(next_token.unwrap());
            Ok(())
        }
    }

    // Gets a clone of the current token
    // Precondition: First token has been loaded
    fn get_current_token(&self) -> Token {
        self.current_token.borrow().clone().unwrap()
    }

    // Start symbol, loads first token, calls expr() and checks that last token is an EOF
    fn start(&self) -> Result<i64, SyntaxError> {
        self.load_first_token()?;

        let result = self.expr()?;

        self.eat(TokenType::Eof)?;

        Ok(result)
    }

    // Evaluates an expression:
    // expr -> term ((PLUS | MINUS) term)*
    //
    // Precondition: First token has been loaded
    fn expr(&self) -> Result<i64, SyntaxError> {

        // Expect a term on the left hand side
        let mut result = self.term()?;

        loop {
            // Return if next token is not an OPERATOR
            if self.get_current_token().token_type != TokenType::Operator {
                return Ok(result);
            }

            // Otherwise, expect next token to be an operator
            // (Handle the case that the operator is not PLUS or MINUS further down)
            let op = self.get_current_token().value;
            self.eat(TokenType::Operator)?;

            // Extract value
            let op_type = op.unwrap().extract_operator_type();

            // Expect a term on the right hand side
            let rhs = self.term()?;

            // Update result of expression
            result = if op_type == OperatorType::Plus {
                result + rhs
            } else if op_type == OperatorType::Minus {
                result - rhs
            } else {
                return Err(SyntaxError {
                    msg: "Internal Error (Unexpected operator type)".to_string(),
                    position: (self.lexer.get_position(), self.lexer.get_position() + 1),
                });
            }
        }
    }

    // Evaluates a term:
    // term -> factor ((TIMES | DIVISION) factor)*
    //
    // Precondition: First token has been loaded
    fn term(&self) -> Result<i64, SyntaxError> {

        // Expect a factor on the left hand side
        let mut result = self.factor()?;

        loop {
            // Return if next token is EOF
            if self.get_current_token().token_type != TokenType::Operator {
                return Ok(result);
            }

            // Otherwise, expect next token to be an operator TIMES or DIVISION
            let op = self.get_current_token();
            if op.token_type == TokenType::Operator {
                // Extract value
                let op_type = op.value.as_ref().unwrap().extract_operator_type();
                if op_type != OperatorType::Times && op_type != OperatorType::Division {
                    return Ok(result);
                }
            }
            self.eat(TokenType::Operator)?;
            let op_type = op.value.unwrap().extract_operator_type();

            // Expect a factor on the right hand side
            let rhs = self.factor()?;

            // Update result of expression
            result = if op_type == OperatorType::Times {
                result * rhs
            } else if op_type == OperatorType::Division {
                if rhs == 0 {
                    return Err(SyntaxError {
                        msg: "Division by zero".to_string(),
                        position: (self.lexer.get_position(), self.lexer.get_position() + 1),
                    });
                } else {
                    result / rhs
                }
            } else {
                return Err(SyntaxError {
                    msg: "Internal Error (Unexpected operator type)".to_string(),
                    position: (self.lexer.get_position(), self.lexer.get_position() + 1),
                });
            }
        }
    }

    // Evaluates a factor:
    // factor -> INTEGER | LPAREN expr RPAREN
    //
    // Precondition: First token has been loaded
    fn factor(&self) -> Result<i64, SyntaxError> {

        // First token should be an INTEGER or LPAREN
        let current_token = self.get_current_token();

        if current_token.token_type == TokenType::Integer {
            self.eat(TokenType::Integer)?;
            Ok(current_token.value.unwrap().extract_integer_value() as i64)
        } else {
            self.eat(TokenType::LParen)?;

            let result = self.expr()?;

            self.eat(TokenType::RParen)?;

            Ok(result)
        }
    }
}

#[allow(unused_must_use)]
fn print_preamble() {
    let stdout = io::stdout();

    stdout.lock().write(b"interpreter> ");
    stdout.lock().flush();
}

fn main() {
    let stdin = io::stdin();

    print_preamble();
    for line in stdin.lock().lines() {
        match line {
            Ok(_) => {
                let input = line.unwrap();
                let lexer = PascalLexer::new(&input);
                let interpreter = Interpreter::new(input, lexer);
                let result = interpreter.start();
                match result {
                    Ok(value) => println!("{}", value),
                    Err(e) => interpreter.print_error(e),
                }
            }
            Err(error) => {
                println!("error: {}", error);
                panic!();
            }
        }
        print_preamble();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lexer::{Lexer, MockLexer};
    use tokens::*;

    #[test]
    fn interpreter_eat_should_consume_token_if_it_has_the_correct_type() {
        let input = "+4".to_string();
        let tokens = vec![(TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(4))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        *interpreter.current_token.borrow_mut() = Some(interpreter.lexer.get_next_token().unwrap());
        let _op = interpreter.eat(TokenType::Operator);
        let current_token = interpreter.current_token.borrow();
        match *current_token {
            Some(ref token) => assert_eq!(TokenType::Integer, token.token_type),
            None => assert!(false),
        }
    }

    #[test]
    fn interpreter_eat_should_not_consume_token_if_it_has_the_wrong_type() {
        let input = "+4".to_string();
        let tokens = vec![(TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(4))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        *interpreter.current_token.borrow_mut() = Some(interpreter.lexer.get_next_token().unwrap());
        let result = interpreter.eat(TokenType::Integer);
        assert!(result.is_err());
    }

    #[test]
    // expr -> INTEGER OPERATOR INTEGER
    fn interpreter_expr_should_add_values_when_expression_is_addition() {
        let input = "3+4".to_string();
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(4))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.expr();
        assert_eq!(7, result.unwrap());
    }

    #[test]
    // expr -> INTEGER OPERATOR INTEGER
    fn interpreter_expr_should_subtract_values_when_expression_is_subtraction() {
        let input = "4-3".to_string();
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(4)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::Integer, TokenValue::Integer(3))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.expr();
        assert_eq!(1, result.unwrap());
    }

    #[test]
    fn interpreter_expr_should_return_negative_number_when_result_of_subtraction_is_negative() {
        let input = "3-4".to_string();
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::Integer, TokenValue::Integer(4))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.expr();
        assert_eq!(-1, result.unwrap() as i64);
    }

    #[test]
    fn interpreter_expr_should_not_parse_expressions_that_dont_begin_with_an_integer() {
        let input = "+4".to_string();
        let tokens = vec![(TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(4))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.expr();
        assert!(result.is_err());
    }

    #[test]
    fn interpreter_expr_should_not_parse_expressions_that_dont_have_integer_after_operator() {
        let input = "4+-".to_string();
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(4)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.expr();
        assert!(result.is_err());
    }

    #[test]
    fn interpreter_expr_should_not_parse_empty_string() {
        let input = "".to_string();
        let tokens = vec![];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.expr();
        assert!(result.is_err());
    }

    #[test]
    fn interpreter_expr_should_not_parse_expressions_that_dont_terminate_with_eof() {
        let input = "1+3/".to_string();
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(1)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Division))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.expr();
        assert!(result.is_err());
    }

    #[test]
    fn interpreter_load_first_token_should_load_first_token() {
        let input = "2+3".to_string();
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(2)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(3))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        let _ = interpreter.load_first_token();
        assert_eq!(TokenType::Integer,
                   interpreter.current_token.borrow().clone().unwrap().token_type);
        let val = interpreter.current_token.borrow().clone().unwrap().value.unwrap();
        match val {
            TokenValue::Integer(val) => assert_eq!(2, val),
            _ => panic!(),
        }
    }

    #[test]
    fn interpreter_expr_should_return_integer_value_if_input_consists_of_only_integer() {
        let input = "42".to_string();
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(42))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.expr();
        assert_eq!(42, result.unwrap());
    }

    #[test]
    fn interpreter_expr_should_interpret_chained_expressions() {
        let input = "1+3+5".to_string();
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(1)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(5))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.expr();
        assert_eq!(9, result.unwrap());
    }

    #[test]
    fn interpreter_expr_should_evaluate_chained_expressions_from_left_to_right() {
        let input = "1-2+3".to_string();
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(1)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::Integer, TokenValue::Integer(2)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(3))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.expr();
        assert_eq!(2, result.unwrap());
    }

    #[test]
    fn interpreter_term_should_multiply_values_when_expression_is_multiplication() {
        let input = "3*4".to_string();
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::Integer, TokenValue::Integer(4))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.term();
        assert_eq!(12, result.unwrap());
    }

    #[test]
    fn interpreter_term_should_divide_values_when_expression_is_division() {
        let input = "4/2".to_string();
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(4)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Division)),
                          (TokenType::Integer, TokenValue::Integer(2))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.term();
        assert_eq!(2, result.unwrap());
    }

    #[test]
    fn interpreter_term_should_return_error_when_division_by_zero() {
        let input = "1/0".to_string();
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(1)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Division)),
                          (TokenType::Integer, TokenValue::Integer(0))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.term();
        assert!(result.is_err());
    }

    #[test]
    fn interpreter_term_should_return_integer_value_if_input_consists_of_only_integer() {
        let input = "42".to_string();
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(42))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.term();
        assert_eq!(42, result.unwrap());
    }

    #[test]
    fn interpreter_term_should_not_parse_expressions_that_dont_begin_with_an_integer() {
        let input = "+4".to_string();
        let tokens = vec![(TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(4))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.term();
        assert!(result.is_err());
    }

    #[test]
    fn interpreter_term_should_not_parse_expressions_that_dont_have_integer_after_operator() {
        let input = "4*/".to_string();
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(4)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Division))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.term();
        assert!(result.is_err());
    }

    #[test]
    fn interpreter_term_should_not_parse_empty_string() {
        let input = "".to_string();
        let tokens = vec![];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.term();
        assert!(result.is_err());
    }

    #[test]
    fn interpreter_term_should_not_parse_expressions_that_dont_terminate_with_eof() {
        let input = "1*3/".to_string();
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(1)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Division))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.term();
        assert!(result.is_err());
    }

    #[test]
    fn interpreter_term_should_interpret_chained_expressions() {
        let input = "1*3*5".to_string();
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(1)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::Integer, TokenValue::Integer(5))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.term();
        assert_eq!(15, result.unwrap());
    }

    #[test]
    fn interpreter_term_should_evaluate_chained_expressions_from_left_to_right() {
        let input = "6/2*3".to_string();
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(6)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Division)),
                          (TokenType::Integer, TokenValue::Integer(2)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::Integer, TokenValue::Integer(3))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.term();
        assert_eq!(9, result.unwrap());
    }

    #[test]
    fn interpreter_expr_should_give_precedence_to_multiplication_and_division() {
        let input = "14+2*3-6/2".to_string();
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
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.expr();
        assert_eq!(17, result.unwrap());
    }

    #[test]
    fn interpreter_factor_should_return_integer_value_if_input_consists_of_only_integer() {
        let input = "42".to_string();
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(42))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.factor();
        assert_eq!(42, result.unwrap());
    }

    #[test]
    fn interpreter_factor_returns_result_of_expr_if_input_consists_of_expr_in_parentheses() {
        let input = "(6+3)".to_string();
        let tokens = vec![(TokenType::LParen, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(6)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::RParen, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.factor();
        assert_eq!(9, result.unwrap());
    }

    #[test]
    fn interpreter_factor_returns_integer_if_input_consists_of_integer_in_parentheses() {
        let input = "(6)".to_string();
        let tokens = vec![(TokenType::LParen, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(6)),
                          (TokenType::RParen, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.factor();
        assert_eq!(6, result.unwrap());
    }

    #[test]
    fn interpreter_factor_returns_error_if_lparen_is_followed_by_operator() {
        let input = "(+3)".to_string();
        let tokens = vec![(TokenType::LParen, TokenValue::Empty),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::RParen, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.factor();
        assert!(result.is_err());
    }

    #[test]
    fn interpreter_factor_returns_error_if_operator_is_followed_by_rparen() {
        let input = "(6+)".to_string();
        let tokens = vec![(TokenType::LParen, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(6)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::RParen, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.factor();
        assert!(result.is_err());
    }

    #[test]
    fn interpreter_factor_returns_error_if_parentheses_are_mismatched() {
        let input = "(6+3".to_string();
        let tokens = vec![(TokenType::LParen, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(6)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(3))];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.factor();
        assert!(result.is_err());
    }

    #[test]
    fn interpreter_expr_can_evaluate_nested_expressions() {
        let input = "7+3*(10/(12/(3+1)-1))".to_string();
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
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.expr();
        assert_eq!(22, result.unwrap());
    }

    #[test]
    fn interpreter_start_returns_error_if_parentheses_are_mismatched() {
        let input = "(6+3))".to_string();
        let tokens = vec![(TokenType::LParen, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(6)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::RParen, TokenValue::Empty),
                          (TokenType::RParen, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let interpreter = Interpreter::new(input, lexer);
        let result = interpreter.start();
        assert!(result.is_err());
    }
}

#[cfg(test)]
mod integration_tests {
    use super::*;
    use lexer::PascalLexer;

    #[test]
    fn interpreter_expr_should_parse_expressions_that_contain_multi_digit_integer() {
        let input = "44+3".to_string();
        let lexer = PascalLexer::new(&input);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.expr();
        assert_eq!(47, result.unwrap());
    }

    #[test]
    fn interpreter_expr_should_parse_expressions_that_contain_whitespace_characters() {
        let input = "2 + 3".to_string();
        let lexer = PascalLexer::new(&input);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.expr();
        assert_eq!(5, result.unwrap());
    }

    #[test]
    fn interpreter_expr_should_parse_expressions_that_begin_with_whitespace_characters() {
        let input = " 2 + 3".to_string();
        let lexer = PascalLexer::new(&input);
        let interpreter = Interpreter::new(input, lexer);
        assert!(interpreter.load_first_token().is_ok());
        let result = interpreter.expr();
        assert_eq!(5, result.unwrap());
    }
}
