use std::cell::RefCell;
use tokens::{Token, TokenType, OperatorType};
use ast::{Ast, AstIndex, OperatorNode, IntegerNode};
use errors::SyntaxError;
use lexer::Lexer;

pub struct Parser<L> {
    current_token: RefCell<Option<Token>>,
    lexer: L,
}

impl<L: Lexer> Parser<L> {
    pub fn new(lexer: L) -> Parser<L> {
        Parser {
            current_token: RefCell::new(None),
            lexer: lexer,
        }
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

    // Start parsing: load first token, call expr() and checks that last token is an EOF
    // As a sanity check, the generated AST is checked for contiguity
    pub fn parse(&self, ast: &mut Ast) -> Result<i64, SyntaxError> {
        self.load_first_token()?;

        let result = self.expr(ast)?;

        self.eat(TokenType::Eof)?;

        if ast.is_contiguous() {
            Ok((result.0))
        } else {
            Err(SyntaxError {
                msg: "Internal Error (AST is not contiguous)".to_string(),
                position: (0, 0),
            })
        }
    }

    // Evaluates an expression:
    // expr -> term ((PLUS | MINUS) term)*
    //
    // Precondition: First token has been loaded
    fn expr(&self, ast: &mut Ast) -> Result<(i64, AstIndex), SyntaxError> {

        // Expect a term on the left hand side
        let mut result = self.term(ast)?;

        loop {
            // Return if next token is not an OPERATOR
            if self.get_current_token().token_type != TokenType::Operator {
                return Ok(result);
            }

            // Otherwise, expect next token to be an operator
            // (Handle the case that the operator is not PLUS or MINUS further down)
            let op = self.get_current_token();
            self.eat(TokenType::Operator)?;

            // Extract value
            let op_type = op.value.as_ref().unwrap().extract_operator_type();
            let op_type_2 = op_type.clone();   // Temporary hack to guarantee it is cleaned up
                                               // when modifications are complete

            // Expect a term on the right hand side
            let rhs = self.term(ast)?;

            // Construct AST node
            let node = OperatorNode::new(result.1, rhs.1, op_type, op);
            result.1 = ast.add_node(node);

            // Update result of expression
            result.0 = if op_type_2 == OperatorType::Plus {
                result.0 + rhs.0
            } else if op_type_2 == OperatorType::Minus {
                result.0 - rhs.0
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
    fn term(&self, ast: &mut Ast) -> Result<(i64, AstIndex), SyntaxError> {

        // Expect a factor on the left hand side
        let mut result = self.factor(ast)?;

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
            let op_type = op.value.as_ref().unwrap().extract_operator_type();
            let op_type_2 = op_type.clone();   // Temporary hack to guarantee it is cleaned up
                                               // when modifications are complete

            // Expect a factor on the right hand side
            let rhs = self.factor(ast)?;

            // Construct AST node
            let node = OperatorNode::new(result.1, rhs.1, op_type, op);
            result.1 = ast.add_node(node);

            // Update result of expression
            result.0 = if op_type_2 == OperatorType::Times {
                result.0 * rhs.0
            } else if op_type_2 == OperatorType::Division {
                if rhs.0 == 0 {
                    return Err(SyntaxError {
                        msg: "Division by zero".to_string(),
                        position: (self.lexer.get_position(), self.lexer.get_position() + 1),
                    });
                } else {
                    result.0 / rhs.0
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
    fn factor(&self, ast: &mut Ast) -> Result<(i64, AstIndex), SyntaxError> {

        // First token should be an INTEGER or LPAREN
        let current_token = self.get_current_token();

        if current_token.token_type == TokenType::Integer {
            self.eat(TokenType::Integer)?;
            let value = current_token.value.as_ref().unwrap().extract_integer_value();
            let node = IntegerNode::new(value, current_token);
            Ok((value as i64, ast.add_node(node)))
        } else {
            self.eat(TokenType::LParen)?;

            let result = self.expr(ast)?;

            self.eat(TokenType::RParen)?;

            Ok(result)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokens::*;
    use ast::Ast;
    use lexer::{Lexer, MockLexer};

    #[test]
    fn parser_eat_should_consume_token_if_it_has_the_correct_type() {
        // Input: +4
        let tokens = vec![(TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(4))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        *parser.current_token.borrow_mut() = Some(parser.lexer.get_next_token().unwrap());
        let _op = parser.eat(TokenType::Operator);
        let current_token = parser.current_token.borrow();
        match *current_token {
            Some(ref token) => assert_eq!(TokenType::Integer, token.token_type),
            None => assert!(false),
        }
    }

    #[test]
    fn parser_eat_should_not_consume_token_if_it_has_the_wrong_type() {
        // Input: +4
        let tokens = vec![(TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(4))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        *parser.current_token.borrow_mut() = Some(parser.lexer.get_next_token().unwrap());
        let result = parser.eat(TokenType::Integer);
        assert!(result.is_err());
    }

    #[test]
    // expr -> INTEGER OPERATOR INTEGER
    fn parser_expr_should_add_values_when_expression_is_addition() {
        // Input: 3+4
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(4))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.expr(&mut ast);
        assert_eq!(7, result.unwrap().0);
    }

    #[test]
    // expr -> INTEGER OPERATOR INTEGER
    fn parser_expr_should_create_operator_node_when_expression_is_addition() {
        // Input: 3+4
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(4))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.expr(&mut ast);
        let op_index = result.unwrap().1;
        let node = ast.get_node(op_index);
        assert_eq!(node.get_parent(), None);
        assert_eq!(node.get_value(), TokenValue::Operator(OperatorType::Plus));
        let operands = node.get_children();
        let lhs = ast.get_node(operands[0]);
        assert_eq!(lhs.get_parent(), Some(op_index));
        assert_eq!(lhs.get_value(), TokenValue::Integer(3));
        let rhs = ast.get_node(operands[1]);
        assert_eq!(rhs.get_parent(), Some(op_index));
        assert_eq!(rhs.get_value(), TokenValue::Integer(4));
    }

    #[test]
    // expr -> INTEGER OPERATOR INTEGER
    fn parser_expr_should_subtract_values_when_expression_is_subtraction() {
        // Input: 4-3
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(4)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::Integer, TokenValue::Integer(3))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.expr(&mut ast);
        assert_eq!(1, result.unwrap().0);
    }

    #[test]
    // expr -> INTEGER OPERATOR INTEGER
    fn parser_expr_should_create_operator_node_when_expression_is_subtraction() {
        // Input: 4-3
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(4)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::Integer, TokenValue::Integer(3))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.expr(&mut ast);
        let op_index = result.unwrap().1;
        let node = ast.get_node(op_index);
        assert_eq!(node.get_parent(), None);
        assert_eq!(node.get_value(), TokenValue::Operator(OperatorType::Minus));
        let operands = node.get_children();
        let lhs = ast.get_node(operands[0]);
        assert_eq!(lhs.get_parent(), Some(op_index));
        assert_eq!(lhs.get_value(), TokenValue::Integer(4));
        let rhs = ast.get_node(operands[1]);
        assert_eq!(rhs.get_parent(), Some(op_index));
        assert_eq!(rhs.get_value(), TokenValue::Integer(3));
    }

    #[test]
    fn parser_expr_should_return_negative_number_when_result_of_subtraction_is_negative() {
        // Input: 3-4
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::Integer, TokenValue::Integer(4))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.expr(&mut ast);
        assert_eq!(-1, result.unwrap().0 as i64);
    }

    #[test]
    fn parser_expr_should_not_parse_expressions_that_dont_begin_with_an_integer() {
        // Input: +4
        let tokens = vec![(TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(4))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.expr(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_expr_should_not_parse_expressions_that_dont_have_integer_after_operator() {
        // Input: 4+-
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(4)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.expr(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_expr_should_not_parse_empty_string() {
        // Input: (Empty string)
        let tokens = vec![];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.expr(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_expr_should_not_parse_expressions_that_dont_terminate_with_eof() {
        // Input: 1+3/
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(1)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Division))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.expr(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_load_first_token_should_load_first_token() {
        // Input: 2+3
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(2)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(3))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let _ = parser.load_first_token();
        assert_eq!(TokenType::Integer,
                   parser.current_token.borrow().clone().unwrap().token_type);
        let val = parser.current_token.borrow().clone().unwrap().value.unwrap();
        match val {
            TokenValue::Integer(val) => assert_eq!(2, val),
            _ => panic!(),
        }
    }

    #[test]
    fn parser_expr_should_return_integer_value_if_input_consists_of_only_integer() {
        // Input: 42
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(42))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.expr(&mut ast);
        assert_eq!(42, result.unwrap().0);
    }

    #[test]
    fn parser_expr_should_create_integer_node_if_input_consists_of_only_integer() {
        // Input: 42
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(42))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.expr(&mut ast);
        let node = ast.get_node(result.unwrap().1);
        assert_eq!(node.get_parent(), None);
        assert_eq!(node.get_value(), TokenValue::Integer(42));
    }

    #[test]
    fn parser_expr_should_interpret_chained_expressions() {
        // Input: 1+3+5
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(1)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(5))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.expr(&mut ast);
        assert_eq!(9, result.unwrap().0);
    }

    #[test]
    fn parser_expr_should_evaluate_chained_expressions_from_left_to_right() {
        // Input: 1-2+3
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(1)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::Integer, TokenValue::Integer(2)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(3))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.expr(&mut ast);
        assert_eq!(2, result.unwrap().0);
    }

    #[test]
    fn parser_term_should_multiply_values_when_expression_is_multiplication() {
        // Input: 3*4
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::Integer, TokenValue::Integer(4))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.term(&mut ast);
        assert_eq!(12, result.unwrap().0);
    }

    #[test]
    fn parser_term_should_create_operator_node_when_expression_is_multiplication() {
        // Input: 3*4
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::Integer, TokenValue::Integer(4))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.term(&mut ast);
        let op_index = result.unwrap().1;
        let node = ast.get_node(op_index);
        assert_eq!(node.get_parent(), None);
        assert_eq!(node.get_value(), TokenValue::Operator(OperatorType::Times));
        let operands = node.get_children();
        let lhs = ast.get_node(operands[0]);
        assert_eq!(lhs.get_parent(), Some(op_index));
        assert_eq!(lhs.get_value(), TokenValue::Integer(3));
        let rhs = ast.get_node(operands[1]);
        assert_eq!(rhs.get_parent(), Some(op_index));
        assert_eq!(rhs.get_value(), TokenValue::Integer(4));
    }

    #[test]
    fn parser_term_should_divide_values_when_expression_is_division() {
        // Input: 4/2
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(4)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Division)),
                          (TokenType::Integer, TokenValue::Integer(2))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.term(&mut ast);
        assert_eq!(2, result.unwrap().0);
    }

    #[test]
    fn parser_term_should_create_operator_node_when_expression_is_division() {
        // Input: 4/2
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(4)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Division)),
                          (TokenType::Integer, TokenValue::Integer(2))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.term(&mut ast);
        let op_index = result.unwrap().1;
        let node = ast.get_node(op_index);
        assert_eq!(node.get_parent(), None);
        assert_eq!(node.get_value(),
                   TokenValue::Operator(OperatorType::Division));
        let operands = node.get_children();
        let lhs = ast.get_node(operands[0]);
        assert_eq!(lhs.get_parent(), Some(op_index));
        assert_eq!(lhs.get_value(), TokenValue::Integer(4));
        let rhs = ast.get_node(operands[1]);
        assert_eq!(rhs.get_parent(), Some(op_index));
        assert_eq!(rhs.get_value(), TokenValue::Integer(2));
    }

    #[test]
    fn parser_term_should_return_error_when_division_by_zero() {
        // Input: 1/0
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(1)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Division)),
                          (TokenType::Integer, TokenValue::Integer(0))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.term(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_term_should_return_integer_value_if_input_consists_of_only_integer() {
        // Input: 42
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(42))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.term(&mut ast);
        assert_eq!(42, result.unwrap().0);
    }

    #[test]
    fn parser_term_should_return_integer_node_if_input_consists_of_only_integer() {
        // Input: 42
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(42))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.term(&mut ast);
        let node = ast.get_node(result.unwrap().1);
        assert_eq!(node.get_parent(), None);
        assert_eq!(node.get_value(), TokenValue::Integer(42));
    }

    #[test]
    fn parser_term_should_not_parse_expressions_that_dont_begin_with_an_integer() {
        // Input: +4
        let tokens = vec![(TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(4))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.term(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_term_should_not_parse_expressions_that_dont_have_integer_after_operator() {
        // Input: 4*/
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(4)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Division))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.term(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_term_should_not_parse_empty_string() {
        // Input: (Empty string)
        let tokens = vec![];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.term(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_term_should_not_parse_expressions_that_dont_terminate_with_eof() {
        // Input: 1*3/
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(1)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Division))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.term(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_term_should_interpret_chained_expressions() {
        // Input: 1*3*5
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(1)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::Integer, TokenValue::Integer(5))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.term(&mut ast);
        assert_eq!(15, result.unwrap().0);
    }

    #[test]
    fn parser_term_should_evaluate_chained_expressions_from_left_to_right() {
        // Input: 6/2*3
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(6)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Division)),
                          (TokenType::Integer, TokenValue::Integer(2)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::Integer, TokenValue::Integer(3))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.term(&mut ast);
        assert_eq!(9, result.unwrap().0);
    }

    #[test]
    fn parser_expr_should_give_precedence_to_multiplication_and_division() {
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
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.expr(&mut ast);
        assert_eq!(17, result.unwrap().0);
    }

    #[test]
    fn parser_factor_should_return_integer_value_if_input_consists_of_only_integer() {
        // Input: 42
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(42))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.factor(&mut ast);
        assert_eq!(42, result.unwrap().0);
    }

    #[test]
    fn parser_factor_should_return_integer_node_if_input_consists_of_only_integer() {
        // Input: 42
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(42))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.factor(&mut ast);
        let node = ast.get_node(result.unwrap().1);
        assert_eq!(node.get_parent(), None);
        assert_eq!(node.get_value(), TokenValue::Integer(42));
    }

    #[test]
    fn parser_factor_returns_result_of_expr_if_input_consists_of_expr_in_parentheses() {
        // Input: (6+3)
        let tokens = vec![(TokenType::LParen, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(6)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::RParen, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.factor(&mut ast);
        assert_eq!(9, result.unwrap().0);
    }

    #[test]
    fn parser_factor_creates_graph_of_expr_if_input_consists_of_expr_in_parentheses() {
        // Input: (6+3)
        let tokens = vec![(TokenType::LParen, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(6)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::RParen, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.factor(&mut ast);
        let op_index = result.unwrap().1;
        let node = ast.get_node(op_index);
        assert_eq!(node.get_parent(), None);
        assert_eq!(node.get_value(), TokenValue::Operator(OperatorType::Plus));
        let operands = node.get_children();
        let lhs = ast.get_node(operands[0]);
        assert_eq!(lhs.get_parent(), Some(op_index));
        assert_eq!(lhs.get_value(), TokenValue::Integer(6));
        let rhs = ast.get_node(operands[1]);
        assert_eq!(rhs.get_parent(), Some(op_index));
        assert_eq!(rhs.get_value(), TokenValue::Integer(3));
    }

    #[test]
    fn parser_factor_returns_integer_if_input_consists_of_integer_in_parentheses() {
        // Input: (6)
        let tokens = vec![(TokenType::LParen, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(6)),
                          (TokenType::RParen, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.factor(&mut ast);
        assert_eq!(6, result.unwrap().0);
    }

    #[test]
    fn parser_factor_creates_integer_node_if_input_consists_of_integer_in_parentheses() {
        // Input: (6)
        let tokens = vec![(TokenType::LParen, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(6)),
                          (TokenType::RParen, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.factor(&mut ast);
        let node = ast.get_node(result.unwrap().1);
        assert_eq!(node.get_parent(), None);
        assert_eq!(node.get_value(), TokenValue::Integer(6));
    }

    #[test]
    fn parser_factor_returns_error_if_lparen_is_followed_by_operator() {
        // Input: (+3)
        let tokens = vec![(TokenType::LParen, TokenValue::Empty),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::RParen, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.factor(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_factor_returns_error_if_operator_is_followed_by_rparen() {
        // Input: (6+)
        let tokens = vec![(TokenType::LParen, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(6)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::RParen, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.factor(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_factor_returns_error_if_parentheses_are_mismatched() {
        // Input: (6+3
        let tokens = vec![(TokenType::LParen, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(6)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(3))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.factor(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_expr_can_evaluate_nested_expressions() {
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
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.expr(&mut ast);
        assert_eq!(22, result.unwrap().0);
    }

    #[test]
    fn parser_start_returns_error_if_parentheses_are_mismatched() {
        // Input: (6+3))
        let tokens = vec![(TokenType::LParen, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(6)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(3)),
                          (TokenType::RParen, TokenValue::Empty),
                          (TokenType::RParen, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        let result = parser.parse(&mut ast);
        assert!(result.is_err());
    }
}
