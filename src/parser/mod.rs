use std::cell::RefCell;
use tokens::{Token, TokenType, OperatorType};
use ast::{Ast, AstIndex, BinaryOperatorNode, UnaryOperatorNode, IntegerNode};
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
    pub fn parse(&self, ast: &mut Ast) -> Result<(), SyntaxError> {
        self.load_first_token()?;

        self.expr(ast)?;

        self.eat(TokenType::Eof)?;

        if ast.is_contiguous() {
            Ok(())
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
    fn expr(&self, ast: &mut Ast) -> Result<AstIndex, SyntaxError> {

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

            // Expect a term on the right hand side
            let rhs = self.term(ast)?;

            // Construct AST node
            let node = BinaryOperatorNode::new(result, rhs, op_type, op);
            result = ast.add_node(node);
        }
    }

    // Evaluates a term:
    // term -> factor ((TIMES | DIVISION) factor)*
    //
    // Precondition: First token has been loaded
    fn term(&self, ast: &mut Ast) -> Result<AstIndex, SyntaxError> {

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

            // Expect a factor on the right hand side
            let rhs = self.factor(ast)?;

            // Construct AST node
            let node = BinaryOperatorNode::new(result, rhs, op_type, op);
            result = ast.add_node(node);
        }
    }

    // Evaluates a factor:
    // factor -> ( PLUS | MINUS) factor | INTEGER | LPAREN expr RPAREN
    //
    // Precondition: First token has been loaded
    fn factor(&self, ast: &mut Ast) -> Result<AstIndex, SyntaxError> {

        // First token should be an INTEGER, PLUS, MINUS or LPAREN
        let current_token = self.get_current_token();

        if current_token.token_type == TokenType::Integer {
            self.eat(TokenType::Integer)?;

            let value = current_token.value.as_ref().unwrap().extract_integer_value();
            let node = IntegerNode::new(value, current_token);

            Ok(ast.add_node(node))
        } else if current_token.token_type == TokenType::Operator {
            // Extract value
            let op_type = current_token.value.as_ref().unwrap().extract_operator_type();
            if op_type == OperatorType::Minus || op_type == OperatorType::Plus {
                self.eat(TokenType::Operator)?;

                // Expect a factor
                let operand = self.factor(ast)?;

                // Construct AST node
                let node = UnaryOperatorNode::new(operand, op_type, current_token);
                Ok(ast.add_node(node))
            } else {
                Err(SyntaxError {
                    msg: format!("Expected '+' or '-', got {}", op_type),
                    position: current_token.position,
                })
            }
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
        let op_index = result.unwrap();
        let node = ast.get_node(op_index);
        assert_eq!(node.get_parent(), None);
        assert_eq!(node.get_value().unwrap(),
                   TokenValue::Operator(OperatorType::Plus));
        let operands = node.get_children();
        let lhs = ast.get_node(operands[0]);
        assert_eq!(lhs.get_parent(), Some(op_index));
        assert_eq!(lhs.get_value().unwrap(), TokenValue::Integer(3));
        let rhs = ast.get_node(operands[1]);
        assert_eq!(rhs.get_parent(), Some(op_index));
        assert_eq!(rhs.get_value().unwrap(), TokenValue::Integer(4));
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
        let op_index = result.unwrap();
        let node = ast.get_node(op_index);
        assert_eq!(node.get_parent(), None);
        assert_eq!(node.get_value().unwrap(),
                   TokenValue::Operator(OperatorType::Minus));
        let operands = node.get_children();
        let lhs = ast.get_node(operands[0]);
        assert_eq!(lhs.get_parent(), Some(op_index));
        assert_eq!(lhs.get_value().unwrap(), TokenValue::Integer(4));
        let rhs = ast.get_node(operands[1]);
        assert_eq!(rhs.get_parent(), Some(op_index));
        assert_eq!(rhs.get_value().unwrap(), TokenValue::Integer(3));
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
    fn parser_expr_should_create_integer_node_if_input_consists_of_only_integer() {
        // Input: 42
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(42))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.expr(&mut ast);
        let node = ast.get_node(result.unwrap());
        assert_eq!(node.get_parent(), None);
        assert_eq!(node.get_value().unwrap(), TokenValue::Integer(42));
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
        let op_index = result.unwrap();
        let node = ast.get_node(op_index);
        assert_eq!(node.get_parent(), None);
        assert_eq!(node.get_value().unwrap(),
                   TokenValue::Operator(OperatorType::Times));
        let operands = node.get_children();
        let lhs = ast.get_node(operands[0]);
        assert_eq!(lhs.get_parent(), Some(op_index));
        assert_eq!(lhs.get_value().unwrap(), TokenValue::Integer(3));
        let rhs = ast.get_node(operands[1]);
        assert_eq!(rhs.get_parent(), Some(op_index));
        assert_eq!(rhs.get_value().unwrap(), TokenValue::Integer(4));
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
        let op_index = result.unwrap();
        let node = ast.get_node(op_index);
        assert_eq!(node.get_parent(), None);
        assert_eq!(node.get_value().unwrap(),
                   TokenValue::Operator(OperatorType::Division));
        let operands = node.get_children();
        let lhs = ast.get_node(operands[0]);
        assert_eq!(lhs.get_parent(), Some(op_index));
        assert_eq!(lhs.get_value().unwrap(), TokenValue::Integer(4));
        let rhs = ast.get_node(operands[1]);
        assert_eq!(rhs.get_parent(), Some(op_index));
        assert_eq!(rhs.get_value().unwrap(), TokenValue::Integer(2));
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
        let node = ast.get_node(result.unwrap());
        assert_eq!(node.get_parent(), None);
        assert_eq!(node.get_value().unwrap(), TokenValue::Integer(42));
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
    fn parser_factor_should_return_integer_node_if_input_consists_of_only_integer() {
        // Input: 42
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(42))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.factor(&mut ast);
        let node = ast.get_node(result.unwrap());
        assert_eq!(node.get_parent(), None);
        assert_eq!(node.get_value().unwrap(), TokenValue::Integer(42));
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
        let op_index = result.unwrap();
        let node = ast.get_node(op_index);
        assert_eq!(node.get_parent(), None);
        assert_eq!(node.get_value().unwrap(),
                   TokenValue::Operator(OperatorType::Plus));
        let operands = node.get_children();
        let lhs = ast.get_node(operands[0]);
        assert_eq!(lhs.get_parent(), Some(op_index));
        assert_eq!(lhs.get_value().unwrap(), TokenValue::Integer(6));
        let rhs = ast.get_node(operands[1]);
        assert_eq!(rhs.get_parent(), Some(op_index));
        assert_eq!(rhs.get_value().unwrap(), TokenValue::Integer(3));
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
        let node = ast.get_node(result.unwrap());
        assert_eq!(node.get_parent(), None);
        assert_eq!(node.get_value().unwrap(), TokenValue::Integer(6));
    }

    #[test]
    fn parser_factor_creates_unary_operator_node_if_input_consists_of_unary_minus() {
        // Input: -5
        let tokens = vec![(TokenType::Operator, TokenValue::Operator(OperatorType::Minus)),
                          (TokenType::Integer, TokenValue::Integer(5))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.factor(&mut ast);
        let op_index = result.unwrap();
        let op_node = ast.get_node(op_index);
        assert_eq!(op_node.get_parent(), None);
        assert_eq!(op_node.get_value().unwrap(),
                   TokenValue::Operator(OperatorType::Minus));
        let operand = op_node.get_children()[0];
        let int_node = ast.get_node(operand);
        assert_eq!(int_node.get_parent(), Some(op_index));
        assert_eq!(int_node.get_value().unwrap(), TokenValue::Integer(5));
    }

    #[test]
    fn parser_factor_creates_unary_operator_node_if_input_consists_of_unary_plus() {
        // Input: +5
        let tokens = vec![(TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(5))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.factor(&mut ast);
        let op_index = result.unwrap();
        let op_node = ast.get_node(op_index);
        assert_eq!(op_node.get_parent(), None);
        assert_eq!(op_node.get_value().unwrap(),
                   TokenValue::Operator(OperatorType::Plus));
        let operand = op_node.get_children()[0];
        let int_node = ast.get_node(operand);
        assert_eq!(int_node.get_parent(), Some(op_index));
        assert_eq!(int_node.get_value().unwrap(), TokenValue::Integer(5));
    }

    #[test]
    fn parser_factor_returns_error_if_input_consists_of_unary_times() {
        // Input: *5
        let tokens = vec![(TokenType::Operator, TokenValue::Operator(OperatorType::Times)),
                          (TokenType::Integer, TokenValue::Integer(5))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.factor(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_factor_returns_error_if_input_consists_of_unary_division() {
        // Input: /5
        let tokens = vec![(TokenType::Operator, TokenValue::Operator(OperatorType::Division)),
                          (TokenType::Integer, TokenValue::Integer(5))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.factor(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_factor_returns_error_if_lparen_is_followed_by_rparen() {
        // Input: ()
        let tokens = vec![(TokenType::LParen, TokenValue::Empty),
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
