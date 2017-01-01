use std::cell::RefCell;
use tokens::{Token, TokenType, OperatorType};
use ast::{Ast, AstIndex, BinaryOperatorNode, UnaryOperatorNode, IntegerNode, VariableNode,
          AssignmentStmtNode, CompoundStmtNode};
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

        self.compound_statement(ast)?;

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

    /// Evaluates a compound statement:
    /// compound_statement -> BEGIN statement_list END
    fn compound_statement(&self, ast: &mut Ast) -> Result<AstIndex, SyntaxError> {
        // Expect BEGIN keyword
        let begin = self.get_current_token();
        self.eat(TokenType::Begin)?;

        // Expect list of statements
        let statements = self.statement_list(ast)?;

        // Expect END keyword
        let end = self.get_current_token();
        self.eat(TokenType::End)?;

        // Construct AST node
        let node = CompoundStmtNode::new(statements, begin, end);
        Ok(ast.add_node(node))
    }

    /// Evaluates a statement list:
    /// statement_list -> statement (SEMICOLON statement)*
    fn statement_list(&self, ast: &mut Ast) -> Result<Vec<AstIndex>, SyntaxError> {
        let mut statements = Vec::new();

        // Parse first statement
        if let Some(index) = self.statement(ast)? {
            statements.push(index);
        }

        loop {
            // Return if first statement is not followed by semicolon
            if self.get_current_token().token_type != TokenType::Semicolon {
                return Ok(statements);
            }

            // Otherwise, expect next token to be a semicolon
            self.eat(TokenType::Semicolon)?;

            // Parse next statement
            if let Some(index) = self.statement(ast)? {
                statements.push(index);
            }
        }
    }

    /// Evaluates a statement:
    /// statement -> (compound_statement | assignment_statement)?
    fn statement(&self, ast: &mut Ast) -> Result<Option<AstIndex>, SyntaxError> {
        match self.get_current_token().token_type {
            TokenType::Begin => Ok(Some(self.compound_statement(ast)?)),
            TokenType::Identifier => Ok(Some(self.assignment_statement(ast)?)),
            _ => Ok(None),
        }
    }

    /// Evaluates an assignment statement:
    /// assignment_statement -> variable ASSIGN expr
    fn assignment_statement(&self, ast: &mut Ast) -> Result<AstIndex, SyntaxError> {
        let variable = self.variable(ast)?;

        let assign_token = self.get_current_token();
        self.eat(TokenType::Assign)?;

        let expression = self.expr(ast)?;

        // Construct AST node
        let node = AssignmentStmtNode::new(variable, expression, assign_token);
        Ok(ast.add_node(node))
    }

    /// Creates a variable node
    fn variable(&self, ast: &mut Ast) -> Result<AstIndex, SyntaxError> {
        let variable = self.get_current_token();
        self.eat(TokenType::Identifier)?;

        // Extract name
        let name = variable.value.as_ref().unwrap().extract_identifier_value();

        // Construct AST node
        let node = VariableNode::new(name, variable);
        Ok(ast.add_node(node))
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

    #[test]
    fn parser_variable_creates_variable_node_when_token_is_identifier() {
        // Input: a
        let tokens = vec![(TokenType::Identifier, TokenValue::Identifier("a".to_string()))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let var_index = parser.variable(&mut ast).unwrap();
        let var_node = ast.get_node(var_index);
        assert_eq!(var_node.get_parent(), None);
        assert_eq!(var_node.get_value().unwrap(),
                   TokenValue::Identifier("a".to_string()));
    }

    #[test]
    fn parser_variable_returns_error_when_token_is_no_identifier() {
        // Input: 5
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(5))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.variable(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_assignment_statement_parses_assignment_statement() {
        // Input: a := 5
        let tokens = vec![(TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(5))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let assign_index = parser.assignment_statement(&mut ast).unwrap();
        let assign_node = ast.get_node(assign_index);
        assert_eq!(assign_node.get_parent(), None);
        let children = assign_node.get_children();
        let var_node = ast.get_node(children[0]);
        assert_eq!(var_node.get_parent(), Some(assign_index));
        assert_eq!(var_node.get_value().unwrap(),
                   TokenValue::Identifier("a".to_string()));
        let expr_node = ast.get_node(children[1]);
        assert_eq!(expr_node.get_parent(), Some(assign_index));
        assert_eq!(expr_node.get_value().unwrap(), TokenValue::Integer(5));
    }

    #[test]
    fn parser_assignment_statement_parses_assignment_statement_with_expression() {
        // Input: a := 5 + 7
        let tokens = vec![(TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(5)),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(7))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let assign_index = parser.assignment_statement(&mut ast).unwrap();
        let assign_node = ast.get_node(assign_index);
        assert_eq!(assign_node.get_parent(), None);
        let children = assign_node.get_children();
        let var_node = ast.get_node(children[0]);
        assert_eq!(var_node.get_parent(), Some(assign_index));
        assert_eq!(var_node.get_value().unwrap(),
                   TokenValue::Identifier("a".to_string()));
        let expr_node = ast.get_node(children[1]);
        assert_eq!(expr_node.get_parent(), Some(assign_index));
        assert_eq!(expr_node.get_value().unwrap(),
                   TokenValue::Operator(OperatorType::Plus));
    }

    #[test]
    fn parser_assignment_statement_doesnt_parse_assignment_without_variable_on_the_left() {
        // Input: 1 := 5
        let tokens = vec![(TokenType::Integer, TokenValue::Integer(1)),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(5))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        assert!(parser.assignment_statement(&mut ast).is_err());
    }

    #[test]
    fn parser_assignment_statement_doesnt_parse_assignment_without_assign_token_in_the_middle() {
        // Input: a + 5
        let tokens = vec![(TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Operator, TokenValue::Operator(OperatorType::Plus)),
                          (TokenType::Integer, TokenValue::Integer(5))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        assert!(parser.assignment_statement(&mut ast).is_err());
    }

    #[test]
    fn parser_assignment_statement_doesnt_parse_assignment_without_expression_on_the_right() {
        // Input: a := BEGIN
        let tokens = vec![(TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Begin, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        assert!(parser.assignment_statement(&mut ast).is_err());
    }

    #[test]
    fn parser_statement_returns_assignment_statement_if_statement_is_assignment_statement() {
        // Input: a := 5
        let tokens = vec![(TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(5))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let stmt_index = parser.statement(&mut ast).unwrap().unwrap();
        let stmt_node = ast.get_node(stmt_index);
        assert_eq!(stmt_node.get_parent(), None);
        let children = stmt_node.get_children();
        let var_node = ast.get_node(children[0]);
        assert_eq!(var_node.get_parent(), Some(stmt_index));
        assert_eq!(var_node.get_value().unwrap(),
                   TokenValue::Identifier("a".to_string()));
        let expr_node = ast.get_node(children[1]);
        assert_eq!(expr_node.get_parent(), Some(stmt_index));
        assert_eq!(expr_node.get_value().unwrap(), TokenValue::Integer(5));
    }

    #[test]
    fn parser_statement_returns_none_if_no_statement_is_present() {
        // Input: END
        let tokens = vec![(TokenType::End, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let result = parser.statement(&mut ast).unwrap();
        assert_eq!(result, None);
    }

    #[test]
    fn parser_statement_list_returns_assignment_statement_if_statement_is_assignment() {
        // Input: a := 5
        let tokens = vec![(TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(5))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let statement_list = parser.statement_list(&mut ast).unwrap();
        assert_eq!(statement_list.len(), 1);

        let stmt_index = statement_list[0];
        let stmt_node = ast.get_node(stmt_index);
        assert_eq!(stmt_node.get_parent(), None);
        let children = stmt_node.get_children();
        let var_node = ast.get_node(children[0]);
        assert_eq!(var_node.get_parent(), Some(stmt_index));
        assert_eq!(var_node.get_value().unwrap(),
                   TokenValue::Identifier("a".to_string()));
        let expr_node = ast.get_node(children[1]);
        assert_eq!(expr_node.get_parent(), Some(stmt_index));
        assert_eq!(expr_node.get_value().unwrap(), TokenValue::Integer(5));
    }

    #[test]
    fn parser_statement_list_returns_two_statements_when_statements_are_separated_by_semicolon() {
        // Input: a := 5; b := 6
        let tokens = vec![(TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(5)),
                          (TokenType::Semicolon, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("b".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(6))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let statement_list = parser.statement_list(&mut ast).unwrap();
        assert_eq!(statement_list.len(), 2);

        let mut stmt_index = statement_list[0];
        let mut stmt_node = ast.get_node(stmt_index);
        assert_eq!(stmt_node.get_parent(), None);
        let mut children = stmt_node.get_children();
        let mut var_node = ast.get_node(children[0]);
        assert_eq!(var_node.get_parent(), Some(stmt_index));
        assert_eq!(var_node.get_value().unwrap(),
                   TokenValue::Identifier("a".to_string()));
        let mut expr_node = ast.get_node(children[1]);
        assert_eq!(expr_node.get_parent(), Some(stmt_index));
        assert_eq!(expr_node.get_value().unwrap(), TokenValue::Integer(5));

        stmt_index = statement_list[1];
        stmt_node = ast.get_node(stmt_index);
        assert_eq!(stmt_node.get_parent(), None);
        children = stmt_node.get_children();
        var_node = ast.get_node(children[0]);
        assert_eq!(var_node.get_parent(), Some(stmt_index));
        assert_eq!(var_node.get_value().unwrap(),
                   TokenValue::Identifier("b".to_string()));
        expr_node = ast.get_node(children[1]);
        assert_eq!(expr_node.get_parent(), Some(stmt_index));
        assert_eq!(expr_node.get_value().unwrap(), TokenValue::Integer(6));
    }

    #[test]
    fn parser_statement_list_returns_only_first_stmt_when_stmts_are_not_separated_by_semicolon() {
        // Input: a := 5 b := 6
        let tokens = vec![(TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(5)),
                          (TokenType::Identifier, TokenValue::Identifier("b".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(6))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let statement_list = parser.statement_list(&mut ast).unwrap();
        assert_eq!(statement_list.len(), 1);

        let stmt_index = statement_list[0];
        let stmt_node = ast.get_node(stmt_index);
        assert_eq!(stmt_node.get_parent(), None);
        let children = stmt_node.get_children();
        let var_node = ast.get_node(children[0]);
        assert_eq!(var_node.get_parent(), Some(stmt_index));
        assert_eq!(var_node.get_value().unwrap(),
                   TokenValue::Identifier("a".to_string()));
        let expr_node = ast.get_node(children[1]);
        assert_eq!(expr_node.get_parent(), Some(stmt_index));
        assert_eq!(expr_node.get_value().unwrap(), TokenValue::Integer(5));
    }

    #[test]
    fn parser_statement_list_can_begin_with_semicolon() {
        // Input: ;b := 6
        let tokens = vec![(TokenType::Semicolon, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("b".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(6))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let statement_list = parser.statement_list(&mut ast).unwrap();
        assert_eq!(statement_list.len(), 1);

        let stmt_index = statement_list[0];
        let stmt_node = ast.get_node(stmt_index);
        assert_eq!(stmt_node.get_parent(), None);
        let children = stmt_node.get_children();
        let var_node = ast.get_node(children[0]);
        assert_eq!(var_node.get_parent(), Some(stmt_index));
        assert_eq!(var_node.get_value().unwrap(),
                   TokenValue::Identifier("b".to_string()));
        let expr_node = ast.get_node(children[1]);
        assert_eq!(expr_node.get_parent(), Some(stmt_index));
        assert_eq!(expr_node.get_value().unwrap(), TokenValue::Integer(6));
    }

    #[test]
    fn parser_statement_list_can_end_with_semicolon() {
        // Input: b := 6;
        let tokens = vec![(TokenType::Identifier, TokenValue::Identifier("b".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(6)),
                          (TokenType::Semicolon, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();
        let statement_list = parser.statement_list(&mut ast).unwrap();
        assert_eq!(statement_list.len(), 1);

        let stmt_index = statement_list[0];
        let stmt_node = ast.get_node(stmt_index);
        assert_eq!(stmt_node.get_parent(), None);
        let children = stmt_node.get_children();
        let var_node = ast.get_node(children[0]);
        assert_eq!(var_node.get_parent(), Some(stmt_index));
        assert_eq!(var_node.get_value().unwrap(),
                   TokenValue::Identifier("b".to_string()));
        let expr_node = ast.get_node(children[1]);
        assert_eq!(expr_node.get_parent(), Some(stmt_index));
        assert_eq!(expr_node.get_value().unwrap(), TokenValue::Integer(6));
    }

    #[test]
    fn parser_compound_statement_parses_compound_statement() {
        // Input: BEGIN a := 5 END
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(5)),
                          (TokenType::End, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();

        let cmpd_index = parser.compound_statement(&mut ast).unwrap();
        let cmpd_node = ast.get_node(cmpd_index);
        assert_eq!(cmpd_node.get_parent(), None);

        let statements = cmpd_node.get_children();
        assert_eq!(statements.len(), 1);

        let stmt_node = ast.get_node(statements[0]);
        assert_eq!(stmt_node.get_parent(), Some(cmpd_index));

        let children = stmt_node.get_children();
        let var_node = ast.get_node(children[0]);
        assert_eq!(var_node.get_parent(), Some(statements[0]));
        assert_eq!(var_node.get_value().unwrap(),
                   TokenValue::Identifier("a".to_string()));
    }

    #[test]
    fn parser_compound_statement_returns_error_when_begin_is_missing() {
        // Input: a := 5 END
        let tokens = vec![(TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(5)),
                          (TokenType::End, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();

        assert!(parser.compound_statement(&mut ast).is_err());
    }

    #[test]
    fn parser_compound_statement_returns_error_when_end_is_missing() {
        // Input: BEGIN a := 5
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(5))];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();

        assert!(parser.compound_statement(&mut ast).is_err());
    }

    #[test]
    fn parser_compound_statement_returns_error_when_statements_arent_separated_with_semicolons() {
        // Input: BEGIN a := 5 b := 6 END
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(5)),
                          (TokenType::Identifier, TokenValue::Identifier("b".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(6)),
                          (TokenType::End, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();

        assert!(parser.compound_statement(&mut ast).is_err());
    }

    #[test]
    fn parser_compound_statement_parses_nested_compound_statement() {
        // Input: BEGIN BEGIN a := 5 END END
        let tokens = vec![(TokenType::Begin, TokenValue::Empty),
                          (TokenType::Begin, TokenValue::Empty),
                          (TokenType::Identifier, TokenValue::Identifier("a".to_string())),
                          (TokenType::Assign, TokenValue::Empty),
                          (TokenType::Integer, TokenValue::Integer(5)),
                          (TokenType::End, TokenValue::Empty),
                          (TokenType::End, TokenValue::Empty)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let mut ast = Ast::new();

        let outer_index = parser.compound_statement(&mut ast).unwrap();
        let outer_node = ast.get_node(outer_index);
        assert_eq!(outer_node.get_parent(), None);

        let inner_index = outer_node.get_children()[0];
        let inner_node = ast.get_node(inner_index);
        assert_eq!(inner_node.get_parent(), Some(outer_index));

        let stmt_index = inner_node.get_children()[0];
        let stmt_node = ast.get_node(stmt_index);
        assert_eq!(stmt_node.get_parent(), Some(inner_index));

        let var_index = stmt_node.get_children()[0];
        let var_node = ast.get_node(var_index);
        assert_eq!(var_node.get_parent(), Some(stmt_index));
        assert_eq!(var_node.get_value().unwrap(),
                   TokenValue::Identifier("a".to_string()));
    }
}
