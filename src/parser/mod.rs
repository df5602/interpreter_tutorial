//! This module contains the parser.

use std::cell::RefCell;
use tokens::{Token, TokenType, OperatorType, Span};
use ast::{Ast, AstIndex, BinaryOperatorNode, UnaryOperatorNode, IntegerNode, VariableNode,
          AssignmentStmtNode, CompoundStmtNode};
use errors::SyntaxError;
use lexer::Lexer;

/// Parser type. It is generic over any Lexer implementing the `Lexer` trait.
pub struct Parser<L> {
    current_token: RefCell<Option<Token>>,
    lexer: L,
}

impl<L: Lexer> Parser<L> {
    /// Construct new `Parser`.
    pub fn new(lexer: L) -> Parser<L> {
        Parser {
            current_token: RefCell::new(None),
            lexer: lexer,
        }
    }

    /// Consumes current token if it is of the expected type
    fn eat(&self, token_type: TokenType) -> Result<Span, SyntaxError> {
        let mut current_token = self.current_token.borrow_mut();
        let span = current_token.as_ref()
            .unwrap()
            .span
            .clone();

        // If token has expected type...
        if current_token.as_ref().unwrap().token_type == token_type {
            // ... consume token and set current token to the next token
            if token_type != TokenType::Eof {
                let next_token = self.lexer.get_next_token();
                match next_token {
                    Ok(token) => {
                        *current_token = Some(token);
                        Ok(span)
                    }
                    Err(e) => Err(e),
                }
            } else {
                Ok(span)
            }
        } else {
            Err(SyntaxError {
                    msg: format!("Expected {}, got {}",
                                 token_type,
                                 current_token.as_ref().unwrap().token_type),
                    span: span,
                })
        }
    }

    /// Loads first token
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

    /// Gets a clone of the current token
    /// Precondition: First token has been loaded
    fn get_current_token(&self) -> Token {
        self.current_token
            .borrow()
            .clone()
            .unwrap()
    }

    /// Start parsing: load first token, parse input and checks that last token is an EOF
    /// As a sanity check, the generated AST is checked for contiguity
    pub fn parse(&self, ast: &mut Ast) -> Result<(), SyntaxError> {
        self.load_first_token()?;

        self.program(ast)?;

        self.eat(TokenType::Eof)?;

        if ast.is_contiguous() {
            Ok(())
        } else {
            panic!("Internal Error (AST is not contiguous)")
        }
    }

    /// Evaluate a program:
    /// program -> compound_statement DOT
    fn program(&self, ast: &mut Ast) -> Result<AstIndex, SyntaxError> {
        // Expect compound statement
        let result = self.compound_statement(ast)?;

        // Expect '.'
        self.eat(TokenType::Dot)?;

        Ok(result)
    }

    /// Evaluate a compound statement:
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

    /// Evaluate a statement list:
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

    /// Evaluate a statement:
    /// statement -> (compound_statement | assignment_statement)?
    fn statement(&self, ast: &mut Ast) -> Result<Option<AstIndex>, SyntaxError> {
        match self.get_current_token().token_type {
            TokenType::Begin => Ok(Some(self.compound_statement(ast)?)),
            TokenType::Identifier => Ok(Some(self.assignment_statement(ast)?)),
            _ => Ok(None),
        }
    }

    /// Evaluate an assignment statement:
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

    /// Create a variable node
    fn variable(&self, ast: &mut Ast) -> Result<AstIndex, SyntaxError> {
        let variable = self.get_current_token();
        self.eat(TokenType::Identifier)?;

        // Extract name
        let name = variable.value
            .as_ref()
            .unwrap()
            .extract_identifier_value();

        // Construct AST node
        let node = VariableNode::new(name, variable);
        Ok(ast.add_node(node))
    }

    /// Evaluate an expression:
    /// expr -> term ((PLUS | MINUS) term)*
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
            let op_type = op.value
                .as_ref()
                .unwrap()
                .extract_operator_type();

            // Expect a term on the right hand side
            let rhs = self.term(ast)?;

            // Construct AST node
            let node = BinaryOperatorNode::new(result, rhs, op_type, op);
            result = ast.add_node(node);
        }
    }

    /// Evaluate a term:
    /// term -> factor ((TIMES | DIVISION) factor)*
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
                let op_type = op.value
                    .as_ref()
                    .unwrap()
                    .extract_operator_type();
                if op_type != OperatorType::Times && op_type != OperatorType::IntegerDivision {
                    return Ok(result);
                }
            }
            self.eat(TokenType::Operator)?;
            let op_type = op.value
                .as_ref()
                .unwrap()
                .extract_operator_type();

            // Expect a factor on the right hand side
            let rhs = self.factor(ast)?;

            // Construct AST node
            let node = BinaryOperatorNode::new(result, rhs, op_type, op);
            result = ast.add_node(node);
        }
    }

    /// Evaluate a factor:
    /// factor -> ( PLUS | MINUS) factor
    ///           | INTEGER
    ///           | LPAREN expr RPAREN
    ///           | variable
    fn factor(&self, ast: &mut Ast) -> Result<AstIndex, SyntaxError> {

        // First token should be an INTEGER, PLUS, MINUS, LPAREN or IDENTIFIER
        let current_token = self.get_current_token();

        if current_token.token_type == TokenType::IntegerLiteral {
            self.eat(TokenType::IntegerLiteral)?;

            let value = current_token.value
                .as_ref()
                .unwrap()
                .extract_integer_value();
            let node = IntegerNode::new(value, current_token);

            Ok(ast.add_node(node))
        } else if current_token.token_type == TokenType::Operator {
            // Extract value
            let op_type = current_token.value
                .as_ref()
                .unwrap()
                .extract_operator_type();
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
                        span: current_token.span,
                    })
            }
        } else if current_token.token_type == TokenType::LParen {
            let pos_lparen = self.eat(TokenType::LParen)?.start;

            let result = self.expr(ast)?;

            let pos_rparen = self.eat(TokenType::RParen)?.end;

            ast.get_node_mut(result).set_span(Span::new(pos_lparen, pos_rparen));

            Ok(result)
        } else {
            self.variable(ast)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokens::*;
    use ast::Ast;
    use lexer::{Lexer, MockLexer};

    fn setup_from<'a>(tokens: Vec<(TokenType, TokenValue)>) -> (Parser<MockLexer>, Ast<'a>) {
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        assert!(parser.load_first_token().is_ok());
        let ast = Ast::new();
        (parser, ast)
    }

    fn verify_node(ast: &Ast, idx: AstIndex, parent: Option<AstIndex>, value: TokenValue) {
        let node = ast.get_node(idx);
        assert_eq!(node.get_parent(), parent);
        assert_eq!(node.get_value().unwrap(), value);
    }

    #[test]
    fn parser_eat_should_consume_token_if_it_has_the_correct_type() {
        // Input: +4
        let tokens = vec![plus!(), integer!(4)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        *parser.current_token.borrow_mut() = Some(parser.lexer.get_next_token().unwrap());
        let _op = parser.eat(TokenType::Operator);
        let current_token = parser.current_token.borrow();
        match *current_token {
            Some(ref token) => assert_eq!(TokenType::IntegerLiteral, token.token_type),
            None => assert!(false),
        }
    }

    #[test]
    fn parser_eat_should_not_consume_token_if_it_has_the_wrong_type() {
        // Input: +4
        let tokens = vec![plus!(), integer!(4)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        *parser.current_token.borrow_mut() = Some(parser.lexer.get_next_token().unwrap());
        let result = parser.eat(TokenType::IntegerLiteral);
        assert!(result.is_err());
    }

    #[test]
    // expr -> INTEGER OPERATOR INTEGER
    fn parser_expr_should_create_operator_node_when_expression_is_addition() {
        // Input: 3+4
        let tokens = vec![integer!(3), plus!(), integer!(4)];
        let (parser, mut ast) = setup_from(tokens);

        let op_index = parser.expr(&mut ast).unwrap();
        verify_node(&ast,
                    op_index,
                    None,
                    TokenValue::Operator(OperatorType::Plus));


        let operands = ast.get_node(op_index).get_children();
        verify_node(&ast, operands[0], Some(op_index), TokenValue::Integer(3));
        verify_node(&ast, operands[1], Some(op_index), TokenValue::Integer(4));
    }

    #[test]
    // expr -> INTEGER OPERATOR INTEGER
    fn parser_expr_should_create_operator_node_when_expression_is_subtraction() {
        // Input: 4-3
        let tokens = vec![integer!(4), minus!(), integer!(3)];
        let (parser, mut ast) = setup_from(tokens);

        let op_index = parser.expr(&mut ast).unwrap();
        verify_node(&ast,
                    op_index,
                    None,
                    TokenValue::Operator(OperatorType::Minus));

        let operands = ast.get_node(op_index).get_children();
        verify_node(&ast, operands[0], Some(op_index), TokenValue::Integer(4));
        verify_node(&ast, operands[1], Some(op_index), TokenValue::Integer(3));
    }

    #[test]
    fn parser_expr_should_not_parse_expressions_that_dont_have_integer_after_operator() {
        // Input: 4+-
        let tokens = vec![integer!(4), plus!(), minus!()];
        let (parser, mut ast) = setup_from(tokens);

        let result = parser.expr(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_expr_should_not_parse_empty_string() {
        // Input: (Empty string)
        let tokens = vec![];
        let (parser, mut ast) = setup_from(tokens);

        let result = parser.expr(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_expr_should_not_parse_expressions_that_dont_terminate_with_eof() {
        // Input: 1+3 div
        let tokens = vec![integer!(1), plus!(), integer!(3), int_div!()];
        let (parser, mut ast) = setup_from(tokens);

        let result = parser.expr(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_load_first_token_should_load_first_token() {
        // Input: 2+3
        let tokens = vec![integer!(2), plus!(), integer!(3)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let _ = parser.load_first_token();
        assert_eq!(TokenType::IntegerLiteral,
                   parser.current_token
                       .borrow()
                       .clone()
                       .unwrap()
                       .token_type);
        let val = parser.current_token
            .borrow()
            .clone()
            .unwrap()
            .value
            .unwrap();
        match val {
            TokenValue::Integer(val) => assert_eq!(2, val),
            _ => panic!(),
        }
    }

    #[test]
    fn parser_expr_should_create_integer_node_if_input_consists_of_only_integer() {
        // Input: 42
        let tokens = vec![integer!(42)];
        let (parser, mut ast) = setup_from(tokens);

        let index = parser.expr(&mut ast).unwrap();
        verify_node(&ast, index, None, TokenValue::Integer(42));
    }

    #[test]
    fn parser_term_should_create_operator_node_when_expression_is_multiplication() {
        // Input: 3*4
        let tokens = vec![integer!(3), times!(), integer!(4)];
        let (parser, mut ast) = setup_from(tokens);

        let op_index = parser.term(&mut ast).unwrap();
        verify_node(&ast,
                    op_index,
                    None,
                    TokenValue::Operator(OperatorType::Times));

        let operands = ast.get_node(op_index).get_children();
        verify_node(&ast, operands[0], Some(op_index), TokenValue::Integer(3));
        verify_node(&ast, operands[1], Some(op_index), TokenValue::Integer(4));
    }

    #[test]
    fn parser_term_should_create_operator_node_when_expression_is_division() {
        // Input: 4 div 2
        let tokens = vec![integer!(4), int_div!(), integer!(2)];
        let (parser, mut ast) = setup_from(tokens);

        let op_index = parser.term(&mut ast).unwrap();
        verify_node(&ast,
                    op_index,
                    None,
                    TokenValue::Operator(OperatorType::IntegerDivision));

        let operands = ast.get_node(op_index).get_children();
        verify_node(&ast, operands[0], Some(op_index), TokenValue::Integer(4));
        verify_node(&ast, operands[1], Some(op_index), TokenValue::Integer(2));
    }

    #[test]
    fn parser_term_should_return_integer_node_if_input_consists_of_only_integer() {
        // Input: 42
        let tokens = vec![integer!(42)];
        let (parser, mut ast) = setup_from(tokens);

        let index = parser.term(&mut ast).unwrap();
        verify_node(&ast, index, None, TokenValue::Integer(42));
    }

    #[test]
    fn parser_term_should_not_parse_expressions_that_dont_have_integer_after_operator() {
        // Input: 4*div
        let tokens = vec![integer!(4), times!(), int_div!()];
        let (parser, mut ast) = setup_from(tokens);

        let result = parser.term(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_term_should_not_parse_empty_string() {
        // Input: (Empty string)
        let tokens = vec![];
        let (parser, mut ast) = setup_from(tokens);

        let result = parser.term(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_term_should_not_parse_expressions_that_dont_terminate_with_eof() {
        // Input: 1*3 div
        let tokens = vec![integer!(1), times!(), integer!(3), int_div!()];
        let (parser, mut ast) = setup_from(tokens);

        let result = parser.term(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_factor_should_return_integer_node_if_input_consists_of_only_integer() {
        // Input: 42
        let tokens = vec![integer!(42)];
        let (parser, mut ast) = setup_from(tokens);

        let index = parser.factor(&mut ast).unwrap();
        verify_node(&ast, index, None, TokenValue::Integer(42));
    }

    #[test]
    fn parser_factor_creates_graph_of_expr_if_input_consists_of_expr_in_parentheses() {
        // Input: (6+3)
        let tokens = vec![lparen!(), integer!(6), plus!(), integer!(3), rparen!()];
        let (parser, mut ast) = setup_from(tokens);

        let op_index = parser.factor(&mut ast).unwrap();
        verify_node(&ast,
                    op_index,
                    None,
                    TokenValue::Operator(OperatorType::Plus));

        let operands = ast.get_node(op_index).get_children();
        verify_node(&ast, operands[0], Some(op_index), TokenValue::Integer(6));
        verify_node(&ast, operands[1], Some(op_index), TokenValue::Integer(3));
    }

    #[test]
    fn parser_factor_creates_integer_node_if_input_consists_of_integer_in_parentheses() {
        // Input: (6)
        let tokens = vec![lparen!(), integer!(6), rparen!()];
        let (parser, mut ast) = setup_from(tokens);

        let index = parser.factor(&mut ast).unwrap();
        verify_node(&ast, index, None, TokenValue::Integer(6));
    }

    #[test]
    fn parser_factor_creates_unary_operator_node_if_input_consists_of_unary_minus() {
        // Input: -5
        let tokens = vec![minus!(), integer!(5)];
        let (parser, mut ast) = setup_from(tokens);

        let op_index = parser.factor(&mut ast).unwrap();
        verify_node(&ast,
                    op_index,
                    None,
                    TokenValue::Operator(OperatorType::Minus));

        let operand = ast.get_node(op_index).get_children()[0];
        verify_node(&ast, operand, Some(op_index), TokenValue::Integer(5));
    }

    #[test]
    fn parser_factor_creates_unary_operator_node_if_input_consists_of_unary_plus() {
        // Input: +5
        let tokens = vec![plus!(), integer!(5)];
        let (parser, mut ast) = setup_from(tokens);

        let op_index = parser.factor(&mut ast).unwrap();
        verify_node(&ast,
                    op_index,
                    None,
                    TokenValue::Operator(OperatorType::Plus));

        let operand = ast.get_node(op_index).get_children()[0];
        verify_node(&ast, operand, Some(op_index), TokenValue::Integer(5));
    }

    #[test]
    fn parser_factor_returns_error_if_input_consists_of_unary_times() {
        // Input: *5
        let tokens = vec![times!(), integer!(5)];
        let (parser, mut ast) = setup_from(tokens);

        let result = parser.factor(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_factor_returns_error_if_input_consists_of_unary_division() {
        // Input: div 5
        let tokens = vec![int_div!(), integer!(5)];
        let (parser, mut ast) = setup_from(tokens);

        let result = parser.factor(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_factor_returns_error_if_lparen_is_followed_by_rparen() {
        // Input: ()
        let tokens = vec![lparen!(), rparen!()];
        let (parser, mut ast) = setup_from(tokens);

        let result = parser.factor(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_factor_returns_error_if_operator_is_followed_by_rparen() {
        // Input: (6+)
        let tokens = vec![lparen!(), integer!(6), plus!(), rparen!()];
        let (parser, mut ast) = setup_from(tokens);

        let result = parser.factor(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_factor_returns_error_if_parentheses_are_mismatched() {
        // Input: (6+3
        let tokens = vec![lparen!(), integer!(6), plus!(), integer!(3)];
        let (parser, mut ast) = setup_from(tokens);

        let result = parser.factor(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_factor_creates_variable_node_when_it_encounters_identifier() {
        // Input: a
        let tokens = vec![identifier!("a")];
        let (parser, mut ast) = setup_from(tokens);

        let var_index = parser.factor(&mut ast).unwrap();
        verify_node(&ast,
                    var_index,
                    None,
                    TokenValue::Identifier("a".to_string()));
    }

    #[test]
    fn parser_start_returns_error_if_parentheses_are_mismatched() {
        // Input: (6+3))
        let tokens = vec![lparen!(), integer!(6), plus!(), integer!(3), rparen!(), rparen!()];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        let result = parser.parse(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_variable_creates_variable_node_when_token_is_identifier() {
        // Input: a
        let tokens = vec![identifier!("a")];
        let (parser, mut ast) = setup_from(tokens);

        let var_index = parser.variable(&mut ast).unwrap();
        verify_node(&ast,
                    var_index,
                    None,
                    TokenValue::Identifier("a".to_string()));
    }

    #[test]
    fn parser_variable_returns_error_when_token_is_no_identifier() {
        // Input: 5
        let tokens = vec![integer!(5)];
        let (parser, mut ast) = setup_from(tokens);

        let result = parser.variable(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_assignment_statement_parses_assignment_statement() {
        // Input: a := 5
        let tokens = vec![identifier!("a"), assign!(), integer!(5)];
        let (parser, mut ast) = setup_from(tokens);

        let assign_index = parser.assignment_statement(&mut ast).unwrap();
        let assign_node = ast.get_node(assign_index);
        assert_eq!(assign_node.get_parent(), None);

        let children = assign_node.get_children();
        verify_node(&ast,
                    children[0],
                    Some(assign_index),
                    TokenValue::Identifier("a".to_string()));
        verify_node(&ast,
                    children[1],
                    Some(assign_index),
                    TokenValue::Integer(5));
    }

    #[test]
    fn parser_assignment_statement_parses_assignment_statement_with_expression() {
        // Input: a := 5 + 7
        let tokens = vec![identifier!("a"), assign!(), integer!(5), plus!(), integer!(7)];
        let (parser, mut ast) = setup_from(tokens);

        let assign_index = parser.assignment_statement(&mut ast).unwrap();
        let assign_node = ast.get_node(assign_index);
        assert_eq!(assign_node.get_parent(), None);

        let children = assign_node.get_children();
        verify_node(&ast,
                    children[0],
                    Some(assign_index),
                    TokenValue::Identifier("a".to_string()));
        verify_node(&ast,
                    children[1],
                    Some(assign_index),
                    TokenValue::Operator(OperatorType::Plus));
    }

    #[test]
    fn parser_assignment_statement_doesnt_parse_assignment_without_variable_on_the_left() {
        // Input: 1 := 5
        let tokens = vec![integer!(1), assign!(), integer!(5)];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.assignment_statement(&mut ast).is_err());
    }

    #[test]
    fn parser_assignment_statement_doesnt_parse_assignment_without_assign_token_in_the_middle() {
        // Input: a + 5
        let tokens = vec![identifier!("a"), plus!(), integer!(5)];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.assignment_statement(&mut ast).is_err());
    }

    #[test]
    fn parser_assignment_statement_doesnt_parse_assignment_without_expression_on_the_right() {
        // Input: a := BEGIN
        let tokens = vec![identifier!("a"), assign!(), begin!()];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.assignment_statement(&mut ast).is_err());
    }

    #[test]
    fn parser_statement_returns_assignment_statement_if_statement_is_assignment_statement() {
        // Input: a := 5
        let tokens = vec![identifier!("a"), assign!(), integer!(5)];
        let (parser, mut ast) = setup_from(tokens);

        let stmt_index = parser.statement(&mut ast).unwrap().unwrap();
        let stmt_node = ast.get_node(stmt_index);
        assert_eq!(stmt_node.get_parent(), None);

        let children = stmt_node.get_children();
        verify_node(&ast,
                    children[0],
                    Some(stmt_index),
                    TokenValue::Identifier("a".to_string()));
        verify_node(&ast, children[1], Some(stmt_index), TokenValue::Integer(5));
    }

    #[test]
    fn parser_statement_returns_none_if_no_statement_is_present() {
        // Input: END
        let tokens = vec![end!()];
        let (parser, mut ast) = setup_from(tokens);

        let result = parser.statement(&mut ast).unwrap();
        assert_eq!(result, None);
    }

    #[test]
    fn parser_statement_list_returns_assignment_statement_if_statement_is_assignment() {
        // Input: a := 5
        let tokens = vec![identifier!("a"), assign!(), integer!(5)];
        let (parser, mut ast) = setup_from(tokens);

        let statement_list = parser.statement_list(&mut ast).unwrap();
        assert_eq!(statement_list.len(), 1);

        let stmt_index = statement_list[0];
        let stmt_node = ast.get_node(stmt_index);
        assert_eq!(stmt_node.get_parent(), None);

        let children = stmt_node.get_children();
        verify_node(&ast,
                    children[0],
                    Some(stmt_index),
                    TokenValue::Identifier("a".to_string()));
        verify_node(&ast, children[1], Some(stmt_index), TokenValue::Integer(5));
    }

    #[test]
    fn parser_statement_list_returns_two_statements_when_statements_are_separated_by_semicolon() {
        // Input: a := 5; b := 6
        let tokens = vec![identifier!("a"),
                          assign!(),
                          integer!(5),
                          semicolon!(),
                          identifier!("b"),
                          assign!(),
                          integer!(6)];
        let (parser, mut ast) = setup_from(tokens);

        let statement_list = parser.statement_list(&mut ast).unwrap();
        assert_eq!(statement_list.len(), 2);

        let mut stmt_index = statement_list[0];
        let mut stmt_node = ast.get_node(stmt_index);
        assert_eq!(stmt_node.get_parent(), None);

        let mut children = stmt_node.get_children();
        verify_node(&ast,
                    children[0],
                    Some(stmt_index),
                    TokenValue::Identifier("a".to_string()));
        verify_node(&ast, children[1], Some(stmt_index), TokenValue::Integer(5));

        stmt_index = statement_list[1];
        stmt_node = ast.get_node(stmt_index);
        assert_eq!(stmt_node.get_parent(), None);

        children = stmt_node.get_children();
        verify_node(&ast,
                    children[0],
                    Some(stmt_index),
                    TokenValue::Identifier("b".to_string()));
        verify_node(&ast, children[1], Some(stmt_index), TokenValue::Integer(6));
    }

    #[test]
    fn parser_statement_list_returns_only_first_stmt_when_stmts_are_not_separated_by_semicolon() {
        // Input: a := 5 b := 6
        let tokens = vec![identifier!("a"),
                          assign!(),
                          integer!(5),
                          identifier!("b"),
                          assign!(),
                          integer!(6)];
        let (parser, mut ast) = setup_from(tokens);

        let statement_list = parser.statement_list(&mut ast).unwrap();
        assert_eq!(statement_list.len(), 1);

        let stmt_index = statement_list[0];
        let stmt_node = ast.get_node(stmt_index);
        assert_eq!(stmt_node.get_parent(), None);

        let children = stmt_node.get_children();
        verify_node(&ast,
                    children[0],
                    Some(stmt_index),
                    TokenValue::Identifier("a".to_string()));
        verify_node(&ast, children[1], Some(stmt_index), TokenValue::Integer(5));
    }

    #[test]
    fn parser_statement_list_can_begin_with_semicolon() {
        // Input: ;b := 6
        let tokens = vec![semicolon!(), identifier!("b"), assign!(), integer!(6)];
        let (parser, mut ast) = setup_from(tokens);

        let statement_list = parser.statement_list(&mut ast).unwrap();
        assert_eq!(statement_list.len(), 1);

        let stmt_index = statement_list[0];
        let stmt_node = ast.get_node(stmt_index);
        assert_eq!(stmt_node.get_parent(), None);

        let children = stmt_node.get_children();
        verify_node(&ast,
                    children[0],
                    Some(stmt_index),
                    TokenValue::Identifier("b".to_string()));
        verify_node(&ast, children[1], Some(stmt_index), TokenValue::Integer(6));
    }

    #[test]
    fn parser_statement_list_can_end_with_semicolon() {
        // Input: b := 6;
        let tokens = vec![identifier!("b"), assign!(), integer!(6), semicolon!()];
        let (parser, mut ast) = setup_from(tokens);

        let statement_list = parser.statement_list(&mut ast).unwrap();
        assert_eq!(statement_list.len(), 1);

        let stmt_index = statement_list[0];
        let stmt_node = ast.get_node(stmt_index);
        assert_eq!(stmt_node.get_parent(), None);

        let children = stmt_node.get_children();
        verify_node(&ast,
                    children[0],
                    Some(stmt_index),
                    TokenValue::Identifier("b".to_string()));
        verify_node(&ast, children[1], Some(stmt_index), TokenValue::Integer(6));
    }

    #[test]
    fn parser_compound_statement_parses_compound_statement() {
        // Input: BEGIN a := 5 END
        let tokens = vec![begin!(), identifier!("a"), assign!(), integer!(5), end!()];
        let (parser, mut ast) = setup_from(tokens);

        let cmpd_index = parser.compound_statement(&mut ast).unwrap();
        let cmpd_node = ast.get_node(cmpd_index);
        assert_eq!(cmpd_node.get_parent(), None);

        let statements = cmpd_node.get_children();
        assert_eq!(statements.len(), 1);

        let stmt_node = ast.get_node(statements[0]);
        assert_eq!(stmt_node.get_parent(), Some(cmpd_index));

        let children = stmt_node.get_children();
        verify_node(&ast,
                    children[0],
                    Some(statements[0]),
                    TokenValue::Identifier("a".to_string()));
    }

    #[test]
    fn parser_compound_statement_returns_error_when_begin_is_missing() {
        // Input: a := 5 END
        let tokens = vec![identifier!("a"), assign!(), integer!(5), end!()];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.compound_statement(&mut ast).is_err());
    }

    #[test]
    fn parser_compound_statement_returns_error_when_end_is_missing() {
        // Input: BEGIN a := 5
        let tokens = vec![begin!(), identifier!("a"), assign!(), integer!(5)];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.compound_statement(&mut ast).is_err());
    }

    #[test]
    fn parser_compound_statement_returns_error_when_statements_arent_separated_with_semicolons() {
        // Input: BEGIN a := 5 b := 6 END
        let tokens = vec![begin!(),
                          identifier!("a"),
                          assign!(),
                          integer!(5),
                          identifier!("b"),
                          assign!(),
                          integer!(6),
                          end!()];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.compound_statement(&mut ast).is_err());
    }

    #[test]
    fn parser_compound_statement_parses_nested_compound_statement() {
        // Input: BEGIN BEGIN a := 5 END END
        let tokens =
            vec![begin!(), begin!(), identifier!("a"), assign!(), integer!(5), end!(), end!()];
        let (parser, mut ast) = setup_from(tokens);

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
        verify_node(&ast,
                    var_index,
                    Some(stmt_index),
                    TokenValue::Identifier("a".to_string()));
    }

    #[test]
    fn parser_program_parses_program() {
        // Input: BEGIN a := 5 END.
        let tokens = vec![begin!(), identifier!("a"), assign!(), integer!(5), end!(), dot!()];
        let (parser, mut ast) = setup_from(tokens);

        let cmpd_index = parser.program(&mut ast).unwrap();
        let cmpd_node = ast.get_node(cmpd_index);
        assert_eq!(cmpd_node.get_parent(), None);

        let statements = cmpd_node.get_children();
        assert_eq!(statements.len(), 1);

        let stmt_node = ast.get_node(statements[0]);
        assert_eq!(stmt_node.get_parent(), Some(cmpd_index));

        let children = stmt_node.get_children();
        verify_node(&ast,
                    children[0],
                    Some(statements[0]),
                    TokenValue::Identifier("a".to_string()));
    }

    #[test]
    fn parser_program_returns_error_when_compound_statement_is_missing() {
        // Input: .
        let tokens = vec![dot!()];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.program(&mut ast).is_err());
    }

    #[test]
    fn parser_program_returns_error_when_dot_is_missing() {
        // Input: BEGIN a := 5 END
        let tokens = vec![begin!(), identifier!("a"), assign!(), integer!(5), end!()];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.program(&mut ast).is_err());
    }

    #[test]
    fn parser_program_returns_error_when_two_compound_statements_are_present() {
        // Input: BEGIN a := 5 END; BEGIN b := 6 END.
        let tokens = vec![begin!(),
                          identifier!("a"),
                          assign!(),
                          integer!(5),
                          end!(),
                          semicolon!(),
                          begin!(),
                          identifier!("b"),
                          assign!(),
                          integer!(6),
                          end!(),
                          dot!()];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.program(&mut ast).is_err());
    }
}
