//! This module contains the parser.

use std::cell::RefCell;
use tokens::{Token, TokenType, OperatorType, Span};
use ast::{Ast, AstIndex, BinaryOperatorNode, UnaryOperatorNode, IntegerNode, VariableNode,
          AssignmentStmtNode, CompoundStmtNode, BlockNode, ProgramNode, TypeNode};
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

    /// Parse a program:
    /// program -> PROGRAM variable SEMICOLON block DOT
    fn program(&self, ast: &mut Ast) -> Result<AstIndex, SyntaxError> {
        // Expect PROGRAM token
        self.eat(TokenType::Program)?;

        // Expect variable
        let variable_node = self.variable(ast)?;
        let program_name = ast.get_node(variable_node)
            .get_value()
            .unwrap()
            .extract_identifier_value();

        // Expect semicolon
        self.eat(TokenType::Semicolon)?;

        // Expect block
        let block_node = self.block(ast)?;

        // Expect '.'
        self.eat(TokenType::Dot)?;

        // Construct node
        let program_node = ProgramNode::new(program_name, variable_node, block_node);
        Ok(ast.add_node(program_node))
    }

    /// Parse a block:
    /// block -> compound_statement
    fn block(&self, ast: &mut Ast) -> Result<AstIndex, SyntaxError> {
        let compound_statement = self.compound_statement(ast)?;
        let node = BlockNode::new(Vec::new(), compound_statement);
        Ok(ast.add_node(node))
    }

    /// Parse a type specifier:
    /// type_spec -> INTEGER | REAL
    fn type_spec(&self, ast: &mut Ast) -> Result<AstIndex, SyntaxError> {
        let type_specifier = self.get_current_token();
        self.eat(TokenType::TypeSpecifier)?;

        let type_value = type_specifier.value
            .as_ref()
            .unwrap()
            .extract_type_specifier();
        let node = TypeNode::new(type_value, type_specifier);
        Ok(ast.add_node(node))
    }

    /// Parse a compound statement:
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

    /// Parse a statement list:
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

    /// Parse a statement:
    /// statement -> (compound_statement | assignment_statement)?
    fn statement(&self, ast: &mut Ast) -> Result<Option<AstIndex>, SyntaxError> {
        match self.get_current_token().token_type {
            TokenType::Begin => Ok(Some(self.compound_statement(ast)?)),
            TokenType::Identifier => Ok(Some(self.assignment_statement(ast)?)),
            _ => Ok(None),
        }
    }

    /// Parse an assignment statement:
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

    /// Parse an expression:
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

    /// Parse a term:
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

    /// Parse a factor:
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
        let tokens = vec![plus!(), integer_lit!(4)];
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
        let tokens = vec![plus!(), integer_lit!(4)];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        *parser.current_token.borrow_mut() = Some(parser.lexer.get_next_token().unwrap());
        let result = parser.eat(TokenType::IntegerLiteral);
        assert!(result.is_err());
    }

    #[test]
    fn parser_load_first_token_should_load_first_token() {
        // Input: 2+3
        let tokens = vec![integer_lit!(2), plus!(), integer_lit!(3)];
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
    fn parser_start_returns_error_if_parentheses_are_mismatched() {
        // Input: (6+3))
        let tokens =
            vec![lparen!(), integer_lit!(6), plus!(), integer_lit!(3), rparen!(), rparen!()];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        let result = parser.parse(&mut ast);
        assert!(result.is_err());
    }

    // program : PROGRAM variable SEMICOLON block DOT
    //      PROGRAM variable SEMICOLON block DOT -> PASS: PROG.1
    //      variable SEMICOLON block DOT -> FAIL: PROG.2
    //      PROGRAM PROGRAM variable SEMICOLON block DOT -> FAIL: PROG.3
    //      PROGRAM SEMICOLON block DOT -> FAIL: PROG.4
    //      PROGRAM variable variable SEMICOLON block DOT -> FAIL: PROG.5
    //      PROGRAM variable block DOT -> FAIL: PROG.6
    //      PROGRAM variable SEMICOLON SEMICOLON block DOT -> FAIL: PROG.7
    //      PROGRAM variable SEMICOLON DOT -> FAIL: PROG.8
    //      PROGRAM variable SEMICOLON block block DOT -> FAIL: PROG.9
    //      PROGRAM variable SEMICOLON block -> FAIL: PROG.10
    //      PROGRAM variable SEMICOLON block DOT DOT -> FAIL: PROG.11

    #[test]
    // PROG.1
    fn parser_program_parses_program() {
        // Input: PROGRAM Test; BEGIN a := 5 END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(5),
                          end!(),
                          dot!()];
        let (parser, mut ast) = setup_from(tokens);

        let program_index = parser.program(&mut ast).unwrap();
        let program_node = ast.get_node(program_index);
        assert_eq!(program_node.get_parent(), None);

        let block_index = program_node.get_children()[1];
        let block_node = ast.get_node(block_index);
        assert_eq!(block_node.get_parent(), Some(program_index));

        let block_children = block_node.get_children();
        let cmpd_index = block_children[block_children.len() - 1];
        let cmpd_node = ast.get_node(cmpd_index);
        assert_eq!(cmpd_node.get_parent(), Some(block_index));

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
    // PROG.2
    fn parser_program_returns_error_when_program_keyword_is_missing() {
        // Input: Test; BEGIN a := 5 END.
        let tokens = vec![identifier!("Test"),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(5),
                          end!(),
                          dot!()];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.program(&mut ast).is_err());
    }

    #[test]
    // PROG.3
    fn parser_program_returns_error_when_program_keyword_occurs_twice() {
        // Input: PROGRAM PROGRAM Test; BEGIN a := 5 END.
        let tokens = vec![program!(),
                          program!(),
                          identifier!("Test"),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(5),
                          end!(),
                          dot!()];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.program(&mut ast).is_err());
    }

    #[test]
    // PROG.4
    fn parser_program_returns_error_when_program_name_is_missing() {
        // Input: PROGRAM; BEGIN a := 5 END.
        let tokens = vec![program!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(5),
                          end!(),
                          dot!()];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.program(&mut ast).is_err());
    }

    #[test]
    // PROG.5
    fn parser_program_returns_error_when_program_has_two_names() {
        // Input: PROGRAM Test1 Test2; BEGIN a := 5 END.
        let tokens = vec![program!(),
                          identifier!("Test1"),
                          identifier!("Test2"),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(5),
                          end!(),
                          dot!()];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.program(&mut ast).is_err());
    }

    #[test]
    // PROG.6
    fn parser_program_returns_error_when_semicolon_after_program_name_is_missing() {
        // Input: PROGRAM Test BEGIN a := 5 END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(5),
                          end!(),
                          dot!()];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.program(&mut ast).is_err());
    }

    #[test]
    // PROG.7
    fn parser_program_returns_error_when_two_semicolons_after_program_name() {
        // Input: PROGRAM Test;; BEGIN a := 5 END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(5),
                          end!(),
                          dot!()];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.program(&mut ast).is_err());
    }

    #[test]
    // PROG.8
    fn parser_program_returns_error_when_compound_statement_is_missing() {
        // Input: PROGRAM Test; .
        let tokens = vec![program!(), identifier!("Test"), semicolon!(), dot!()];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.program(&mut ast).is_err());
    }

    #[test]
    // PROG.9
    fn parser_program_returns_error_when_two_compound_statements_are_present() {
        // Input: PROGRAM Test; BEGIN a := 5 END BEGIN b := 6 END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(5),
                          end!(),
                          begin!(),
                          identifier!("b"),
                          assign!(),
                          integer_lit!(6),
                          end!(),
                          dot!()];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.program(&mut ast).is_err());
    }

    #[test]
    // PROG.10
    fn parser_program_returns_error_when_dot_is_missing() {
        // Input: PROGRAM Test; BEGIN a := 5 END
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(5),
                          end!()];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.program(&mut ast).is_err());
    }

    #[test]
    // PROG.11
    fn parser_parse_returns_error_when_ends_with_two_dots() {
        // Input: PROGRAM Test; BEGIN a := 5 END..
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(5),
                          end!(),
                          dot!(),
                          dot!()];
        let lexer = MockLexer::new(tokens);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        assert!(parser.parse(&mut ast).is_err());
    }

    #[test]
    fn parser_program_parses_program_name() {
        // Input: PROGRAM Test; BEGIN a := 5 END.
        let tokens = vec![program!(),
                          identifier!("Test"),
                          semicolon!(),
                          begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(5),
                          end!(),
                          dot!()];
        let (parser, mut ast) = setup_from(tokens);

        let program_index = parser.program(&mut ast).unwrap();
        let program_node = ast.get_node(program_index);
        assert_eq!(program_node.get_parent(), None);

        let variable_index = program_node.get_children()[0];
        let variable_node = ast.get_node(variable_index);
        assert_eq!(variable_node.get_parent(), Some(program_index));

        assert_eq!(program_node.get_value().unwrap().extract_identifier_value(),
                   "Test".to_lowercase().to_string());
        assert_eq!(variable_node.get_value().unwrap().extract_identifier_value(),
                   "Test".to_lowercase().to_string());
    }

    // block : compound_statement
    //      compound_statement -> PASS: BLK.1
    //      <nothing> -> FAIL: BLK.2
    //      compound_statement compound_statement -> FAIL: PROG.3

    #[test]
    // BLK.1
    fn parser_block_parses_compound_statement() {
        // Input: BEGIN a := 1 END
        let tokens = vec![begin!(), identifier!("a"), assign!(), integer_lit!(1), end!()];
        let (parser, mut ast) = setup_from(tokens);

        let block_index = parser.block(&mut ast).unwrap();
        let block_node = ast.get_node(block_index);
        assert_eq!(block_node.get_parent(), None);

        let block_children = block_node.get_children();
        let stmt_index = block_children[block_children.len() - 1];
        let stmt_node = ast.get_node(stmt_index);
        assert_eq!(stmt_node.get_parent(), Some(block_index));

        let statements = stmt_node.get_children();
        assert_eq!(statements.len(), 1);

        let statement = ast.get_node(statements[0]);
        assert_eq!(statement.get_parent(), Some(stmt_index));

        verify_node(&ast,
                    statement.get_children()[0],
                    Some(statements[0]),
                    TokenValue::Identifier("a".to_string()));
    }

    #[test]
    // BLK.2
    fn parser_block_returns_error_when_empty_input() {
        // Input:
        let tokens = vec![];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.block(&mut ast).is_err());
    }

    // type_spec : INTEGER | REAL
    //      INTEGER -> PASS: TYPE.1
    //      <nothing> -> FAIL: TYPE.2
    //      INTEGER INTEGER -> FAIL: not yet testable
    //      REAL -> PASS: TYPE.4
    //      REAL REAL -> FAIL: not yet testable
    //      INTEGER REAL -> FAIL: not yet testable

    #[test]
    // TYPE.1
    fn parser_type_spec_parses_integer_type_specifier() {
        // Input: INTEGER
        let tokens = vec![integer!()];
        let (parser, mut ast) = setup_from(tokens);

        let type_index = parser.type_spec(&mut ast).unwrap();
        verify_node(&ast, type_index, None, TokenValue::Type(Type::Integer));
    }

    #[test]
    // TYPE.2
    fn parser_type_spec_returns_error_when_no_type_specifier_is_present() {
        // Input:
        let tokens = vec![];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.type_spec(&mut ast).is_err());
    }

    #[test]
    // TYPE.4
    fn parser_type_spec_parses_real_integer_specifier() {
        // Input: REAL
        let tokens = vec![real!()];
        let (parser, mut ast) = setup_from(tokens);

        let type_index = parser.type_spec(&mut ast).unwrap();
        verify_node(&ast, type_index, None, TokenValue::Type(Type::Real));
    }

    // compound_statement : BEGIN statement_list END
    //      BEGIN statement_list END -> PASS: CMPD.1
    //      statement_list END -> FAIL: CMPD.2
    //      BEGIN BEGIN statement_list END -> FAIL: CMPD.3
    //      BEGIN END -> PASS: CMPD.4
    //      BEGIN statement statement END -> FAIL: CMPD.5
    //      BEGIN statement_list -> FAIL: CMPD.6
    //      BEGIN statement_list END END -> FAIL: CMPD.7

    #[test]
    // CMPD.1
    fn parser_compound_statement_parses_compound_statement() {
        // Input: BEGIN a := 5 END
        let tokens = vec![begin!(), identifier!("a"), assign!(), integer_lit!(5), end!()];
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
    // CMPD.2
    fn parser_compound_statement_returns_error_when_begin_is_missing() {
        // Input: a := 5 END
        let tokens = vec![identifier!("a"), assign!(), integer_lit!(5), end!()];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.compound_statement(&mut ast).is_err());
    }

    #[test]
    // CMPD.3
    fn parser_compound_statement_returns_error_when_begin_is_repeated_without_matching_end() {
        // Input: BEGIN BEGIN a := 5 END
        let tokens = vec![begin!(), begin!(), identifier!("a"), assign!(), integer_lit!(5), end!()];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.compound_statement(&mut ast).is_err());
    }

    #[test]
    // CMPD.4
    fn parser_compound_statement_parses_empty_statement_list() {
        // Input: BEGIN END
        let tokens = vec![begin!(), end!()];
        let (parser, mut ast) = setup_from(tokens);

        let cmpd_index = parser.compound_statement(&mut ast).unwrap();
        let cmpd_node = ast.get_node(cmpd_index);
        let statements = cmpd_node.get_children();
        assert!(statements.is_empty());
    }

    #[test]
    // CMPD.5
    fn parser_compound_statement_returns_error_when_statements_arent_separated_with_semicolons() {
        // Input: BEGIN a := 5 b := 6 END
        let tokens = vec![begin!(),
                          identifier!("a"),
                          assign!(),
                          integer_lit!(5),
                          identifier!("b"),
                          assign!(),
                          integer_lit!(6),
                          end!()];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.compound_statement(&mut ast).is_err());
    }

    #[test]
    // CMPD.6
    fn parser_compound_statement_returns_error_when_end_is_missing() {
        // Input: BEGIN a := 5
        let tokens = vec![begin!(), identifier!("a"), assign!(), integer_lit!(5)];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.compound_statement(&mut ast).is_err());
    }

    #[test]
    // CMPD.7
    fn parser_compound_statement_returns_error_when_end_occurs_twice() {
        // Input: BEGIN a := 5 END END.
        let tokens =
            vec![begin!(), identifier!("a"), assign!(), integer_lit!(5), end!(), end!(), dot!()];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.program(&mut ast).is_err());
    }

    #[test]
    fn parser_compound_statement_parses_nested_compound_statement() {
        // Input: BEGIN BEGIN a := 5 END END
        let tokens =
            vec![begin!(), begin!(), identifier!("a"), assign!(), integer_lit!(5), end!(), end!()];
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

    // statement_list : statement (SEMICOLON statement)*
    //      statement -> PASS: STMT-LIST.1
    //      <nothing> -> PASS: STMT-LIST.2
    //      statement statement -> FAIL: STMT-LIST.3
    //      statement SEMICOLON statement -> PASS: STMT-LIST.4
    //      statement SEMICOLON statement SEMICOLON statement -> PASS: STMT-LIST.5
    //      statement SEMICOLON -> PASS: STMT-LIST.6
    //      statement SEMICOLON statement statement -> FAIL: STMT-LIST.7

    #[test]
    // STMT-LIST.1
    fn parser_statement_list_returns_assignment_statement_if_statement_is_assignment() {
        // Input: a := 5
        let tokens = vec![identifier!("a"), assign!(), integer_lit!(5)];
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
    // STMT-LIST.2
    fn parser_statement_list_parses_empty_input() {
        // Input:
        let tokens = vec![];
        let (parser, mut ast) = setup_from(tokens);

        let statement_list = parser.statement_list(&mut ast).unwrap();
        assert!(statement_list.is_empty());
    }

    #[test]
    // STMT-LIST.3
    fn parser_statement_list_returns_error_when_multiple_statements_not_separated_by_semicolon() {
        // Input: a := 5 b := 6
        let tokens = vec![identifier!("a"),
                          assign!(),
                          integer_lit!(5),
                          identifier!("b"),
                          assign!(),
                          integer_lit!(6)];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.compound_statement(&mut ast).is_err());
    }

    #[test]
    // STMT-LIST.4
    fn parser_statement_list_returns_two_statements_when_statements_are_separated_by_semicolon() {
        // Input: a := 5; b := 6
        let tokens = vec![identifier!("a"),
                          assign!(),
                          integer_lit!(5),
                          semicolon!(),
                          identifier!("b"),
                          assign!(),
                          integer_lit!(6)];
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
    // STMT-LIST.5
    fn parser_statement_list_returns_three_statements_when_given_three_statements() {
        // Input: a := 5; b := 6; c := 7
        let tokens = vec![identifier!("a"),
                          assign!(),
                          integer_lit!(5),
                          semicolon!(),
                          identifier!("b"),
                          assign!(),
                          integer_lit!(6),
                          semicolon!(),
                          identifier!("c"),
                          assign!(),
                          integer_lit!(7)];
        let (parser, mut ast) = setup_from(tokens);

        let statements = parser.statement_list(&mut ast).unwrap();
        assert_eq!(statements.len(), 3);
    }

    #[test]
    // STMT-LIST.6
    fn parser_statement_list_can_end_with_semicolon() {
        // Input: b := 6;
        let tokens = vec![identifier!("b"), assign!(), integer_lit!(6), semicolon!()];
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
    // STMT-LIST.7
    fn parser_statement_list_returns_error_when_statements_not_separated_by_semicolon() {
        // Input: a := 5; b := 6 c := 7
        let tokens = vec![identifier!("a"),
                          assign!(),
                          integer_lit!(5),
                          semicolon!(),
                          identifier!("b"),
                          assign!(),
                          integer_lit!(6),
                          identifier!("c"),
                          assign!(),
                          integer_lit!(7)];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.compound_statement(&mut ast).is_err());
    }

    #[test]
    fn parser_statement_list_returns_only_first_stmt_when_stmts_are_not_separated_by_semicolon() {
        // Input: a := 5 b := 6
        let tokens = vec![identifier!("a"),
                          assign!(),
                          integer_lit!(5),
                          identifier!("b"),
                          assign!(),
                          integer_lit!(6)];
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
        let tokens = vec![semicolon!(), identifier!("b"), assign!(), integer_lit!(6)];
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

    // statement : (compound_statement | assignment_statement)?
    //      <nothing> -> PASS: STMT.1
    //      compound_statement -> PASS: STMT.2
    //      assignment_statement -> PASS: STMT.3
    //      compound_statement assignment_statement -> FAIL: STMT.4

    #[test]
    // STMT.1
    fn parser_statement_returns_none_if_no_statement_is_present() {
        // Input:
        let tokens = vec![];
        let (parser, mut ast) = setup_from(tokens);

        let result = parser.statement(&mut ast).unwrap();
        assert_eq!(result, None);
    }

    #[test]
    // STMT.2
    fn parser_statement_returns_compound_statement_if_statement_is_compound_statement() {
        // Input: BEGIN END
        let tokens = vec![begin!(), end!()];
        let (parser, mut ast) = setup_from(tokens);

        let statement_index = parser.statement(&mut ast).unwrap().unwrap();
        let statement_node = ast.get_node(statement_index);
        let children = statement_node.get_children();
        assert!(children.is_empty());
    }

    #[test]
    // STMT.3
    fn parser_statement_returns_assignment_statement_if_statement_is_assignment_statement() {
        // Input: a := 5
        let tokens = vec![identifier!("a"), assign!(), integer_lit!(5)];
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
    // STMT.4
    fn parser_statement_returns_error_when_both_statement_types_are_not_separated_by_semicolon() {
        // Input: BEGIN END a := 5.
        let tokens = vec![begin!(), end!(), identifier!("a"), assign!(), integer_lit!(5), dot!()];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.program(&mut ast).is_err());
    }

    // assignment_statement : variable ASSIGN expr
    //      variable ASSIGN expr -> PASS: ASSIGN.1
    //      ASSIGN expr -> FAIL: ASSIGN.2
    //      variable variable ASSIGN expr -> FAIL: ASSIGN.3
    //      variable expr -> FAIL: ASSIGN.4
    //      variable ASSIGN ASSIGN expr -> FAIL: ASSIGN.5
    //      variable ASSIGN -> FAIL: ASSIGN.6
    //      variable ASSIGN expr expr -> FAIL: ASSIGN.7

    #[test]
    // ASSIGN.1
    fn parser_assignment_statement_parses_assignment_statement() {
        // Input: a := 5
        let tokens = vec![identifier!("a"), assign!(), integer_lit!(5)];
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
    // ASSIGN.2
    fn parser_assignment_statement_returns_error_when_missing_variable() {
        // Input: := 5
        let tokens = vec![assign!(), integer_lit!(5)];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.assignment_statement(&mut ast).is_err());
    }

    #[test]
    // ASSIGN.3
    fn parser_assignment_statement_returns_error_when_two_variables_on_lhs() {
        // Input: a b := 5
        let tokens = vec![identifier!("a"), identifier!("b"), assign!(), integer_lit!(5)];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.assignment_statement(&mut ast).is_err());
    }

    #[test]
    // ASSIGN.4
    fn parser_assignment_statement_returns_error_when_missing_assignment_operator() {
        // Input: a 5
        let tokens = vec![identifier!("a"), integer_lit!(5)];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.assignment_statement(&mut ast).is_err());
    }

    #[test]
    // ASSIGN.5
    fn parser_assignment_statement_returns_error_when_having_two_assignment_operators() {
        // Input: a := := 5
        let tokens = vec![identifier!("a"), assign!(), assign!(), integer_lit!(5)];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.assignment_statement(&mut ast).is_err());
    }

    #[test]
    // ASSIGN.6
    fn parser_assignment_statement_doesnt_parse_assignment_without_expression_on_the_right() {
        // Input: a :=
        let tokens = vec![identifier!("a"), assign!()];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.assignment_statement(&mut ast).is_err());
    }

    #[test]
    // ASSIGN.7
    fn parser_assignment_statement_returns_error_when_two_expressions_on_rhs() {
        // Input: BEGIN a := 5 7 END
        let tokens =
            vec![begin!(), identifier!("a"), assign!(), integer_lit!(5), integer_lit!(7), end!()];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.compound_statement(&mut ast).is_err());
    }

    #[test]
    fn parser_assignment_statement_parses_assignment_statement_with_expression() {
        // Input: a := 5 + 7
        let tokens = vec![identifier!("a"), assign!(), integer_lit!(5), plus!(), integer_lit!(7)];
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
        let tokens = vec![integer_lit!(1), assign!(), integer_lit!(5)];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.assignment_statement(&mut ast).is_err());
    }

    #[test]
    fn parser_assignment_statement_doesnt_parse_assignment_without_assign_token_in_the_middle() {
        // Input: a + 5
        let tokens = vec![identifier!("a"), plus!(), integer_lit!(5)];
        let (parser, mut ast) = setup_from(tokens);

        assert!(parser.assignment_statement(&mut ast).is_err());
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
        let tokens = vec![integer_lit!(5)];
        let (parser, mut ast) = setup_from(tokens);

        let result = parser.variable(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    // expr -> INTEGER OPERATOR INTEGER
    fn parser_expr_should_create_operator_node_when_expression_is_addition() {
        // Input: 3+4
        let tokens = vec![integer_lit!(3), plus!(), integer_lit!(4)];
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
        let tokens = vec![integer_lit!(4), minus!(), integer_lit!(3)];
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
        let tokens = vec![integer_lit!(4), plus!(), minus!()];
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
        let tokens = vec![integer_lit!(1), plus!(), integer_lit!(3), int_div!()];
        let (parser, mut ast) = setup_from(tokens);

        let result = parser.expr(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_expr_should_create_integer_node_if_input_consists_of_only_integer() {
        // Input: 42
        let tokens = vec![integer_lit!(42)];
        let (parser, mut ast) = setup_from(tokens);

        let index = parser.expr(&mut ast).unwrap();
        verify_node(&ast, index, None, TokenValue::Integer(42));
    }

    #[test]
    fn parser_term_should_create_operator_node_when_expression_is_multiplication() {
        // Input: 3*4
        let tokens = vec![integer_lit!(3), times!(), integer_lit!(4)];
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
        let tokens = vec![integer_lit!(4), int_div!(), integer_lit!(2)];
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
        let tokens = vec![integer_lit!(42)];
        let (parser, mut ast) = setup_from(tokens);

        let index = parser.term(&mut ast).unwrap();
        verify_node(&ast, index, None, TokenValue::Integer(42));
    }

    #[test]
    fn parser_term_should_not_parse_expressions_that_dont_have_integer_after_operator() {
        // Input: 4*div
        let tokens = vec![integer_lit!(4), times!(), int_div!()];
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
        let tokens = vec![integer_lit!(1), times!(), integer_lit!(3), int_div!()];
        let (parser, mut ast) = setup_from(tokens);

        let result = parser.term(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_factor_should_return_integer_node_if_input_consists_of_only_integer() {
        // Input: 42
        let tokens = vec![integer_lit!(42)];
        let (parser, mut ast) = setup_from(tokens);

        let index = parser.factor(&mut ast).unwrap();
        verify_node(&ast, index, None, TokenValue::Integer(42));
    }

    #[test]
    fn parser_factor_creates_graph_of_expr_if_input_consists_of_expr_in_parentheses() {
        // Input: (6+3)
        let tokens = vec![lparen!(), integer_lit!(6), plus!(), integer_lit!(3), rparen!()];
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
        let tokens = vec![lparen!(), integer_lit!(6), rparen!()];
        let (parser, mut ast) = setup_from(tokens);

        let index = parser.factor(&mut ast).unwrap();
        verify_node(&ast, index, None, TokenValue::Integer(6));
    }

    #[test]
    fn parser_factor_creates_unary_operator_node_if_input_consists_of_unary_minus() {
        // Input: -5
        let tokens = vec![minus!(), integer_lit!(5)];
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
        let tokens = vec![plus!(), integer_lit!(5)];
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
        let tokens = vec![times!(), integer_lit!(5)];
        let (parser, mut ast) = setup_from(tokens);

        let result = parser.factor(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_factor_returns_error_if_input_consists_of_unary_division() {
        // Input: div 5
        let tokens = vec![int_div!(), integer_lit!(5)];
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
        let tokens = vec![lparen!(), integer_lit!(6), plus!(), rparen!()];
        let (parser, mut ast) = setup_from(tokens);

        let result = parser.factor(&mut ast);
        assert!(result.is_err());
    }

    #[test]
    fn parser_factor_returns_error_if_parentheses_are_mismatched() {
        // Input: (6+3
        let tokens = vec![lparen!(), integer_lit!(6), plus!(), integer_lit!(3)];
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
}
