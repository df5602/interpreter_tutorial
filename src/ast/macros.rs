macro_rules! int_node {
    ($ast:expr, $value:expr) => {{
        let node = IntegerNode::new($value, 
                                    Token::new(TokenType::IntegerLiteral, 
                                               Some(TokenValue::Integer($value)), 
                                               Span::default()));
        $ast.add_node(node)
    }}
}

macro_rules! binop_node {
    ($ast:expr, $left:expr, $right:expr, $op:expr) => {{
        let node = BinaryOperatorNode::new($left, $right, $op,
                                           Token::new(TokenType::Operator,
                                                      Some(TokenValue::Operator($op)),
                                                      Span::default()));
        $ast.add_node(node)
    }}
}

macro_rules! unop_node {
    ($ast:expr, $operand:expr, $op:expr) => {{
        let node = UnaryOperatorNode::new($operand, $op,
                                          Token::new(TokenType::Operator,
                                          Some(TokenValue::Operator($op)),
                                          Span::default()));
        $ast.add_node(node)
    }}
}

macro_rules! cmpd_stmt_node {
    ($ast:expr, $statements:expr) => {{
        let node = CompoundStmtNode::new($statements,
                                         Token::new(TokenType::Begin, None, Span::default()),
                                         Token::new(TokenType::End, None, Span::default()));
        $ast.add_node(node)
    }}
}

macro_rules! var_node {
    ($ast:expr, $name:expr) => {{
        let node = VariableNode::new($name.to_string(),
                                     Token::new(TokenType::Identifier,
                                                Some(TokenValue::Identifier($name.to_string())),
                                                Span::default()));
        $ast.add_node(node)
    }}
}

macro_rules! assign_node {
    ($ast:expr, $var:expr, $expr:expr) => {{
        let node = AssignmentStmtNode::new($var, $expr,
                                           Token::new(TokenType::Assign, None, Span::default()));
        $ast.add_node(node)
    }}
}

macro_rules! block_node {
    ($ast:expr, $declarations:expr, $cmpd_stmt:expr) => {{
        let node = BlockNode::new($declarations, $cmpd_stmt);
        $ast.add_node(node)
    }}
}