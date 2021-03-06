macro_rules! int_node {
    ($ast:expr, $value:expr) => {{
        let node = NumberNode::new(Value::Integer($value), 
                                   Token::new(TokenType::IntegerLiteral, 
                                              Some(TokenValue::Integer($value)), 
                                              Span::default()));
        $ast.add_node(node)
    }}
}

macro_rules! real_node {
    ($ast:expr, $value:expr) => {{
        let node = NumberNode::new(Value::Real($value), 
                                   Token::new(TokenType::RealLiteral, 
                                              Some(TokenValue::Real($value)), 
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

macro_rules! type_node {
    ($ast:expr, $type_spec:expr) => {{
        let node = TypeNode::new($type_spec,
                                 Token::new(TokenType::TypeSpecifier,
                                            Some(TokenValue::Type($type_spec)),
                                            Span::default()));
        $ast.add_node(node)
    }}
}

macro_rules! var_decl_node {
    ($ast:expr, $var_name:expr, $type_spec:expr) => {{
        let node = VariableDeclNode::new($var_name, $type_spec);
        $ast.add_node(node)
    }}
}

macro_rules! program_node {
    ($ast:expr, $name:expr, $variable:expr, $block:expr) => {{
        let node = ProgramNode::new($name.to_string(), $variable, $block);
        $ast.add_node(node)
    }}
}