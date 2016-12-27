use std::io;
use std::io::{BufRead, Write};

pub mod tokens;
mod ast;
pub mod errors;
pub mod lexer;
mod parser;
mod interpreter;

use ast::Ast;
use errors::SyntaxError;
use lexer::PascalLexer;
use parser::Parser;
use interpreter::Interpreter;

#[allow(unused_must_use)]
fn print_preamble() {
    let stdout = io::stdout();

    stdout.lock().write(b"interpreter> ");
    stdout.lock().flush();
}

// Prints error in the following format:
// Error parsing input: msg
// >>> 3?5
// >>>  ^
fn print_error(input: &str, e: SyntaxError) {
    let s = std::iter::repeat(" ").take(e.position.0).collect::<String>();
    let m = std::iter::repeat("^").take(e.position.1 - e.position.0).collect::<String>();

    println!("Error evaluating input: {}", e.msg);
    println!(">>> {}", input);
    println!(">>> {}{}", s, m);
}

fn main() {
    let stdin = io::stdin();

    print_preamble();
    for line in stdin.lock().lines() {
        match line {
            Ok(_) => {
                let input = line.unwrap();
                let lexer = PascalLexer::new(&input);
                let parser = Parser::new(lexer);
                let mut ast = Ast::new();

                // Parse input
                match parser.parse(&mut ast) {
                    Ok(_) => {}
                    Err(e) => {
                        print_error(&input, e);
                        print_preamble();
                        continue;
                    }
                }

                // Evaluate input
                let interpreter = Interpreter::new(&ast);
                match interpreter.interpret() {
                    Ok(result) => println!("{}", result),
                    Err(e) => print_error(&input, e),
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
mod integration_tests {
    use ast::Ast;
    use lexer::PascalLexer;
    use parser::Parser;
    use interpreter::Interpreter;

    #[test]
    fn parser_should_parse_expressions_that_contain_multi_digit_integer() {
        let input = "44+3".to_string();
        let lexer = PascalLexer::new(&input);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        let result = parser.parse(&mut ast);
        assert!(result.is_ok());
        let interpreter = Interpreter::new(&ast);
        let result_i = interpreter.interpret();
        assert_eq!(47, result_i.unwrap());
    }

    #[test]
    fn parser_should_parse_expressions_that_contain_whitespace_characters() {
        let input = "2 + 3".to_string();
        let lexer = PascalLexer::new(&input);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        let result = parser.parse(&mut ast);
        assert!(result.is_ok());
        let interpreter = Interpreter::new(&ast);
        let result_i = interpreter.interpret();
        assert_eq!(5, result_i.unwrap());
    }

    #[test]
    fn parser_should_parse_expressions_that_begin_with_whitespace_characters() {
        let input = " 2 + 3".to_string();
        let lexer = PascalLexer::new(&input);
        let parser = Parser::new(lexer);
        let mut ast = Ast::new();
        let result = parser.parse(&mut ast);
        assert!(result.is_ok());
        let interpreter = Interpreter::new(&ast);
        let result_i = interpreter.interpret();
        assert_eq!(5, result_i.unwrap());
    }
}
