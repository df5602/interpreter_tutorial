use std::io;
use std::io::{BufRead, Write};

mod tokens;
mod ast;
mod errors;
mod lexer;
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
                    Ok(_) => interpreter.print_symbols(),
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
