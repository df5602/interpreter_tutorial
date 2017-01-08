use std::io;
use std::io::{Read, BufRead, Write};
use std::error::Error;
use std::path::Path;
use std::fs::File;
use std::env;

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

fn read_from_file(path: &str) -> Result<String, String> {
    let path = Path::new(path);
    let file_res = File::open(&path);
    if file_res.is_err() {
        return Err(format!("Couldn't open {}: {}",
                           path.display(),
                           file_res.unwrap_err().description()));
    }
    let mut file = file_res.unwrap();

    let mut s = String::new();
    match file.read_to_string(&mut s) {
        Err(why) => Err(format!("Couldn't read {}: {}", path.display(), why.description())),
        Ok(_) => Ok(s),
    }
}

fn evaluate(input: &str) {
    let lexer = PascalLexer::new(input);
    let parser = Parser::new(lexer);
    let mut ast = Ast::new();

    // Parse input
    match parser.parse(&mut ast) {
        Ok(_) => {}
        Err(e) => {
            print_error(input, e);
            return;
        }
    }

    // Evaluate input
    let interpreter = Interpreter::new(&ast);
    match interpreter.interpret() {
        Ok(_) => interpreter.print_symbols(),
        Err(e) => print_error(input, e),
    }
}

fn run_repl() {
    let stdin = io::stdin();

    print_preamble();
    for line in stdin.lock().lines() {
        match line {
            Ok(line) => evaluate(&line),
            Err(error) => {
                println!("error: {}", error);
                panic!();
            }
        }
        print_preamble();
    }
}

fn run_file(path: &str) {
    let input: String;
    match read_from_file(path) {
        Ok(s) => input = s,
        Err(e) => {
            println!("{}", e);
            return;
        }
    };

    evaluate(&input);
}

fn main() {
    let args: Vec<String> = env::args().collect();

    match args.len() {
        1 => run_repl(),
        2 => run_file(&args[1]),
        _ => {
            println!("To start REPL mode, call me with no arguments.\n\
                     To evaluate input from a file, pass the path of the file as argument")
        }
    }
}
