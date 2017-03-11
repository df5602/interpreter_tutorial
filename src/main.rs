#![cfg_attr(feature = "benchmarks", feature(test))]

#![cfg_attr(feature = "fuzzing", feature(question_mark))]
#![cfg_attr(feature = "fuzzing", feature(plugin))]
#![cfg_attr(feature = "fuzzing", plugin(afl_plugin))]

use std::io;
use std::io::{Read, BufRead, Write};
use std::error::Error;
use std::path::Path;
use std::fs::File;
use std::env;

extern crate leftpad;
extern crate unicode_width;

#[cfg(feature = "fuzzing")]
extern crate afl;

#[cfg(feature = "benchmarks")]
extern crate test;

mod tokens;
mod ast;
mod errors;
mod lexer;
mod parser;
mod interpreter;

use ast::Ast;
use errors::{SyntaxError, print_error};
use tokens::Span;
use lexer::PascalLexer;
use parser::Parser;
use interpreter::Interpreter;

#[allow(unused_must_use)]
fn print_preamble() {
    let stdout = io::stdout();

    stdout.lock().write(b"interpreter> ");
    stdout.lock().flush();
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

#[allow(unknown_lints)]
#[allow(needless_pass_by_value)]
fn sanitize_input(input: String) -> Result<String, (String, SyntaxError)> {
    let mut sanitized = String::with_capacity(input.len());

    let mut first_index = None;
    let mut char_len = 0;
    let mut added_chars = 0;
    let mut last_char = '\0';

    let mut iter = input.chars().enumerate().peekable();

    while let Some((i, ch)) = iter.next() {
        if ch.is_control() && ch != '\n' && ch != '\r' && ch != '\t' {
            let mut len = 0;
            for esc in ch.escape_default() {
                sanitized.push(esc);
                len += 1;
            }
            match first_index {
                Some(_) => {}
                None => {
                    first_index = Some(i + added_chars);
                    char_len = len;
                }
            }
        } else if ch == '\t' {
            sanitized.push_str("    ");
            // one \t is replaced by space, the other 3 spaces are extra:
            added_chars += 3;
        } else if ch == '\r' {
            if last_char != '\n' && iter.peek().unwrap_or(&(0usize, '\0')).1 != '\n' {
                sanitized.push('\n');
                println!("Replaced solitary CR character with LF character at position {}",
                         i);
            }
        } else {
            sanitized.push(ch);
        }
        last_char = ch;
    }

    match first_index {
        Some(i) => {
            Err((sanitized,
                 SyntaxError {
                     msg: "Input cannot contain control characters (except LF, CR and TAB)"
                         .to_string(),
                     span: Span::new(i, i + char_len),
                 }))
        }
        None => Ok(sanitized),
    }
}

fn evaluate(input: String) {
    let sanitized: String;
    match sanitize_input(input) {
        Ok(s) => sanitized = s,
        Err((s, e)) => {
            print_error(&s, &e);
            return;
        }
    }

    let lexer = PascalLexer::new(&sanitized);
    let parser = Parser::new(lexer);
    let mut ast = Ast::new();

    // Parse input
    match parser.parse(&mut ast) {
        Ok(_) => {}
        Err(e) => {
            print_error(&sanitized, &e);
            return;
        }
    }

    // Evaluate input
    let interpreter = Interpreter::new(&ast);
    match interpreter.interpret() {
        Ok(_) => interpreter.print_symbols(),
        Err(e) => print_error(&sanitized, &e),
    }
}

fn run_repl() {
    let stdin = io::stdin();

    print_preamble();
    for line in stdin.lock().lines() {
        match line {
            Ok(line) => evaluate(line),
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

    evaluate(input);
}

#[cfg(not(feature = "fuzzing"))]
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

#[cfg(feature = "fuzzing")]
fn main() {
    afl::handle_string(|s| { evaluate(s); })
}