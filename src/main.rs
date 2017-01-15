use std::io;
use std::io::{Read, BufRead, Write};
use std::error::Error;
use std::path::Path;
use std::fs::File;
use std::env;

extern crate leftpad;
use leftpad::left_pad;

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
// Error in line 1: Division by zero
//  |
// 1| a := 1 div 0
//  |      ^^^^^^^
fn print_error(input: &str, e: SyntaxError) {
    let mut last_newline_byte = 0;  // Byte offset of character after most recent newline found in input stream
    let mut last_newline_n = 0;     // Character offset of character after most recent newline found in input stream
    let mut newline_found = false;  // Gets set, when newline character(s) has been found.
                                    // Gets reset at the next (non-newline) character.
    let mut line = 1;               // Current line number in input stream
    let mut start_byte = 0;         // Byte offset of start of the first line that has to be printed
    let mut start_n = 0;            // Character offset of start of the first line that has to be printed
    let mut start_line = 0;         // Line number of first line that has to be printed
    let mut end_byte = 0;           // Byte offset of first newline character after part that has to be printed
    let mut end_reached = false;    // End of part that has to be printed has been reached
    let mut last_non_nl_byte = 0;   // Byte offset of most recent non-newline character found in input stream

    // Iterate over input stream and calculate start and end positions of part that has to be printed
    for (i, ch) in input.char_indices().enumerate() {
        // If current character is a newline character, update position of most recent line break,
        // and update current line number. Abort early, when end of the part that has to be printed
        // has been reached.
        if ch.1 == '\n' || ch.1 == '\r' {
            newline_found = true;
            if end_reached {
                end_byte = last_non_nl_byte;
                break;
            }
        } else if newline_found {
            last_newline_byte = ch.0;
            last_non_nl_byte = ch.0;
            last_newline_n = i;
            line += 1;
            newline_found = false;
        } else {
            last_non_nl_byte = ch.0;
        }

        // Record start and end positions of part that has to be printed.
        if i == e.position.0 {
            start_byte = last_newline_byte;
            start_n = last_newline_n;
            start_line = line;
        } else if i == e.position.1 - 1 {
            end_reached = true;
        }
    }

    // Handle case where start position is at the end of the input stream
    if e.position.0 + 1 > input.len() {
        start_byte = last_newline_byte;
        start_n = last_newline_n;
        start_line = line;
    }

    // Handle case where end position is at the end of the input stream
    if end_byte == 0 {
        end_byte = last_non_nl_byte;
    }

    // Line number stored in `line` is the largest line number that has been encountered.
    // Therefore all printed line numbers have to be padded left to be of equal length as
    // this line number.
    let line_no_length = line.to_string().len();

    println!("Error in line {}: {}", start_line, e.msg);
    println!("{}| ", left_pad("", line_no_length));

    let mut marker = "".to_string();
    let mut preline = true;
    line = start_line;

    print!("{}| ", left_pad(&line.to_string(), line_no_length));

    // Ranges are of type [start...end), to get inclusive range, end has to be
    // incremented by 1. However, due to UTF-8, we do not know by many bytes to increment
    // the end position.
    end_byte += 1;
    while !input.is_char_boundary(end_byte) {
        end_byte += 1;
    }

    // Iterate over part of the input to be printed and construct marker.
    let mut idx = 0;
    for (i, ch) in input[start_byte..end_byte].chars().enumerate() {
        idx = i;
        if ch != '\n' && ch != '\r' {
            print!("{}", ch);
            if ch.is_whitespace() && preline {
                marker.push(ch);
            } else {
                if i >= e.position.0 - start_n && i < e.position.1 - start_n {
                    marker.push('^');
                } else {
                    marker.push(' ');
                }
                preline = false;
            }
        } else {
            println!("\n{}| {}", left_pad("", line_no_length), marker);
            marker.clear();
            preline = true;
            line += 1;
            print!("{}| ", left_pad(&line.to_string(), line_no_length));
        }
    }
    if idx < e.position.1 - start_n {
        marker.push('^');
    }
    println!("\n{}| {}", left_pad("", line_no_length), marker);
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
