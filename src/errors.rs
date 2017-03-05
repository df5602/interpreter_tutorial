//! This module contains error definitions.

use leftpad::left_pad;
use unicode_width::UnicodeWidthChar;

use tokens::Span;

/// Defines a syntax error.
#[derive(Debug)]
pub struct SyntaxError {
    /// The error message
    pub msg: String,
    /// The position in the input stream where the error occurred
    pub span: Span,
}

// Prints error in the following format:
// Error in line 1: Division by zero
//  |
// 1| a := 1 div 0
//  |      ^^^^^^^
pub fn print_error(input: &str, e: &SyntaxError) {
    let mut last_newline_byte = 0; // Byte offset of character after most recent newline found in input stream
    let mut last_newline_n = 0; // Character offset of character after most recent newline found in input stream
    let mut newline_found = false; /* Gets set, when newline character(s) has been found.
                                      Gets reset at the next (non-newline) character. */
    let mut line = 1; // Current line number in input stream
    let mut start_byte = 0; // Byte offset of start of the first line that has to be printed
    let mut start_n = 0; // Character offset of start of the first line that has to be printed
    let mut start_line = 0; // Line number of first line that has to be printed
    let mut end_byte = 0; // Byte offset of first newline character after part that has to be printed
    let mut end_reached = false; // End of part that has to be printed has been reached
    let mut last_non_nl_byte = 0; // Byte offset of most recent non-newline character found in input stream

    let mut preline = true;

    // Empty strings are annoying, replace with something with less edge cases..
    let tmp: String;
    let mut input = input; // Shadow input
    if input.is_empty() {
        tmp = " ".to_string();
        input = &tmp;
        preline = false;
    }

    // Check whether last character is a newline character, if that is the case, truncate
    let mut last_char = input.len() - 1;
    let mut last_bad = last_char + 1;
    loop {
        while !input.is_char_boundary(last_char) {
            last_char -= 1;
        }
        if &input[last_char..last_bad] != "\n" && &input[last_char..last_bad] != "\r" {
            break;
        } else {
            if last_char == 0 {
                last_newline_byte = last_bad; // Hack ^ 2 :-/
                break;
            }
            last_bad = last_char;
            last_char -= 1;
        }
    }

    // Iterate over input stream and calculate start and end positions of part that has to be printed
    for (i, ch) in input[0..last_bad].char_indices().enumerate() {
        // If current character is a newline character, update position of most recent line break,
        // and update current line number. Abort early, when end of the part that has to be printed
        // has been reached.
        if ch.1 == '\n' || ch.1 == '\r' {
            newline_found = true;
            if ch.1 == '\n' {
                line += 1;
            }
            if end_reached {
                end_byte = last_non_nl_byte;
                break;
            }
        } else if newline_found {
            last_newline_byte = ch.0;
            last_non_nl_byte = ch.0;
            last_newline_n = i;
            newline_found = false;
        } else {
            last_non_nl_byte = ch.0;
        }

        // Record start and end positions of part that has to be printed.
        if i == e.span.start {
            start_byte = last_newline_byte;
            start_n = last_newline_n;
            start_line = line;
        }
        if i == e.span.end - 1 {
            end_reached = true;
        }
    }

    // Handle case where start position is at the end of the input stream
    if e.span.start + 1 > input.chars().count() {
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
            if ch.is_whitespace() && preline {
                marker.push(ch);
            } else {
                let mut width = match UnicodeWidthChar::width(ch) {
                    Some(width) => width,
                    None => 0,
                };
                if width == 0 {
                    if preline {
                        print!(" "); // Avoid "swallowing" of the padding space by combining character
                    }
                    if i < e.span.end - start_n {
                        marker.pop();
                    }
                    width = 1;
                }
                let glyph = if i >= e.span.start - start_n && i < e.span.end - start_n {
                    '^'
                } else {
                    ' '
                };
                for _ in 0..width {
                    marker.push(glyph);
                }
                preline = false;
            }
            print!("{}", ch);
        } else {
            println!("\n{}| {}", left_pad("", line_no_length), marker);
            marker.clear();
            preline = true;
            line += 1;
            print!("{}| ", left_pad(&line.to_string(), line_no_length));
        }
    }
    if idx < e.span.end - 1 - start_n {
        marker.push('^');
    }
    println!("\n{}| {}", left_pad("", line_no_length), marker);
}