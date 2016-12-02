#[derive(Debug)]
pub struct SyntaxError {
    pub msg: String,
    pub position: (usize, usize),
}
