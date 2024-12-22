pub enum Token {
    True,
    False,
    Fun,
    Return,
    Do,
    In,
    If,
    Then,
    Else,
    With,
    Handle,
    Handler,

    MapsTo,
    LeftArrow,

    Ident(String),
}

pub struct Lexer {
    src: String,
    ptr: usize,
    tokens: Vec<Token>,
}

impl Lexer {
    pub fn lex(src: String) -> Vec<Token> {
        let lexer = Lexer {
            src,
            ptr: 0,
            tokens: Vec::new(),
        };
        lexer.tokens
    }
}
