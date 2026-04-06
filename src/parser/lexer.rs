//! Simple lexer for .x files

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    // Keywords
    Inductive,
    Structure,
    Where,
    Namespace,
    End,
    Def,
    Theorem,
    Lemma,
    Match,
    With,
    By,
    Exact,
    Have,
    Assume,
    Intro,
    Use,
    Apply,
    Calc,

    // Identifiers
    Ident(String),

    // Symbols
    LParen,      // (
    RParen,      // )
    LBrace,      // {
    RBrace,      // }
    LBracket,    // [
    RBracket,    // ]
    Colon,       // :
    Assign,      // :=
    Equal,       // =
    Arrow,       // => or →
    Pipe,        // |
    Comma,       // ,
    Underscore,  // _
    Dot,         // .

    // Special
    Eof,
}

pub struct Lexer<'a> {
    input: &'a str,
    pos: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self { input, pos: 0 }
    }

    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace();

        if self.pos >= self.input.len() {
            return Token::Eof;
        }

        let c = self.current_char();

        // Identifiers and keywords
        if c.is_alphabetic() || c == '_' {
            return self.read_identifier();
        }

        // Symbols
        match c {
            '(' => { self.advance(); Token::LParen }
            ')' => { self.advance(); Token::RParen }
            '{' => { self.advance(); Token::LBrace }
            '}' => { self.advance(); Token::RBrace }
            '[' => { self.advance(); Token::LBracket }
            ']' => { self.advance(); Token::RBracket }
            ':' => {
                self.advance();
                if self.current_char() == '=' {
                    self.advance();
                    Token::Assign
                } else {
                    Token::Colon
                }
            }
            '|' => { self.advance(); Token::Pipe }
            ',' => { self.advance(); Token::Comma }
            '_' => { self.advance(); Token::Underscore }
            '.' => { self.advance(); Token::Dot }
            '=' => {
                self.advance();
                if self.current_char() == '>' {
                    self.advance();
                    Token::Arrow
                } else {
                    // Just =, return Equal token
                    Token::Equal
                }
            }
            '-' => {
                self.advance();
                if self.current_char() == '>' {
                    self.advance();
                    Token::Arrow
                } else {
                    Token::Ident("-".to_string())
                }
            }
            '→' => { self.advance(); Token::Arrow }
            _ => {
                // Skip unknown character
                self.advance();
                self.next_token()
            }
        }
    }

    fn current_char(&self) -> char {
        self.input[self.pos..].chars().next().unwrap_or('\0')
    }

    fn advance(&mut self) {
        if let Some(c) = self.input[self.pos..].chars().next() {
            self.pos += c.len_utf8();
        }
    }

    fn skip_whitespace(&mut self) {
        while self.pos < self.input.len() {
            let c = self.current_char();
            if c.is_whitespace() {
                self.advance();
            } else if c == '/' && self.peek() == Some('/') {
                // Skip line comment
                while self.current_char() != '\n' && self.pos < self.input.len() {
                    self.advance();
                }
            } else {
                break;
            }
        }
    }

    fn peek(&self) -> Option<char> {
        let mut chars = self.input[self.pos..].chars();
        chars.next();
        chars.next()
    }

    fn read_identifier(&mut self) -> Token {
        let start = self.pos;
        while self.pos < self.input.len() {
            let c = self.current_char();
            if c.is_alphanumeric() || c == '_' {
                self.advance();
            } else {
                break;
            }
        }

        let s = &self.input[start..self.pos];
        match s {
            "inductive" => Token::Inductive,
            "structure" => Token::Structure,
            "where" => Token::Where,
            "namespace" => Token::Namespace,
            "end" => Token::End,
            "def" => Token::Def,
            "theorem" => Token::Theorem,
            "lemma" => Token::Lemma,
            "match" => Token::Match,
            "with" => Token::With,
            "by" => Token::By,
            "exact" => Token::Exact,
            "have" => Token::Have,
            "assume" => Token::Assume,
            "intro" => Token::Intro,
            "use" => Token::Use,
            "apply" => Token::Apply,
            "calc" => Token::Calc,
            _ => Token::Ident(s.to_string()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_tokens() {
        let mut lexer = Lexer::new("inductive Nat where | zero");
        assert_eq!(lexer.next_token(), Token::Inductive);
        assert_eq!(lexer.next_token(), Token::Ident("Nat".to_string()));
        assert_eq!(lexer.next_token(), Token::Where);
        assert_eq!(lexer.next_token(), Token::Pipe);
        assert_eq!(lexer.next_token(), Token::Ident("zero".to_string()));
    }
}
