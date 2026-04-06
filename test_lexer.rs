fn main() {
    use tinycic::parser::lexer::{Lexer, Token};
    
    let input = "def zero : Real := ofRat Rat.zero";
    let mut lexer = Lexer::new(input);
    
    loop {
        let tok = lexer.next_token();
        println!("{:?}", tok);
        if let Token::Eof = tok { break; }
    }
}
