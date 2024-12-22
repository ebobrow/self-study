use std::io::{self, BufRead, Write};

use interp::Interpreter;
use lrlex::lrlex_mod;
use lrpar::lrpar_mod;

lrlex_mod!("eff.l");
lrpar_mod!("eff.y");

pub use eff_y::{Comp, Handler, Ident, OpHandle, Value};

mod interp;

fn main() {
    let lexerdef = eff_l::lexerdef();
    let stdin = io::stdin();
    loop {
        print!(">>> ");
        io::stdout().flush().ok();
        match stdin.lock().lines().next() {
            Some(Ok(ref l)) => {
                if l.trim().is_empty() {
                    continue;
                }
                let lexer = lexerdef.lexer(l);
                let (res, errs) = eff_y::parse(&lexer);
                for e in errs {
                    println!("{}", e.pp(&lexer, &eff_y::token_epp));
                }
                if let Some(Ok(r)) = res {
                    let res = Interpreter::interp(r, &lexer).unwrap();
                    println!("{res:?}");
                }
            }
            _ => break,
        }
    }
}
