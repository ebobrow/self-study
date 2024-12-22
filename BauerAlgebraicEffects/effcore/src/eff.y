%start Comp
%%
Ident -> Result<Ident, ()>: 'IDENT' { Ok(Ident($span)) };

Comp -> Result<Comp, ()>:
    'RETURN' Value
        { Ok(Comp::Ret(Box::new($2?))) }
    | Ident '(' Value ';' Ident '.' Comp ')'
        { Ok(Comp::Op { name: $1?, param: Box::new($3?), ret: $5?, cont: Box::new($7?) }) }
    | 'DO' Ident '<-' Comp 'IN' Comp
        { Ok(Comp::Do($2?, Box::new($4?), Box::new($6?))) }
    | 'IF' Value 'THEN' Comp 'ELSE' Comp
        { Ok(Comp::If(Box::new($2?), Box::new($4?), Box::new($6?))) }
    | Value Value
        { Ok(Comp::App(Box::new($1?), Box::new($2?))) }
    | 'WITH' Value 'HANDLE' Comp
        { Ok(Comp::Handle(Box::new($2?), Box::new($4?))) }
    ;

Value -> Result<Value, ()>:
    Ident
        { Ok(Value::Var($1?)) }
    | 'TRUE'
        { Ok(Value::True) }
    | 'FALSE'
        { Ok(Value::False) }
    | 'FUN' Ident '|->' Comp
        { Ok(Value::Fun($2?, Box::new($4?))) }
    | Handler
        { Ok(Value::Handler($1?)) }
    ;

Handler -> Result<Handler, ()>:
    'HANDLER' '{' RetHandle OpHandles '}' { Ok(Handler { ret: $3?, ops: $4? }) }
    | 'HANDLER' '{' FirstOpHandle OpHandles '}' {
        let mut list = $4?;
        list.push_front($3?);
        Ok(Handler { ret: None, ops: list })
    }
    ;

RetHandle -> Result<Option<(Ident, Comp)>, ()>:
    'RETURN' Ident '|->' Comp { Ok(Some(($2?, $4?))) }
    ;

OpHandles -> Result<LinkedList<OpHandle>, ()>:
    ',' Ident '(' Ident ';' Ident ')' '|->' Comp OpHandles {
        let mut list = $10?;
        list.push_front(OpHandle {name: $2?, param: $4?, continuation: $6?, handle: $9? });
        Ok(list)
    }
    | { Ok(LinkedList::new()) }
    ;

FirstOpHandle -> Result<OpHandle, ()>:
    Ident '(' Ident ';' Ident ')' '|->' Comp
        { Ok(OpHandle {name: $1?, param: $3?, continuation: $5?, handle: $8?}) }
    ;
%%

use cfgrammar::Span;
use std::collections::LinkedList;

#[derive(Debug, Clone)]
pub enum Comp {
    Ret(Box<Value>),
    Op {
        name: Ident,
        param: Box<Value>,
        /// variable bound in continuation
        ret: Ident,
        cont: Box<Comp>,
    },
    Do(Ident, Box<Comp>, Box<Comp>),
    If(Box<Value>, Box<Comp>, Box<Comp>),
    App(Box<Value>, Box<Value>),
    Handle(Box<Value>, Box<Comp>),
}

#[derive(Debug, Clone)]
pub enum Value {
    Var(Ident),
    True,
    False,
    Fun(Ident, Box<Comp>),
    Handler(Handler),
}

#[derive(Debug, Clone)]
pub struct Handler {
    /// return $span |-> c
    pub ret: Option<(Ident, Comp)>,
    pub ops: LinkedList<OpHandle>,
}

#[derive(Debug, Clone)]
pub struct OpHandle {
    pub name: Ident,
    pub param: Ident,
    pub continuation: Ident,
    pub handle: Comp,
}

#[derive(Debug, Clone)]
pub struct Ident(pub Span);
