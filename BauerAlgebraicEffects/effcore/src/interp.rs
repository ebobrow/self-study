use std::collections::HashMap;

use cfgrammar::Span;
use lrlex::{DefaultLexerTypes, LRNonStreamingLexer};
use lrpar::NonStreamingLexer;

use crate::{Comp, Handler, Ident, OpHandle, Value};

pub struct Interpreter<'input, 'lexer> {
    // TODO: wish this didn't have to be owned value...
    vars: HashMap<&'input str, Value>,
    lexer: &'lexer LRNonStreamingLexer<'lexer, 'input, DefaultLexerTypes>,
    handlers: Vec<Handler>,
    /// how many handlers to ignore
    nesting_level: usize,
}

impl<'input, 'lexer> Interpreter<'input, 'lexer> {
    pub fn interp(
        comp: Comp,
        lexer: &'lexer LRNonStreamingLexer<'lexer, 'input, DefaultLexerTypes>,
    ) -> Result<Value, String> {
        let mut interpreter = Interpreter {
            vars: HashMap::new(),
            handlers: Vec::new(),
            nesting_level: 0,
            lexer,
        };

        interpreter.interp_comp(comp)
    }

    fn interp_comp(&mut self, comp: Comp) -> Result<Value, String> {
        match comp {
            Comp::Ret(v) => {
                if let Some((var, comp, i)) = self.find_ret_handle() {
                    let old_nesting = self.nesting_level;
                    self.nesting_level = i;
                    let old_var = self.vars.insert(var, *v);
                    let res = self.interp_comp(comp)?;
                    if let Some(old_var) = old_var {
                        self.vars.insert(var, old_var);
                    } else {
                        self.vars.remove(var);
                    }
                    self.nesting_level = old_nesting;
                    Ok(res)
                } else {
                    Ok(self.interp_value(&v)?)
                }
            }
            Comp::Op {
                name: Ident(name),
                param,
                ret,
                cont,
            } => {
                if let Some((param_name, cont_name, handle)) = self.find_op_handle(&name) {
                    let old_param = self.vars.insert(param_name, *param.clone());
                    let old_cont = self
                        .vars
                        .insert(cont_name, Value::Fun(ret.clone(), Box::new(*cont.clone())));

                    let res = self.interp_comp(handle.clone())?;

                    if let Some(old_param) = old_param {
                        self.vars.insert(param_name, old_param);
                    } else {
                        self.vars.remove(param_name);
                    }
                    if let Some(old_cont) = old_cont {
                        self.vars.insert(cont_name, old_cont);
                    } else {
                        self.vars.remove(cont_name);
                    }

                    Ok(res)
                } else {
                    // TODO: later would add stdlib/primitives for e.g. print
                    Err(format!(
                        "no handler found for `{}`",
                        self.lexer.span_str(name)
                    ))
                }
            }
            Comp::Do(Ident(x), c1, c2) => {
                let c1_out = self.interp_comp(*c1)?;
                let x = self.lexer.span_str(x);
                let oldx = self.vars.insert(x, c1_out.clone());
                let c2_out = self.interp_comp(*c2)?;
                if let Some(oldx) = oldx {
                    self.vars.insert(x, oldx);
                } else {
                    self.vars.remove(x);
                }
                Ok(c2_out)
            }
            Comp::If(cond, c1, c2) => match *cond {
                Value::True => self.interp_comp(*c1),
                Value::False => self.interp_comp(*c2),
                _ => Err(format!(
                    "invalid `if` condition; expected bool type but got {:?}",
                    cond
                )),
            },
            Comp::App(v1, v2) => {
                if let Value::Fun(Ident(x), c) = self.interp_value(&v1)? {
                    let x = self.lexer.span_str(x);
                    let oldx = self.vars.insert(x, self.interp_value(&v2)?);
                    let c_out = self.interp_comp(*c)?;
                    if let Some(oldx) = oldx {
                        self.vars.insert(x, oldx);
                    } else {
                        self.vars.remove(x);
                    }
                    Ok(c_out)
                } else {
                    Err(format!(
                        "invalid application; expected fun type but got {:?}",
                        v1
                    ))
                }
            }
            Comp::Handle(h, c) => {
                if let Value::Handler(h) = *h {
                    self.handlers.push(h);
                    self.interp_comp(*c)
                } else {
                    Err(format!(
                        "invalid handler; expected handler type but got {:?}",
                        h
                    ))
                }
            }
        }
    }

    fn interp_value(&self, value: &Value) -> Result<Value, String> {
        if let Value::Var(Ident(var_name)) = value {
            let var_name = self.lexer.span_str(*var_name);
            if let Some(val) = self.vars.get(var_name) {
                Ok(val.clone())
            } else {
                Err(format!("unknown identifier `{}`", var_name))
            }
        } else {
            Ok(value.clone())
        }
    }

    /// (y, k, h, nesting_level)
    fn find_op_handle(&self, op: &Span) -> Option<(&'input str, &'input str, Comp)> {
        let opname = self.lexer.span_str(*op);
        // Search backwards because innermost handler takes precedence
        for Handler { ops, .. } in self.handlers.iter().rev().skip(self.nesting_level) {
            for OpHandle {
                name: Ident(name),
                param: Ident(param),
                continuation: Ident(continuation),
                handle,
            } in ops
            {
                if self.lexer.span_str(*name) == opname {
                    return Some((
                        self.lexer.span_str(*param),
                        self.lexer.span_str(*continuation),
                        handle.clone(),
                    ));
                }
            }
        }
        None
    }

    fn find_ret_handle(&self) -> Option<(&'input str, Comp, usize)> {
        for (i, Handler { ret, .. }) in self
            .handlers
            .iter()
            .rev()
            .enumerate()
            .skip(self.nesting_level)
        {
            if let Some((Ident(var), comp)) = ret {
                return Some((self.lexer.span_str(*var), comp.clone(), i + 1));
            }
        }
        None
    }
}
