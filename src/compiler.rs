use crate::{
    default_env,
    eval::{call_func, op_eval, value_to_argnames},
    lisp,
    utils::{require_arg, require_typed_arg},
    CompileError, Env, List, Symbol, Value,
};
use std::{cell::RefCell, rc::Rc};

#[derive(Clone, Debug, PartialEq)]
pub enum Opcode {
    LoadConst(Value),
    StoreName(Symbol),
    // For set
    SetName(Symbol),
    LoadName(Symbol),
    MakeList {
        element_count: usize,
    },
    CallFunction {
        arg_count: usize,
    },
    RelativeJumpIfTrue {
        offset: isize,
        //preserve_stack_if_true: bool,
    },
    RelativeJumpIfTruePreserve {
        offset: isize,
        //preserve_stack_if_false: bool,
    },
    RelativeJumpIfFalse {
        offset: isize,
        //preserve_stack_if_false: bool,
    },
    RelativeJumpIfFalsePreserve {
        offset: isize,
        //preserve_stack_if_false: bool,
    },
    RelativeJump {
        offset: isize,
    },
    TailCall {
        arg_count: usize,
    },
    MakeFunction {
        arg_count: usize,
    },
    PushEnv,
    PopEnv,
}

pub fn compile(expression: Value) -> Result<Vec<Opcode>, CompileError> {
    let compile_env = Rc::new(RefCell::new(default_env()));
    compile_inner(expression, compile_env, false)
}

pub fn compile_inner(
    expression: Value,
    compile_env: Rc<RefCell<Env>>,
    is_quoted: bool,
) -> Result<Vec<Opcode>, CompileError> {
    // TODO: Could is_quoted be separate function without is_quoted being required by compile_inner
    if is_quoted {
        match &expression {
            Value::List(list) if *list != List::NIL => match &list.car().unwrap() {
                Value::Symbol(keyword) if keyword.as_str() == "comma" => {
                    // do nothing, handle it down below
                }
                _ => {
                    let code = list
                        .into_iter()
                        .map(|el| compile_inner(el, compile_env.clone(), is_quoted))
                        .collect::<Result<Vec<Vec<Opcode>>, CompileError>>()?;
                    let len = code.len();
                    let mut code = code.into_iter().flatten().collect::<Vec<Opcode>>();
                    code.push(Opcode::MakeList { element_count: len });
                    return Ok(code);
                }
            },
            _ => {
                return Ok(vec![Opcode::LoadConst(expression)]);
            }
        }
    }

    let res = match expression {
        Value::Int(_)
        | Value::Float(_)
        | Value::String(_)
        | Value::True
        | Value::False
        | Value::List(List::NIL) => {
            vec![Opcode::LoadConst(expression)]
        }
        Value::Symbol(symbol) => vec![Opcode::LoadName(symbol)],
        Value::List(list) => {
            match &list.car().unwrap() {
                Value::Symbol(keyword) if keyword.as_str() == "quote" => {
                    vec![Opcode::LoadConst(list.cdr().car().map_err(|_| {
                        CompileError {
                            msg: "Nothing was quoted".to_owned(),
                        }
                    })?)]
                }
                Value::Symbol(keyword) if keyword.as_str() == "comma" => {
                    //vec![Opcode::LoadConst(list.cdr().car()?)]
                    let next_expression = list.cdr().car().map_err(|_| CompileError {
                        msg: format!("Expected argument to comma: {}", list),
                    })?;
                    compile_inner(next_expression, compile_env.clone(), false)?
                }
                Value::Symbol(keyword) if keyword.as_str() == "quasiquote" => {
                    let next_expression = list.cdr().car().map_err(|_| CompileError {
                        msg: format!("Expected argument to quote: {}", list),
                    })?;
                    compile_inner(next_expression, compile_env.clone(), true)?
                }
                Value::Symbol(keyword)
                    if keyword.as_str() == "define" || keyword.as_str() == "set!" =>
                {
                    //let args = &list.cdr().into_iter().collect::<Vec<Value>>();
                    let name = list.cdr().car().map_err(|_| CompileError {
                        msg: format!("No name for {}\n{}\n", keyword, list),
                    })?;
                    let subexp = list.cdr().cdr().car().map_err(|_| CompileError {
                        msg: format!("No body for {}\n{}\n", keyword, list),
                    })?;
                    let mut sub_result;
                    match name {
                        Value::Symbol(symbol) => {
                            sub_result = compile_inner(subexp, compile_env.clone(), is_quoted)?;
                            if keyword.as_str() == "define" {
                                sub_result.push(Opcode::StoreName(symbol));
                            } else {
                                sub_result.push(Opcode::SetName(symbol));
                            }
                        }
                        _ => {
                            return Err(CompileError {
                                msg: format!(
                                    "Expected `{}` name to be a symbol, got: {}",
                                    keyword, name
                                ),
                            });
                        }
                    };

                    sub_result
                }
                Value::Symbol(keyword) if keyword.as_str() == "defun" => {
                    let args = &list.cdr().into_iter().collect::<Vec<Value>>();
                    if args.len() < 3 {
                        return Err(CompileError {
                            msg: format!("Expected at least 3 arguments to defun, got: {:?}", args),
                        });
                    }

                    let name = args[0].clone();
                    let lambda = list
                        .cdr()
                        .cdr()
                        .cons(Value::Symbol(Symbol::from_ref("lambda")));

                    let mut result;

                    match name {
                        Value::Symbol(symbol) => {
                            result = compile_inner(Value::List(lambda), compile_env, is_quoted)?;

                            result.push(Opcode::StoreName(symbol));
                        }
                        _ => {
                            return Err(CompileError {
                                msg: format!(
                                    "Expected symbol as first argument for defun, got: {}",
                                    name
                                ),
                            });
                        }
                    };

                    result
                }
                Value::Symbol(keyword) if keyword.as_str() == "lambda" => {
                    let args = &list.cdr().into_iter().collect::<Vec<Value>>();
                    if args.len() < 2 {
                        return Err(CompileError {
                            msg: format!(
                                "Expected at least 2 arguments to lambda, got: {:?}",
                                args
                            ),
                        });
                    }

                    let argnames_list =
                        require_typed_arg::<&List>(keyword, args, 0).map_err(|_| CompileError {
                            msg: format!(
                                "First argument to lambda should be a list of parameters, {}",
                                list
                            ),
                        })?;
                    let argnames = value_to_argnames(argnames_list.clone())
                        .map_err(|e| CompileError { msg: e.msg })?;

                    let body = list.cdr().cdr();

                    let mut inner_body = body
                        .into_iter()
                        .map(|thing| compile_inner(thing, compile_env.clone(), is_quoted))
                        // TODO: Remove double collect()
                        .collect::<Result<Vec<Vec<Opcode>>, CompileError>>()?
                        .into_iter()
                        .flatten()
                        .collect::<Vec<Opcode>>();
                    'bod_loop: for i in 0..inner_body.len() {
                        if let Opcode::CallFunction { arg_count } = inner_body[i] {
                            let mut pc = i as isize + 1;
                            while let Some(next_ins) = inner_body.get(pc as usize) {
                                match next_ins {
                                    Opcode::RelativeJump { offset } => {
                                        pc += offset + 1;
                                    }
                                    _ => {
                                        continue 'bod_loop;
                                    }
                                }
                            }
                            inner_body[i] = Opcode::TailCall { arg_count };
                        }
                    }
                    let body_code = Opcode::LoadConst(Value::Bytecode(Rc::new(inner_body)));

                    vec![
                        Opcode::LoadConst(args[0].clone()),
                        body_code,
                        Opcode::MakeFunction {
                            arg_count: argnames.len(),
                        },
                    ]
                }
                Value::Symbol(keyword) if keyword.as_str() == "defmacro" => {
                    let args = &list.cdr().into_iter().collect::<Vec<Value>>();
                    if args.len() < 3 {
                        return Err(CompileError {
                            msg: format!(
                                "Expected at least 3 arguments to defmacro, got: {:?}",
                                args
                            ),
                        });
                    }

                    let name = args[0].clone();
                    //let params = args[1].clone();
                    //let body = Value::List(list.cdr().cdr().cdr());
                    let lambda = list
                        .cdr()
                        .cdr()
                        .cons(Value::Symbol(Symbol::from_ref("lambda")));

                    // TODO: Add compiled funcs to compile_env
                    let code = compile_inner(Value::List(lambda), compile_env.clone(), is_quoted)?;

                    let result = op_eval(&code, compile_env.clone()).map_err(|e| CompileError {
                        msg: format!("Unable to evaluate code for defmacro: {}", e),
                    })?;

                    match name {
                        Value::Symbol(symbol) => {
                            if let Value::Lambda(func) = result {
                                compile_env.borrow_mut().define(symbol, Value::Macro(func));
                            }
                        }
                        _ => {
                            return Err(CompileError {
                                msg: format!(
                                    "Expected symbol for defmacro first argument, got: {}",
                                    name
                                ),
                            });
                        }
                    };

                    vec![]
                }
                Value::Symbol(keyword) if keyword.as_str() == "let" => {
                    //let let_env = Rc::new(RefCell::new(Env::extend(env)));

                    let args = &list.cdr().into_iter().collect::<Vec<Value>>();

                    let declarations = require_typed_arg::<&List>(keyword, args, 0).unwrap();

                    let mut result = vec![Opcode::PushEnv];

                    let mut symbols = Vec::new();

                    for decl in declarations.into_iter() {
                        let decl = &decl;

                        let decl_cons: &List = decl.try_into().map_err(|_| CompileError {
                            msg: format!("Expected declaration clause, found {}", decl),
                        })?;
                        let symbol = &decl_cons.car().unwrap();
                        let symbol: &Symbol = symbol.try_into().map_err(|_| CompileError {
                            msg: format!("Expected symbol for let declaration, found {}", symbol),
                        })?;
                        let expr = decl_cons.cdr().car().unwrap();

                        result.append(&mut compile_inner(expr, compile_env.clone(), is_quoted)?);

                        symbols.push(*symbol);
                    }

                    for symbol in symbols.into_iter().rev() {
                        result.push(Opcode::StoreName(symbol));
                    }

                    let body = list.cdr().cdr();

                    let mut body_result = body
                        .into_iter()
                        .map(|thing| compile_inner(thing, compile_env.clone(), is_quoted))
                        // TODO: Remove double collect()
                        .collect::<Result<Vec<Vec<Opcode>>, CompileError>>()?
                        .into_iter()
                        .flatten()
                        .collect();

                    result.append(&mut body_result);

                    result.push(Opcode::PopEnv);

                    result
                }
                Value::Symbol(keyword) if keyword.as_str() == "let*" => {
                    let args = &list.cdr().into_iter().collect::<Vec<Value>>();

                    let declarations = require_typed_arg::<&List>(keyword, args, 0).unwrap();

                    let mut result = vec![Opcode::PushEnv];

                    for decl in declarations.into_iter() {
                        let decl = &decl;

                        let decl_cons: &List = decl.try_into().map_err(|_| CompileError {
                            msg: format!("Expected declaration clause, found {}", decl),
                        })?;
                        let symbol = &decl_cons.car().unwrap();
                        let symbol: &Symbol = symbol.try_into().map_err(|_| CompileError {
                            msg: format!("Expected symbol for let declaration, found {}", symbol),
                        })?;
                        let expr = decl_cons.cdr().car().unwrap();

                        result.append(&mut compile_inner(expr, compile_env.clone(), is_quoted)?);
                        result.push(Opcode::StoreName(*symbol));
                    }

                    let body = list.cdr().cdr();

                    let mut body_result = body
                        .into_iter()
                        .map(|thing| compile_inner(thing, compile_env.clone(), is_quoted))
                        // TODO: Remove double collect()
                        .collect::<Result<Vec<Vec<Opcode>>, CompileError>>()?
                        .into_iter()
                        .flatten()
                        .collect();

                    result.append(&mut body_result);

                    result.push(Opcode::PopEnv);

                    result
                }
                Value::Symbol(keyword) if keyword.as_str() == "and" => {
                    let args = list.cdr().into_iter().collect::<Vec<Value>>();

                    if args.is_empty() {
                        vec![Opcode::LoadConst(Value::True)]
                    } else {
                        let mut result: Vec<Option<Opcode>> = Vec::new();
                        for arg in args {
                            let code = compile_inner(arg.clone(), compile_env.clone(), is_quoted)?;
                            result.append(&mut code.into_iter().map(Some).collect());
                            result.push(None);
                        }

                        result.pop();

                        for i in 0..result.len() {
                            if result[i].is_none() {
                                result[i] = Some(Opcode::RelativeJumpIfFalsePreserve {
                                    offset: result.len() as isize - i as isize - 1,
                                });
                            }
                        }

                        result.into_iter().collect::<Option<Vec<Opcode>>>().unwrap()
                    }
                }
                Value::Symbol(keyword) if keyword.as_str() == "or" => {
                    let args = list.cdr().into_iter().collect::<Vec<Value>>();

                    if args.is_empty() {
                        vec![Opcode::LoadConst(Value::False)]
                    } else {
                        let mut result = Vec::new();
                        for arg in args {
                            let code = compile_inner(arg.clone(), compile_env.clone(), is_quoted)?;
                            result.append(&mut code.into_iter().map(Some).collect());
                            result.push(None);
                        }

                        result.pop();

                        for i in 0..result.len() {
                            if result[i].is_none() {
                                result[i] = Some(Opcode::RelativeJumpIfTruePreserve {
                                    offset: result.len() as isize - i as isize - 1,
                                });
                            }
                        }

                        result.into_iter().collect::<Option<Vec<Opcode>>>().unwrap()
                    }
                }
                Value::Symbol(keyword) if keyword.as_str() == "if" => {
                    let args = &list.cdr().into_iter().collect::<Vec<Value>>();
                    let condition = require_arg(keyword, args, 0)
                        .map_err(|e| CompileError { msg: e.msg })?
                        .clone();
                    let then_expr = require_arg(keyword, args, 1)
                        .map_err(|e| CompileError { msg: e.msg })?
                        .clone();
                    let else_expr = require_arg(keyword, args, 2)
                        .map_err(|e| CompileError { msg: e.msg })?
                        .clone();

                    compile_inner(
                        lisp! { (cond ({ condition} { then_expr }) (T { else_expr } ))},
                        compile_env,
                        is_quoted,
                    )?
                }
                Value::Symbol(keyword) if keyword.as_str() == "cond" => {
                    let clauses = list.cdr();

                    let mut result = Vec::new();

                    let mut it = clauses.into_iter().peekable();
                    while let Some(clause) = it.next() {
                        let clause = &clause;

                        let clause: &List = clause.try_into().map_err(|_| CompileError {
                            msg: format!("Expected conditional clause, found {}", clause),
                        })?;

                        let condition = clause.car().map_err(|_| CompileError {
                            msg: "Expected condition in cond".to_owned(),
                        })?;
                        let then = clause.cdr().car().map_err(|_| CompileError {
                            msg: "Expected then clause in cond".to_owned(),
                        })?;

                        let condition_code =
                            compile_inner(condition, compile_env.clone(), is_quoted)?;
                        if condition_code == vec![Opcode::LoadConst(Value::True)] {
                            let then_code = compile_inner(then, compile_env.clone(), is_quoted)?;

                            result.append(&mut then_code.into_iter().map(Some).collect());
                            break;
                        } else {
                            let then_code = compile_inner(then, compile_env.clone(), is_quoted)?;

                            result.append(&mut condition_code.into_iter().map(Some).collect());
                            let then_len = then_code.len();

                            let has_next = it.peek().is_some();
                            let next_offset = if has_next { 1 } else { 0 };
                            result.push(Some(Opcode::RelativeJumpIfFalse {
                                offset: then_len as isize + next_offset,
                            }));
                            result.append(&mut then_code.into_iter().map(Some).collect());
                            if has_next {
                                result.push(None);
                            }
                        }
                    }

                    //result.pop();

                    for i in 0..result.len() {
                        if result[i].is_none() {
                            result[i] = Some(Opcode::RelativeJump {
                                offset: result.len() as isize - i as isize - 1,
                            });
                        }
                    }

                    result.into_iter().collect::<Option<Vec<Opcode>>>().unwrap()
                }
                Value::Symbol(keyword) if keyword.as_str() == "begin" => {
                    list.cdr()
                        .into_iter()
                        .map(|thing| compile_inner(thing, compile_env.clone(), is_quoted))
                        // TODO: Remove double collect()
                        .collect::<Result<Vec<Vec<Opcode>>, CompileError>>()?
                        .into_iter()
                        .flatten()
                        .collect()
                }
                Value::Symbol(keyword) if keyword.as_str() == "eval-when-compiled-and-run" => {
                    let mut code = Vec::new();
                    for thing in list.cdr().into_iter() {
                        let mut new_code = compile_inner(thing, compile_env.clone(), is_quoted)?;
                        op_eval(&new_code, compile_env.clone()).map_err(|e| CompileError {
                            msg: format!("Error in eval-when-compiled-and-run: {}", e.msg),
                        })?;
                        code.append(&mut new_code);
                    }

                    //let code = codes.into_iter().flatten().collect::<Vec<Opcode>>();

                    code
                }
                Value::Symbol(keyword) if keyword.as_str() == "macroexpand" => {
                    // TODO: Tidy this whole section
                    // Try to run
                    // Check if quoted?
                    let loose_list = list.cdr().car().unwrap();
                    if let Value::List(list) = loose_list {
                        let first_item = list.cdr().car().unwrap();

                        let list;

                        let keyword = if let Value::List(removed_quote_list) = &first_item {
                            list = removed_quote_list;
                            match removed_quote_list.car().unwrap() {
                                Value::Symbol(keyword) => Some(keyword),
                                _ => None,
                            }
                        } else {
                            panic!("WHY HERE IN MACROEXPAND?");
                        };

                        if let Some(keyword) = keyword {
                            if let Some(Value::Macro(func)) = compile_env.borrow().get(&keyword) {
                                let args = list.into_iter().skip(1).collect::<Vec<Value>>();

                                let func_result =
                                    call_func(compile_env.clone(), &Value::Macro(func), args)
                                        .map_err(|e| CompileError {
                                            msg: format!("Got error running macro: {}", e),
                                        })?;

                                // Need to continue with compiling rest of expr?
                                return Ok(vec![Opcode::LoadConst(func_result)]);
                            } else {
                                println!("NOT MACRO?");
                                return Ok(vec![Opcode::LoadConst(Value::NIL)]);
                            }
                        } else {
                            println!("NOT KEYWORD?: {:?}", first_item);
                            return Ok(vec![Opcode::LoadConst(Value::NIL)]);
                        }
                    } else {
                        panic!("NOT A QUOTED THING?");
                    }
                }
                first_item => {
                    let keyword = match first_item {
                        Value::Symbol(keyword) => Some(*keyword),
                        _ => None,
                    };

                    // Try to run macros
                    if let Some(keyword) = keyword {
                        if let Some(Value::Macro(func)) = compile_env.borrow().get(&keyword) {
                            let args = list.into_iter().skip(1).collect::<Vec<Value>>();

                            let func_result =
                                call_func(compile_env.clone(), &Value::Macro(func), args).map_err(
                                    |e| CompileError {
                                        msg: format!("Got error running macro: {}", e),
                                    },
                                )?;

                            println!("MACRO EXPAND?: {}", func_result);

                            // Need to continue with compiling rest of expr?
                            return compile_inner(func_result, compile_env.clone(), is_quoted);
                        }
                    }

                    let mut arg_code = list
                        .into_iter()
                        .skip(1)
                        .map(|car| compile_inner(car, compile_env.clone(), is_quoted))
                        .collect::<Result<Vec<Vec<Opcode>>, CompileError>>()?;
                    let arg_count = arg_code.len();
                    let first_expression = list.car().unwrap();
                    let mut result =
                        compile_inner(first_expression, compile_env.clone(), is_quoted)?;
                    for code in &mut arg_code {
                        result.append(code);
                    }

                    result.push(Opcode::CallFunction { arg_count });
                    result
                }
            }
        }
        _ => unimplemented!("{:?}", expression),
    };

    Ok(res)
}
