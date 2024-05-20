use crate::{compiler::Opcode, Env, Lambda, List, RuntimeError, Symbol, Value};
use std::{cell::RefCell, rc::Rc};

pub fn op_eval(code: &[Opcode], env: Rc<RefCell<Env>>) -> Result<Value, RuntimeError> {
    let mut stack = Vec::new();
    // TODO: Remove clone/to_vec()
    op_eval_inner(Rc::new(code.to_vec()), env, &mut stack)
}

#[derive(Debug)]
struct Frame {
    code: Rc<Vec<Opcode>>,
    pc: usize,
    env: Rc<RefCell<Env>>,
    name: Option<Symbol>,
    //stack: Vec<Value>,
}

fn create_runtime_error(msg: String, call_frames: &[Frame]) -> RuntimeError {
    let calls: Vec<Option<Symbol>> = call_frames.iter().map(|frame| frame.name).collect();
    RuntimeError {
        msg: format!("{}\n->{:?}", msg, calls),
    }
}

pub fn op_eval_inner(
    mut code: Rc<Vec<Opcode>>,
    mut env: Rc<RefCell<Env>>,
    stack: &mut Vec<(Value, Option<Symbol>)>,
) -> Result<Value, RuntimeError> {
    let mut pc = 0;
    let mut call_frames = vec![];
    'eval_loop: loop {
        if call_frames.len() > 10000 {
            Err(RuntimeError {
                msg: "STACK OVERFLOW".to_owned(),
            })?;
        }
        while pc >= code.len() {
            if call_frames.is_empty() {
                break 'eval_loop;
            } else {
                let last: Frame = call_frames.pop().unwrap();
                code = last.code.clone();
                pc = last.pc;
                env = last.env;
            }
        }
        if code.is_empty() {
            break;
        }
        let ins = &code[pc];
        //println!("INS: {:?}", ins);
        pc += 1;

        match ins {
            Opcode::LoadConst(arg) => stack.push((arg.clone(), None)),
            Opcode::StoreName(name) => {
                let value = stack.pop().unwrap().0;
                env.borrow_mut().define(name.to_owned(), value);
            }
            Opcode::SetName(name) => {
                let value = stack.pop().unwrap().0;
                env.borrow_mut().set(name.to_owned(), value)?;
            }
            Opcode::LoadName(name) => {
                let value = env.borrow().get(name).ok_or_else(|| RuntimeError {
                    msg: format!("Could not find symbol: {}", name),
                })?;
                stack.push((value, Some(name.clone())))
            }
            Opcode::MakeList { element_count } => {
                let args: Vec<Value> = stack
                    .split_off(stack.len() - *element_count)
                    .into_iter()
                    .map(|v| v.0)
                    .collect();
                let res = Value::List(args.into_iter().collect::<List>());
                stack.push((res, None));
            }
            Opcode::CallFunction { arg_count, .. } => {
                let args = stack
                    .split_off(stack.len() - *arg_count)
                    .into_iter()
                    .map(|v| v.0)
                    .collect();
                let (func, name) = stack.pop().unwrap();

                match func {
                    Value::NativeClosure(closure) => {
                        let res = closure.borrow_mut()(env.clone(), args);
                        stack.push((res?, None));
                    }
                    Value::NativeFunc(func) => {
                        let res = func(env.clone(), args);

                        stack.push((
                            res.map_err(|e| create_runtime_error(e.msg, &call_frames))?,
                            None,
                        ));
                    }
                    Value::Lambda(lambda) | Value::Macro(lambda) => {
                        let mut body_env = Env::extend(lambda.closure.clone());
                        for (index, arg_name) in lambda.argnames.iter().enumerate() {
                            if arg_name.as_str() == "..." {
                                // rest parameters
                                body_env.define(
                                    Symbol::from_ref("..."),
                                    Value::List(args.into_iter().skip(index).collect()),
                                );
                                break;
                            } else {
                                body_env.define(
                                    *arg_name,
                                    args.get(index)
                                        .ok_or_else(|| {
                                            create_runtime_error(
                                                format!("No element {}", index),
                                                &call_frames,
                                            )
                                        })?
                                        .clone(),
                                );
                            }
                        }
                        if let Value::Bytecode(bc) = lambda.body.as_ref() {
                            //op_eval(bc, Rc::new(RefCell::new(body_env)))
                            call_frames.push(Frame {
                                code: code.clone(),
                                pc,
                                env: env.clone(),
                                name,
                            });
                            code = bc.clone();
                            pc = 0;
                            env = Rc::new(RefCell::new(body_env));
                        } else {
                            unimplemented!(); // unreachable? Value::Lambda?
                        }
                    }
                    _ => {
                        //println!("Unimplemented? {:?}", func);
                        //unimplemented!()
                        Err(create_runtime_error(
                            "Error: {} not a function".to_owned(),
                            &call_frames,
                        ))?;
                    }
                }
            }
            Opcode::RelativeJumpIfTrue { offset } => {
                let cond = stack.pop().unwrap().0;
                match cond {
                    Value::False | Value::List(List::NIL) => {}
                    _ => {
                        let adjusted = pc as isize + *offset;
                        pc = adjusted as usize;
                    }
                }
            }
            Opcode::RelativeJumpIfTruePreserve { offset } => {
                let cond = stack.last().map(|v| &v.0);
                match cond {
                    Some(Value::False) | Some(Value::List(List::NIL)) => {
                        stack.pop();
                    }
                    _ => {
                        let adjusted = pc as isize + *offset;
                        pc = adjusted as usize;
                    }
                }
            }
            Opcode::RelativeJumpIfFalse { offset } => {
                let cond = stack.pop().unwrap().0;

                match cond {
                    Value::False | Value::List(List::NIL) => {
                        let adjusted = pc as isize + *offset;
                        pc = adjusted as usize;
                    }
                    _ => {}
                }
            }
            Opcode::RelativeJumpIfFalsePreserve { offset } => {
                let cond = stack.last().map(|v| &v.0);

                match cond {
                    Some(Value::False) | Some(Value::List(List::NIL)) => {
                        let adjusted = pc as isize + *offset;
                        pc = adjusted as usize;
                    }
                    _ => {
                        stack.pop();
                    }
                }
            }
            Opcode::RelativeJump { offset } => {
                let adjusted = pc as isize + *offset;
                pc = adjusted as usize;
            }
            Opcode::TailCall { arg_count } => {
                let args: Vec<Value> = stack
                    .split_off(stack.len() - *arg_count)
                    .into_iter()
                    .map(|v| v.0)
                    .collect();
                let func = stack.pop().unwrap().0;

                env.borrow_mut().clear_now();

                match func {
                    Value::Lambda(lambda) => {
                        for (index, arg_name) in lambda.argnames.iter().enumerate() {
                            if arg_name.as_str() == "..." {
                                // rest parameters
                                env.borrow_mut().define(
                                    Symbol::from_ref("..."),
                                    Value::List(args.into_iter().skip(index).collect()),
                                );
                                break;
                            } else {
                                env.borrow_mut().define(*arg_name, args[index].clone());
                            }
                        }

                        if let Value::Bytecode(bc) = lambda.body.as_ref() {
                            code = bc.clone();
                            pc = 0;
                            //envs.push(Rc::new(RefCell::new(body_env)));
                        } else {
                            unimplemented!(); // unreachable? Value::Lambda?
                        }
                    }
                    Value::NativeClosure(closure) => {
                        let res = closure.borrow_mut()(env.clone(), args);
                        stack.push((
                            res.map_err(|e| create_runtime_error(e.msg, &call_frames))?,
                            None,
                        ));
                    }
                    Value::NativeFunc(func) => {
                        let res = func(env.clone(), args);
                        stack.push((
                            res.map_err(|e| create_runtime_error(e.msg, &call_frames))?,
                            None,
                        ));
                    }
                    _ =>
                        /*Err(create_runtime_error(
                        format!("Unable to run: {}", func),
                        &call_frames,
                    ))?*/
                        {}
                }
            }
            Opcode::MakeFunction { arg_count } => {
                let body_code = stack.pop().unwrap().0;
                let params = stack.pop().unwrap().0;
                let argnames_list = if let Value::List(list) = params {
                    list
                } else {
                    return Err(RuntimeError {
                        msg: "Couldn't get arg names list in MakeFunction".to_owned(),
                    });
                };
                let argnames = value_to_argnames(argnames_list.clone())?;
                if argnames.len() != *arg_count {
                    return Err(RuntimeError {
                        msg: format!(
                            "Expected 2 in MakeFunction runtime, {} != {}",
                            argnames.len(),
                            *arg_count
                        ),
                    });
                }
                let body = Rc::new(body_code);
                stack.push((
                    Value::Lambda(Lambda {
                        closure: env.clone(),
                        argnames,
                        body,
                    }),
                    None,
                ));
            }
            Opcode::PushEnv => {
                let let_env = Rc::new(RefCell::new(Env::extend(env.clone())));

                env = let_env;
            }
            Opcode::PopEnv => {
                let let_env = { env.borrow().popped_scope().clone().unwrap_or_default() };

                env = let_env;
            }
        }
    }
    Ok(stack
        .last()
        .cloned()
        .map(|v| v.0)
        .unwrap_or(Value::List(List::NIL)))
}

pub fn call_func(
    env: Rc<RefCell<Env>>,
    func: &Value,
    args: Vec<Value>,
) -> Result<Value, RuntimeError> {
    match func {
        Value::NativeClosure(closure) => closure.borrow_mut()(env.clone(), args),
        Value::NativeFunc(func) => func(env.clone(), args),
        Value::Lambda(lambda) | Value::Macro(lambda) => {
            let mut body_env = Env::extend(lambda.closure.clone());
            for (index, arg_name) in lambda.argnames.iter().enumerate() {
                if arg_name.as_str() == "..." {
                    // rest parameters
                    body_env.define(
                        Symbol::from_ref("..."),
                        Value::List(args.into_iter().skip(index).collect()),
                    );
                    break;
                } else {
                    body_env.define(*arg_name, args[index].clone());
                }
            }
            if let Value::Bytecode(bc) = lambda.body.as_ref() {
                op_eval(bc, Rc::new(RefCell::new(body_env)))
            } else {
                unimplemented!(); // unreachable? Value::Lambda?
            }
        }
        _ => unimplemented!(),
    }
}

pub fn value_to_argnames(argnames: List) -> Result<Vec<Symbol>, RuntimeError> {
    argnames
        .into_iter()
        .enumerate()
        .map(|(index, arg)| match arg {
            Value::Symbol(s) => Ok(s),
            _ => Err(RuntimeError {
                msg: format!(
                    "Expected list of arg names, but arg {} is a {}",
                    index,
                    arg.type_name()
                ),
            }),
        })
        .collect()
}
