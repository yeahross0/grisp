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
    //stack: Vec<Value>,
}

pub fn op_eval_inner(
    mut code: Rc<Vec<Opcode>>,
    mut env: Rc<RefCell<Env>>,
    stack: &mut Vec<Value>,
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
        pc += 1;

        match ins {
            Opcode::LoadConst(arg) => stack.push(arg.clone()),
            Opcode::StoreName(name) => {
                let value = stack.pop().unwrap();
                env.borrow_mut().define(name.to_owned(), value);
            }
            Opcode::SetName(name) => {
                let value = stack.pop().unwrap();
                env.borrow_mut().set(name.to_owned(), value)?;
            }
            Opcode::LoadName(name) => {
                let value = env.borrow().get(name).ok_or_else(|| RuntimeError {
                    msg: format!("Could not find symbol: {}", name),
                })?;
                stack.push(value)
            }
            Opcode::MakeList { element_count } => {
                let args = stack.split_off(stack.len() - *element_count);
                let res = Value::List(args.into_iter().collect::<List>());
                stack.push(res);
            }
            Opcode::CallFunction { arg_count, .. } => {
                let args = stack.split_off(stack.len() - *arg_count);
                let func = stack.pop().unwrap();

                match func {
                    Value::NativeClosure(closure) => {
                        let res = closure.borrow_mut()(env.clone(), args);
                        stack.push(res?);
                    }
                    Value::NativeFunc(func) => {
                        let res = func(env.clone(), args);

                        stack.push(res?);
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
                                body_env.define(*arg_name, args[index].clone());
                            }
                        }
                        if let Value::Bytecode(bc) = lambda.body.as_ref() {
                            //op_eval(bc, Rc::new(RefCell::new(body_env)))
                            call_frames.push(Frame {
                                code: code.clone(),
                                pc,
                                env: env.clone(),
                            });
                            code = bc.clone();
                            pc = 0;
                            env = Rc::new(RefCell::new(body_env));
                        } else {
                            unimplemented!(); // unreachable? Value::Lambda?
                        }
                    }
                    _ => {
                        println!("Unimplemented? {:?}", func);
                        unimplemented!()
                    }
                }
            }
            Opcode::RelativeJumpIfTrue { offset } => {
                let cond = stack.pop();
                match cond {
                    Some(Value::False) | Some(Value::List(List::NIL)) => {}
                    _ => {
                        let adjusted = pc as isize + *offset;
                        pc = adjusted as usize;
                    }
                }
            }
            Opcode::RelativeJumpIfTruePreserve { offset } => {
                let cond = stack.last();
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
                let cond = stack.pop();

                match cond {
                    Some(Value::False) | Some(Value::List(List::NIL)) => {
                        let adjusted = pc as isize + *offset;
                        pc = adjusted as usize;
                    }
                    _ => {}
                }
            }
            Opcode::RelativeJumpIfFalsePreserve { offset } => {
                let cond = stack.last();

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
                let args = stack.split_off(stack.len() - *arg_count);
                let func = stack.pop().unwrap();

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
                        stack.push(res?);
                    }
                    Value::NativeFunc(func) => {
                        let res = func(env.clone(), args);
                        stack.push(res?);
                    }
                    _ => unimplemented!(),
                }
            }
            Opcode::MakeFunction { arg_count } => {
                let body_code = stack.pop().unwrap();
                let params = stack.pop().unwrap();
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
                stack.push(Value::Lambda(Lambda {
                    closure: env.clone(),
                    argnames,
                    body,
                }));
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
    Ok(stack.last().cloned().unwrap_or(Value::List(List::NIL)))
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
