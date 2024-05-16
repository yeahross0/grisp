use crate::{
    compiler::compile,
    eval::{op_eval, op_eval_inner},
    utils::{require_arg, require_typed_arg},
    Env, HashMapRc, IntType, List, RuntimeError, Symbol, Value,
};
use cfg_if::cfg_if;
use im::Vector;
use std::{cell::RefCell, collections::HashMap, convert::TryInto, rc::Rc};
cfg_if! {
    if #[cfg(feature = "bigint")] {
        use num_traits::ToPrimitive;
    }
}

/// Initialize an instance of `Env` with several core Lisp functions implemented
/// in Rust. **Without this, you will only have access to the functions you
/// implement yourself.**
pub fn default_env() -> Env {
    let mut env = Env::new();

    env.define(
        Symbol::from_ref("print"),
        Value::NativeFunc(|_env, args| {
            let expr = require_arg("print", &args, 0)?;

            println!("{}", &expr);
            Ok(expr.clone())
        }),
    );

    env.define(
        Symbol::from_ref("->str"),
        Value::NativeFunc(|_env, args| {
            let expr = require_arg("->str", &args, 0)?;

            Ok(Value::String(expr.to_string()))
        }),
    );

    env.define(
        Symbol::from_ref("->symbol"),
        Value::NativeFunc(|_env, args| {
            let expr = require_arg("->symbol", &args, 0)?;

            Ok(Value::Symbol(Symbol::new(expr.to_string())))
        }),
    );

    env.define(
        Symbol::from_ref("null?"),
        Value::NativeFunc(|_env, args| {
            let val = require_arg("null", &args, 0)?;

            Ok(Value::from(*val == Value::NIL))
        }),
    );

    env.define(
        Symbol::from_ref("number?"),
        Value::NativeFunc(|_env, args| {
            let val = require_arg("number?", &args, 0)?;

            Ok(match val {
                Value::Int(_) => Value::True,
                Value::Float(_) => Value::True,
                _ => Value::NIL,
            })
        }),
    );

    env.define(
        Symbol::from_ref("symbol?"),
        Value::NativeFunc(|_env, args| {
            let val = require_arg("symbol?", &args, 0)?;

            Ok(match val {
                Value::Symbol(_) => Value::True,
                _ => Value::NIL,
            })
        }),
    );

    env.define(
        Symbol::from_ref("bound?"),
        Value::NativeFunc(|env, args| {
            let val = require_arg("bound?", &args, 0)?;

            Ok(match val {
                Value::Symbol(symbol) => env.borrow().get(symbol).is_some().into(),
                _ => Value::NIL,
            })
        }),
    );

    env.define(
        Symbol::from_ref("boolean?"),
        Value::NativeFunc(|_env, args| {
            let val = require_arg("boolean?", &args, 0)?;

            Ok(match val {
                Value::True => Value::True,
                Value::False => Value::True,
                _ => Value::NIL,
            })
        }),
    );

    env.define(
        Symbol::from_ref("procedure?"),
        Value::NativeFunc(|_env, args| {
            let val = require_arg("procedure?", &args, 0)?;

            Ok(match val {
                Value::Lambda(_) => Value::True,
                Value::NativeFunc(_) => Value::True,
                Value::NativeClosure(_) => Value::True,
                _ => Value::NIL,
            })
        }),
    );

    env.define(
        Symbol::from_ref("pair?"),
        Value::NativeFunc(|_env, args| {
            let val = require_arg("pair?", &args, 0)?;

            Ok(match val {
                Value::List(_) => Value::True,
                _ => Value::NIL,
            })
        }),
    );

    env.define(
        Symbol::from_ref("car"),
        Value::NativeFunc(|_env, args| {
            let list = require_typed_arg::<&List>("car", &args, 0)?;

            list.car()
        }),
    );

    env.define(
        Symbol::from_ref("cdr"),
        Value::NativeFunc(|_env, args| {
            let list = require_typed_arg::<&List>("cdr", &args, 0)?;

            Ok(Value::List(list.cdr()))
        }),
    );

    env.define(
        Symbol::from_ref("cons"),
        Value::NativeFunc(|_env, args| {
            let car = require_arg("cons", &args, 0)?;
            let cdr = require_typed_arg::<&List>("cons", &args, 1)?;

            Ok(Value::List(cdr.cons(car.clone())))
        }),
    );

    env.define(
        Symbol::from_ref("list"),
        Value::NativeFunc(|_env, args| Ok(Value::List(args.iter().collect::<List>()))),
    );

    env.define(
        Symbol::from_ref("nth"),
        Value::NativeFunc(|_env, args| {
            let index = require_typed_arg::<IntType>("nth", &args, 0)?;
            let list = require_typed_arg::<&List>("nth", &args, 1)?;

            let index = TryInto::<usize>::try_into(index).map_err(|_| RuntimeError {
                msg: "Failed converting to `usize`".to_owned(),
            })?;

            Ok(list.into_iter().nth(index).unwrap_or(Value::NIL))
        }),
    );

    env.define(
        Symbol::from_ref("sort"),
        Value::NativeFunc(|_env, args| {
            let list = require_typed_arg::<&List>("sort", &args, 0)?;

            let mut v: Vec<Value> = list.into_iter().collect();

            v.sort();

            Ok(Value::List(v.into_iter().collect()))
        }),
    );

    env.define(
        Symbol::from_ref("reverse"),
        Value::NativeFunc(|_env, args| {
            let list = require_typed_arg::<&List>("reverse", &args, 0)?;

            let mut v: Vec<Value> = list.into_iter().collect();

            v.reverse();

            Ok(Value::List(v.into_iter().collect()))
        }),
    );

    env.define(
        Symbol::from_ref("list"),
        Value::NativeFunc(|_env, args| Ok(Value::List(args.iter().collect::<List>()))),
    );

    env.define(
        Symbol::from_ref("vector"),
        Value::NativeFunc(|_env, args| {
            let vec = args.into_iter().collect::<Vector<Value>>();

            Ok(Value::Vector(vec))
        }),
    );

    env.define(
        Symbol::from_ref("vec->list"),
        Value::NativeFunc(|_env, args| {
            let vec = require_typed_arg::<&Vector<Value>>("vec->list", &args, 1)?;

            let list: List = vec.into_iter().collect();

            Ok(Value::List(list))
        }),
    );

    env.define(
        Symbol::from_ref("list->vec"),
        Value::NativeFunc(|_env, args| {
            let list = require_typed_arg::<&List>("list->vec", &args, 0)?;

            let v: Vector<Value> = list.into_iter().collect();

            Ok(Value::Vector(v))
        }),
    );

    // TODO: Tidy map and filter methods
    env.define(
        Symbol::from_ref("vec:map"),
        Value::NativeFunc(|env, mut args| {
            let mut stack = Vec::new();

            let func = args.remove(0);
            if let Value::Vector(vec) = args.remove(0) {
                match func {
                    //Value::NativeFunc(func) => func(env.clone(), args),
                    //Need to fix, -> val as args
                    Value::NativeClosure(closure) => vec
                        .into_iter()
                        .map(|val| closure.borrow_mut()(env.clone(), vec![val]))
                        .collect::<Result<Vector<Value>, RuntimeError>>()
                        .map(Value::Vector),
                    Value::NativeFunc(func) => vec
                        .into_iter()
                        .map(|val| func(env.clone(), vec![val]))
                        .collect::<Result<Vector<Value>, RuntimeError>>()
                        .map(Value::Vector),
                    Value::Lambda(lambda) => {
                        //let mut old_env = Some(Env::new());
                        //let argname = lambda.argnames.iter().next().unwrap().clone();
                        let body_env = Rc::new(RefCell::new(Env::extend(lambda.closure.clone())));
                        vec.into_iter()
                            .map(|val| {
                                if let Some(arg_name) = lambda.argnames.first() {
                                    //body_env.borrow_mut().clear_now();
                                    body_env.borrow_mut().define(*arg_name, val);
                                }

                                if let Value::Bytecode(bc) = lambda.body.as_ref() {
                                    stack.clear();
                                    op_eval_inner(bc.clone(), body_env.clone(), &mut stack)
                                } else {
                                    unimplemented!(); // unreachable? Value::Lambda?
                                }
                            })
                            .collect::<Result<Vector<Value>, RuntimeError>>()
                            .map(Value::Vector)
                    }
                    _ => unimplemented!(),
                }
            } else {
                panic!("WHAT");
            }
        }),
    );

    env.define(
        Symbol::from_ref("map"),
        Value::NativeFunc(|env, args| {
            let func = require_arg("map", &args, 0)?;
            let list = require_typed_arg::<&List>("map", &args, 1)?;

            let mut stack = Vec::new();

            match func {
                //Value::NativeFunc(func) => func(env.clone(), args),
                //Need to fix, -> val as args
                Value::NativeFunc(func) => list
                    .into_iter()
                    // TODO: Need to set to body_env for this?
                    .map(|val| func(env.clone(), vec![val.clone()]))
                    .collect::<Result<List, RuntimeError>>()
                    .map(Value::List),
                Value::NativeClosure(closure) => list
                    .into_iter()
                    // TODO: Need to set to body_env for this?
                    .map(|val| closure.borrow_mut()(env.clone(), vec![val.clone()]))
                    .collect::<Result<List, RuntimeError>>()
                    .map(Value::List),
                Value::Lambda(lambda) => {
                    //let mut old_env = Some(Env::new());
                    //let argname = lambda.argnames.iter().next().unwrap().clone();
                    let body_env = Rc::new(RefCell::new(Env::extend(lambda.closure.clone())));
                    list.into_iter()
                        .map(|val| {
                            if let Some(arg_name) = lambda.argnames.first() {
                                body_env.borrow_mut().clear_now();
                                body_env.borrow_mut().define(*arg_name, val.clone());
                            }

                            if let Value::Bytecode(bc) = lambda.body.as_ref() {
                                stack.clear();
                                op_eval_inner(bc.clone(), body_env.clone(), &mut stack)
                            } else {
                                unimplemented!(); // unreachable? Value::Lambda?
                            }
                        })
                        .collect::<Result<List, RuntimeError>>()
                        .map(Value::List)
                }
                _ => unimplemented!(),
            }
        }),
    );

    // 🦀 Oh the poor `filter`, you must feel really sad being unused.
    env.define(
        Symbol::from_ref("filter"),
        Value::NativeFunc(|env, args| {
            let func = require_arg("filter", &args, 0)?;
            let list = require_typed_arg::<&List>("filter", &args, 1)?;

            match func {
                Value::NativeClosure(closure) => list
                    .into_iter()
                    // TODO: Need to set to body_env for this?
                    .filter_map(
                        |val| match closure.borrow_mut()(env.clone(), vec![val.clone()]) {
                            Ok(matches) => {
                                if matches.into() {
                                    Some(Ok(val))
                                } else {
                                    None
                                }
                            }
                            Err(e) => Some(Err(e)),
                        },
                    )
                    .collect::<Result<List, RuntimeError>>()
                    .map(Value::List),
                Value::NativeFunc(func) => list
                    .into_iter()
                    // TODO: Need to set to body_env for this?
                    .filter_map(|val| match func(env.clone(), vec![val.clone()]) {
                        Ok(matches) => {
                            if matches.into() {
                                Some(Ok(val))
                            } else {
                                None
                            }
                        }
                        Err(e) => Some(Err(e)),
                    })
                    .collect::<Result<List, RuntimeError>>()
                    .map(Value::List),
                Value::Lambda(lambda) => {
                    let mut stack = Vec::new();
                    let body_env = Rc::new(RefCell::new(Env::extend(lambda.closure.clone())));
                    list.into_iter()
                        .filter_map(|val| {
                            if let Some(arg_name) = lambda.argnames.first() {
                                body_env.borrow_mut().clear_now();
                                body_env.borrow_mut().define(*arg_name, val.clone());
                            }

                            if let Value::Bytecode(bc) = lambda.body.as_ref() {
                                stack.clear();
                                let res = op_eval_inner(bc.clone(), body_env.clone(), &mut stack);

                                match res {
                                    Ok(matches) => {
                                        if matches.into() {
                                            Some(Ok(val))
                                        } else {
                                            None
                                        }
                                    }
                                    Err(e) => Some(Err(e)),
                                }
                            } else {
                                unimplemented!(); // unreachable? Value::Lambda?
                            }
                        })
                        .collect::<Result<List, RuntimeError>>()
                        .map(Value::List)
                }
                _ => unimplemented!(),
            }
        }),
    );

    env.define(
        Symbol::from_ref("length"),
        Value::NativeFunc(|_env, args| {
            let list = require_typed_arg::<&List>("length", &args, 0)?;

            cfg_if! {
                if #[cfg(feature = "bigint")] {
                    Ok(Value::Int(list.into_iter().len().into()))
                } else {
                    Ok(Value::Int(list.into_iter().len() as IntType))
                }
            }
        }),
    );

    env.define(
        Symbol::from_ref("vec:length"),
        Value::NativeFunc(|_env, args| {
            let vec = require_typed_arg::<&Vector<Value>>("vec:length", &args, 0)?;

            cfg_if! {
                if #[cfg(feature = "bigint")] {
                    Ok(Value::Int(vec.len().into()))
                } else {
                    Ok(Value::Int(vec.len() as IntType))
                }
            }
        }),
    );

    env.define(
        Symbol::from_ref("vec:update"),
        Value::NativeFunc(|_env, args| {
            let vec = require_typed_arg::<&Vector<Value>>("vec:update", &args, 0)?;
            let index = require_typed_arg::<IntType>("vec:update", &args, 1)?;
            if args.len() <= 2 {
                Err(RuntimeError {
                    msg: "No value argument 3 in vec:update".to_owned(),
                })?
            }

            let value = args.get(2).unwrap().clone();

            Ok(Value::Vector(vec.update(index as usize, value)))
        }),
    );

    env.define(
        Symbol::from_ref("range"),
        Value::NativeFunc(|_env, args| {
            let start = require_typed_arg::<IntType>("range", &args, 0)?;
            let end = require_typed_arg::<IntType>("range", &args, 1)?;

            let mut current = start;

            Ok(Value::List(
                std::iter::from_fn(move || {
                    if current == end {
                        None
                    } else {
                        let res = Some(current);

                        current += 1;

                        res
                    }
                })
                .map(Value::from)
                .collect(),
            ))
        }),
    );

    env.define(
        Symbol::from_ref("vec:range"),
        Value::NativeFunc(|_env, args| {
            let start = require_typed_arg::<IntType>("vec:range", &args, 0)?;
            let end = require_typed_arg::<IntType>("vec:range", &args, 1)?;

            Ok(Value::Vector(
                (start..end).map(Value::from).collect::<Vector<Value>>(),
            ))
        }),
    );

    env.define(
        Symbol::from_ref("hash"),
        Value::NativeFunc(|_env, args| {
            let chunks = args.chunks(2);

            let mut hash = HashMap::new();

            for pair in chunks {
                let key = pair.first().unwrap();
                let value = pair.get(1);

                if let Some(value) = value {
                    hash.insert(key.clone(), value.clone());
                } else {
                    return Err(RuntimeError {
                        msg: format!("Must pass an even number of arguments to 'hash', because they're used as key/value pairs; found extra argument {}", key)
                    });
                }
            }

            Ok(Value::HashMap(Rc::new(RefCell::new(hash))))
        }),
    );

    env.define(
        Symbol::from_ref("hash_get"),
        Value::NativeFunc(|_env, args| {
            let hash = require_typed_arg::<&HashMapRc>("hash_get", &args, 0)?;
            let key = require_arg("hash_get", &args, 1)?;

            Ok(hash.borrow().get(key).cloned().unwrap_or(Value::NIL))
        }),
    );

    env.define(
        Symbol::from_ref("hash_set"),
        Value::NativeFunc(|_env, args| {
            let hash = require_typed_arg::<&HashMapRc>("hash_set", &args, 0)?;
            let key = require_arg("hash_set", &args, 1)?;
            let value = require_arg("hash_set", &args, 2)?;

            hash.borrow_mut().insert(key.clone(), value.clone());

            Ok(Value::HashMap(hash.clone()))
        }),
    );

    env.define(
        Symbol::from_ref("+"),
        Value::NativeFunc(|_env, args| {
            let first_arg = require_arg("+", &args, 1).unwrap_or(&Value::Int(0));

            let mut total = match first_arg {
                Value::Int(_) => Ok(Value::Int(0.into())),
                Value::Float(_) => Ok(Value::Float(0.0)),
                Value::String(_) => Ok(Value::String("".into())),
                _ => Err(RuntimeError {
                    msg: format!(
                        "Function \"+\" requires arguments to be numbers or strings; found {}",
                        first_arg
                    ),
                }),
            }?;

            for arg in args {
                total = (&total + &arg).map_err(|_| RuntimeError {
                    msg: format!(
                        "Function \"+\" requires arguments to be numbers or strings; found {}",
                        arg
                    ),
                })?;
            }

            Ok(total)
        }),
    );

    env.define(
        Symbol::from_ref("-"),
        Value::NativeFunc(|_env, args| {
            //let a = require_arg("-", &args, 0)?;

            if args.len() == 1 {
                return (&Value::Int(0) - &args[0]).map_err(|_| RuntimeError {
                    msg: String::from("Function \"-\" requires arguments to be numbers"),
                });
            }

            let mut it = args.into_iter();

            let mut total = it.next().ok_or_else(|| RuntimeError {
                msg: "Function \"-\" requires an argument'".to_owned(),
            })?;

            for n in it {
                total = (&total - &n).map_err(|_| RuntimeError {
                    msg: format!(
                        "Function \"-\" requires arguments to be numbers; found {}",
                        n
                    ),
                })?;
            }

            Ok(total)
        }),
    );

    env.define(
        Symbol::from_ref("*"),
        Value::NativeFunc(|_env, args| {
            let mut product = Value::Int(1.into());

            for arg in args {
                product = (&product * &arg).map_err(|_| RuntimeError {
                    msg: format!(
                        "Function \"*\" requires arguments to be numbers; found {}",
                        arg
                    ),
                })?;
            }

            Ok(product)
        }),
    );

    env.define(
        Symbol::from_ref("/"),
        Value::NativeFunc(|_env, args| {
            let a = require_arg("/", &args, 0)?;
            if args.len() == 1 {
                return Ok(a.clone());
            }
            let mut total = a.clone();
            for arg in args.iter().skip(1) {
                total = (&total / arg).map_err(|_| RuntimeError {
                    msg: format!(
                        "Function \"/\" requires arguments to be numbers; found {}",
                        arg
                    ),
                })?;
            }

            Ok(total)
        }),
    );

    env.define(
        Symbol::from_ref("truncate"),
        Value::NativeFunc(|_env, args| {
            let a = require_arg("truncate", &args, 0)?;
            let b = require_arg("truncate", &args, 1)?;

            if let (Ok(a), Ok(b)) = (
                TryInto::<IntType>::try_into(a),
                TryInto::<IntType>::try_into(b),
            ) {
                return Ok(Value::Int(a / b));
            }

            Err(RuntimeError {
                msg: String::from("Function \"truncate\" requires arguments to be integers"),
            })
        }),
    );

    env.define(
        Symbol::from_ref("not"),
        Value::NativeFunc(|_env, args| {
            let a = require_arg("not", &args, 0)?;
            let a: bool = a.into();

            Ok(Value::from(!a))
        }),
    );

    env.define(
        Symbol::from_ref("="),
        Value::NativeFunc(|_env, args| {
            let a = require_arg("=", &args, 0)?;
            let b = require_arg("=", &args, 1)?;

            Ok(Value::from(a == b))
        }),
    );

    env.define(
        Symbol::from_ref("!="),
        Value::NativeFunc(|_env, args| {
            let a = require_arg("!=", &args, 0)?;
            let b = require_arg("!=", &args, 1)?;

            Ok(Value::from(a != b))
        }),
    );

    env.define(
        Symbol::from_ref("<"),
        Value::NativeFunc(|_env, args| {
            let a = require_arg("<", &args, 0)?;
            let b = require_arg("<", &args, 1)?;

            Ok(Value::from(a < b))
        }),
    );

    env.define(
        Symbol::from_ref("<="),
        Value::NativeFunc(|_env, args| {
            let a = require_arg("<=", &args, 0)?;
            let b = require_arg("<=", &args, 1)?;

            Ok(Value::from(a <= b))
        }),
    );

    env.define(
        Symbol::from_ref(">"),
        Value::NativeFunc(|_env, args| {
            let a = require_arg(">", &args, 0)?;
            let b = require_arg(">", &args, 1)?;

            Ok(Value::from(a > b))
        }),
    );

    env.define(
        Symbol::from_ref(">="),
        Value::NativeFunc(|_env, args| {
            let a = require_arg(">=", &args, 0)?;
            let b = require_arg(">=", &args, 1)?;

            Ok(Value::from(a >= b))
        }),
    );

    env.define(
        Symbol::from_ref("eval"),
        Value::NativeFunc(|env, args| {
            let expr = require_arg("eval", &args, 0)?;

            let code = compile(expr.clone()).map_err(|e| RuntimeError {
                msg: format!("Error in eval: {}", e),
            })?;

            op_eval(&code, env)
        }),
    );

    env.define(
        Symbol::from_ref("apply"),
        Value::NativeFunc(|env, args| {
            let func = require_arg("apply", &args, 0)?;
            let params = require_typed_arg::<&List>("apply", &args, 1)?;

            let expr = Value::List(params.cons(func.clone()));

            let code = compile(expr.clone()).map_err(|e| RuntimeError {
                msg: format!("Error in apply: {}", e),
            })?;

            op_eval(&code, env)
        }),
    );

    env
}
