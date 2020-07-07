
use std::{rc::Rc, collections::HashMap};
use crate::{utils::{require_list_parameter, vec_to_cons, require_parameter}, model::{Value, Env, RuntimeError, ConsCell}};

pub fn default_env() -> Env {
  let mut entries = HashMap::new();

  entries.insert(
    String::from("print"),
    Value::NativeFunc(
      |_env, args| {
        let expr = require_parameter("print", args, 0)?;

        println!("{}", &expr);
        return Ok(expr.clone());
      }));

  entries.insert(
    String::from("null"),
    Value::NativeFunc(
      |_env, args| {
        let val = require_parameter("null", args, 0)?;

        Ok(Value::from_truth(*val == Value::Nil))
      }));

  entries.insert(
    String::from("car"),
    Value::NativeFunc(
      |_env, args| {
        let list = require_list_parameter("car", args, 0)?;

        return Ok(match list {
          Value::List(c) => c.car.clone(),
          Value::Nil => Value::Nil,
          _ => panic!("Argument validation didn't work properly"),
        });
      }));
    
  entries.insert(
    String::from("cdr"),
    Value::NativeFunc(
      |_env, args| {
        let list = require_list_parameter("cdr", args, 0)?;

        return Ok(match list {
          Value::List(c) => match &c.cdr {
            Some(c) => Value::List(c.clone()),
            None => Value::Nil,
          },
          Value::Nil => Value::Nil,
          _ => panic!("Argument validation didn't work properly"),
        });
      }));
    
  entries.insert(
    String::from("cons"),
    Value::NativeFunc(
      |_env, args| {
        let car = require_parameter("cons", args, 0)?;
        let cdr = require_list_parameter("cons", args, 1)?;

        return Ok(Value::List(Rc::new(ConsCell {
          car: car.clone(),
          cdr: match cdr {
            Value::List(c) => Some(c.clone()),
            Value::Nil => None,
            _ => panic!("Argument validation didn't work properly"),
          }
        })));
      }));
    
  entries.insert(
    String::from("list"),
    Value::NativeFunc(
      |_env, args| Ok(vec_to_cons(args))));

  entries.insert(
    String::from("length"),
    Value::NativeFunc(
      |_env, args| {
        let list = require_list_parameter("length", args, 0)?;

        return match list {
          Value::List(cons) => Ok(Value::Int(cons.into_iter().len() as i32)),
          Value::Nil => Ok(Value::Int(0)),
          _ => panic!("Argument validation didn't work properly"),
        };
      }));

  entries.insert(
    String::from("+"), 
    Value::NativeFunc(
      |_env, args| {
        let a = require_parameter("+", args, 0)?;
        let b = require_parameter("+", args, 0)?;

        match (a.as_int(), b.as_int()) {
          (Some(a), Some(b)) => return Ok(Value::Int(a + b)),
          _ => ()
        };

        match (a.as_float(), b.as_float()) {
          (Some(a), Some(b)) => return Ok(Value::Float(a + b)),
          _ => ()
        };

        match (a.as_string(), b.as_string()) {
          (Some(a), Some(b)) => return Ok(Value::String(String::from(a) + b)),
          _ => ()
        };

        return Err(RuntimeError { msg: String::from("Function \"+\" requires arguments to be numbers or strings") });
      }));
    
  entries.insert(
    String::from("-"), 
    Value::NativeFunc(
      |_env, args| {
        let a = require_parameter("-", args, 0)?;
        let b = require_parameter("-", args, 0)?;

        match (a.as_int(), b.as_int()) {
          (Some(a), Some(b)) => return Ok(Value::Int(a - b)),
          _ => ()
        };

        match (a.as_float(), b.as_float()) {
          (Some(a), Some(b)) => return Ok(Value::Float(a - b)),
          _ => ()
        };

        return Err(RuntimeError { msg: String::from("Function \"-\" requires arguments to be numbers") });
      }));
    
  entries.insert(
    String::from("*"), 
    Value::NativeFunc(
      |_env, args| {
        let a = require_parameter("*", args, 0)?;
        let b = require_parameter("*", args, 0)?;

        match (a.as_int(), b.as_int()) {
          (Some(a), Some(b)) => return Ok(Value::Int(a * b)),
          _ => ()
        };

        match (a.as_float(), b.as_float()) {
          (Some(a), Some(b)) => return Ok(Value::Float(a * b)),
          _ => ()
        };

        return Err(RuntimeError { msg: String::from("Function \"*\" requires arguments to be numbers") });
      }));

  entries.insert(
    String::from("/"), 
    Value::NativeFunc(
      |_env, args| {
        let a = require_parameter("/", args, 0)?;
        let b = require_parameter("/", args, 0)?;

        match (a.as_int(), b.as_int()) {
          (Some(a), Some(b)) => return Ok(Value::Int(a / b)),
          _ => ()
        };

        match (a.as_float(), b.as_float()) {
          (Some(a), Some(b)) => return Ok(Value::Float(a / b)),
          _ => ()
        };

        return Err(RuntimeError { msg: String::from("Function \"/\" requires arguments to be numbers") });
      }));

  entries.insert(
    String::from("truncate"),
    Value::NativeFunc(
      |_env, args| {
        let a = require_parameter("truncate", args, 0)?;
        let b = require_parameter("truncate", args, 0)?;

        match (a.as_int(), b.as_int()) {
          (Some(a), Some(b)) => return Ok(Value::Int(a / b)),
          _ => ()
        };

        return Err(RuntimeError { msg: String::from("Function \"truncate\" requires arguments to be integers") });
      }));
  
  // TODO: And and or should be secial forms
  entries.insert(
    String::from("and"), 
    Value::NativeFunc(
      |_env, args| {
        let a = require_parameter("and", args, 0)?;
        let b = require_parameter("and", args, 0)?;

        Ok(Value::from_truth(a.is_truthy() && b.is_truthy()))
      }));

  entries.insert(
    String::from("or"), 
    Value::NativeFunc(
      |_env, args| {
        let a = require_parameter("or", args, 0)?;
        let b = require_parameter("or", args, 0)?;

        Ok(Value::from_truth(a.is_truthy() || b.is_truthy()))
      }));
    
  entries.insert(
    String::from("not"), 
    Value::NativeFunc(
      |_env, args| {
        let a = require_parameter("not", args, 0)?;

        Ok(Value::from_truth(!a.is_truthy()))
      }));

  entries.insert(
    String::from("=="), 
    Value::NativeFunc(
      |_env, args| {
        let a = require_parameter("==", args, 0)?;
        let b = require_parameter("==", args, 0)?;

        Ok(Value::from_truth(a == b))
      }));

  entries.insert(
    String::from("!="), 
    Value::NativeFunc(
      |_env, args| {
        let a = require_parameter("!=", args, 0)?;
        let b = require_parameter("!=", args, 0)?;

        Ok(Value::from_truth(a != b))
      }));

  entries.insert(
    String::from("<"), 
    Value::NativeFunc(
      |_env, args| {
        let a = require_parameter("<", args, 0)?;
        let b = require_parameter("<", args, 0)?;

        Ok(Value::from_truth(a < b))
      }));
      
  entries.insert(
    String::from("<="), 
    Value::NativeFunc(
      |_env, args| {
        let a = require_parameter("<=", args, 0)?;
        let b = require_parameter("<=", args, 0)?;

        Ok(Value::from_truth(a <= b))
      }));

  entries.insert(
    String::from(">"), 
    Value::NativeFunc(
      |_env, args| {
        let a = require_parameter(">", args, 0)?;
        let b = require_parameter(">", args, 0)?;

        Ok(Value::from_truth(a > b))
      }));

  entries.insert(
    String::from(">="), 
    Value::NativeFunc(
      |_env, args| {
        let a = require_parameter(">=", args, 0)?;
        let b = require_parameter(">=", args, 0)?;

        Ok(Value::from_truth(a >= b))
      }));

  Env {
    parent: None,
    entries
  }
}