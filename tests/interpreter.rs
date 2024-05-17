use grisp::{
    compiler::{compile, Opcode},
    default_env,
    eval::op_eval,
    lisp,
    parser::parse,
    CompileError, Env, FloatType, IntType, RuntimeError, Symbol, Value,
};
use std::{cell::RefCell, rc::Rc};

#[test]
fn eval_basic_expression() {
    let result = eval_str("(+ (* 1 2) (/ 6 3))");

    assert_eq!(result, Value::from(Into::<IntType>::into(4)));
}

#[test]
fn eval_add_list() {
    let result = eval_str("(+ 1 2 3 4)");

    assert_eq!(result, Value::from(Into::<IntType>::into(10)));
}

#[test]
fn eval_mul_list_ints() {
    let result = eval_str("(* 1 2 3 4)");

    assert_eq!(result, Value::from(Into::<IntType>::into(24)));
}

#[test]
fn eval_mul_list_mixed() {
    let result = eval_str("(* 1 2.0 3.0 4)");

    assert_eq!(result, Value::from(Into::<FloatType>::into(24.0)));
}

#[test]
fn eval_nil() {
    let result = eval_str("(= nil '())");

    assert_eq!(result, Value::from(true));
}

#[test]
fn eval_quote_1() {
    let result = eval_str("(quote \"stuff\")");

    assert_eq!(result, Value::String(String::from("stuff")));
}

#[test]
fn eval_quote_2() {
    let result = eval_str("(quote (1 2 3))");

    assert_eq!(result, lisp! { (1 2 3) });
}

#[test]
fn eval_quote_tick_list() {
    let result = eval_str("'(1 2 3)");

    assert_eq!(result, lisp! { (1 2 3) });
}

#[test]
fn eval_quote_tick_atom() {
    let result = eval_str("(nth 0 (list '12))");

    assert_eq!(result, Value::from(Into::<IntType>::into(12)));
}

#[test]
fn eval_quote_tick_symbol() {
    let result = eval_str("(nth 0 (list 'foo))");

    assert_eq!(result, Value::Symbol(Symbol::from_ref("foo")));
}

#[test]
fn eval_let() {
    let result = eval_str(
        "
        (let ((foo 12)
              (bar (+ 4 3))
              (blah \"stuff\"))
          (print foo)
          (print bar)
          (print blah)
          (list (* foo bar) (+ blah \" also\")))",
    );

    assert_eq!(result, lisp! { (84 "stuff also") });
}

#[test]
#[should_panic]
fn eval_let_scope() {
    let result = eval_str_without_default_env(
        "
        (begin
          (let ((foo 12)
                (bar (+ 4 3))
                (blah \"stuff\"))
            (print foo)
            (print bar)
            (print blah))
    
          (* foo bar))",
    )
    .unwrap();

    assert_eq!(result, lisp! { (84 "stuff also") });
}

#[test]
fn eval_set_global() {
    let result = eval_str(
        "
        (begin
          (define foo 12)
    
          (let ((bar 25))
            (set! foo 13))
    
          foo)",
    );

    assert_eq!(result, Value::from(Into::<IntType>::into(13)));
}

#[test]
fn eval_set_local() {
    let result = eval_str(
        "
        (begin
          (define foo 12)
    
          (let ((bar 25))
            (set! bar 13))
    
          foo)",
    );

    assert_eq!(result, Value::from(Into::<IntType>::into(12)));
}

#[test]
#[should_panic]
fn eval_set_undefined() {
    eval_str(
        "
        (begin
          (let ((bar 25))
            (set! foo 13)))",
    );
}

#[test]
fn eval_fib() {
    let result = eval_str(
        "
        (begin
          (define fib 
            (lambda (n)
              (cond           ;; some comment
                ((= n 0) 0)
                ((= n 1) 1)
                (#t (+ (fib (- n 1)) (fib (- n 2)) ))))) ;;another comment
    
          (list (fib 0) (fib 1) (fib 2) (fib 3) (fib 4) (fib 5) (fib 6) (fib 7) (fib 8)))",
    );

    assert_eq!(result, lisp! { (0 1 1 2 3 5 8 13 21) });
}

#[test]
fn eval_merge_sort() {
    let result = eval_str(
        "
        (begin
    
          (defun list-head (lst n) 
            (if (= n 0) 
              (list) 
              (cons (car lst) (list-head (cdr lst) (- n 1)))))
    
          (defun list-tail (lst n) 
            (if (= n 0) 
              lst 
              (list-tail (cdr lst) (- n 1))))
    
          (defun merge (lst-a lst-b)
            (cond ((not lst-a) lst-b)
                  ((not lst-b) lst-a)
                  ((< (car lst-a) (car lst-b)) (cons (car lst-a) (merge (cdr lst-a) lst-b)))
                  (#t (cons (car lst-b) (merge lst-a (cdr lst-b))))))
    
          (defun mergesort (lst)
            (if (= (length lst) 1)
              lst
              (merge (mergesort (list-head lst (truncate (length lst) 2)))
                    (mergesort (list-tail lst (truncate (length lst) 2))))))
    
          (mergesort (list 7 2 5 0 1 5)))",
    );

    assert_eq!(result, lisp! { (0 1 2 5 5 7) });
}

#[test]
fn tail_call_test() {
    let result = eval_str(
        "
        (begin
          (defun recurse-test (n)
              (if (> n 0) 
                (begin
                  (print n)
                  (recurse-test (- n 1)))
                n))
          
          (recurse-test 1000))
      ",
    );

    assert_eq!(result, Value::from(Into::<IntType>::into(0)));
}

#[test]
fn rest_parameters_test() {
    let result = eval_str(
        "
        (begin
          (defun foo (a b ...)
            ...)
          
          (foo 1 2 3 4 5))",
    );

    assert_eq!(result, lisp! { (3 4 5) });
}

#[test]
fn calling_empty_fun() {
    let result = eval_str(
        "
        (begin
          (defun foo () ())
          
          (foo))",
    );

    assert_eq!(result, lisp! { () });
}

#[test]
fn closure() {
    let result = eval_str(
        "
        (map (let ((x 3)) (lambda (y) (+ x y))) (list 0 1 2 3 4))
            ",
    );

    assert_eq!(result, lisp! {(3 4 5 6 7)});
}

#[test]
fn lambda_err() {
    let ast = parse(
        "
          (defun foo (#f) #f)",
    )
    .next()
    .unwrap()
    .unwrap();
    let code = compile(ast);

    assert_eq!(
        code,
        Err(CompileError {
            msg: String::from("Expected list of arg names, but arg 0 is a #f")
        })
    );
}

#[test]
fn quote_comma() {
    let result = eval_str(
        "
        `(+ 1 2 3 ,(+ 2 2))
        ",
    );

    assert_eq!(result, lisp! { (+ 1 2 3 4) })
}

#[test]
fn defmacro() {
    let result = eval_str(
        "
        (begin
          (defmacro foo (x)
            `(list ,x ,x ,x))
          
          (foo 3))
      ",
    );

    assert_eq!(result, lisp! { (3 3 3) })
}

#[test]
fn or_expressions() {
    let result = eval_str(
        "
        `(
          ,(or)
          ,(or #t)
          ,(or #f #t)
          ,(or #f #f #t)
    
          ,(or #f)
          ,(or #f #f)
          ,(or #f #f #f))",
    );

    assert_eq!(result, eval_str("'(#f #t #t #t #f #f #f)"))
}

#[test]
fn and_expressions() {
    let result = eval_str(
        "
        `(
          ,(and)
          ,(and #f)
          ,(and #t #f)
          ,(and #t #t #f)
    
          ,(and #t)
          ,(and #t #t)
          ,(and #t #t #t))",
    );

    assert_eq!(result, lisp! { (T F F F T T T) });
}

#[test]
fn test_compile_and_list() {
    let s = "(list (and) (and #f) (and #t #f))";

    let ast = parse(s).next().unwrap().unwrap();

    println!("AST: {}", ast);

    assert_eq!(
        compile(ast).unwrap(),
        vec![
            Opcode::LoadName(Symbol::from_ref("list")),
            Opcode::LoadConst(Value::True),
            Opcode::LoadConst(Value::False),
            Opcode::LoadConst(Value::True),
            Opcode::RelativeJumpIfFalsePreserve { offset: 1 },
            Opcode::LoadConst(Value::False),
            Opcode::CallFunction { arg_count: 3 }
        ]
    )
}

#[test]
fn test_compile_and_comma() {
    //let s = "(and T F)";
    let s = "
        `(
          ,(and)
          ,(and #f)
          ,(and #t #f)
        )";

    let ast = parse(s).next().unwrap().unwrap();

    println!("AST: {}", ast);

    assert_eq!(
        compile(ast).unwrap(),
        vec![
            Opcode::LoadConst(Value::True),
            Opcode::LoadConst(Value::False),
            Opcode::LoadConst(Value::True),
            Opcode::RelativeJumpIfFalsePreserve { offset: 1 },
            Opcode::LoadConst(Value::False),
            Opcode::MakeList { element_count: 3 }
        ]
    )
}

#[test]
fn and_expressions3() {
    let result = eval_str("(list (and) (and #f) (and #t #f))");

    //assert_eq!(result, eval_str("(list (and) (and F) (and T F))"));

    assert_eq!(result, eval_str("'(#t #f #f)"))
}

#[test]
fn and_expressions2() {
    let result = eval_str(
        "
        `(
          ,(and)
          ,(and #f)
          ,(and #t #f)
        )",
    );

    //assert_eq!(result, eval_str("(list (and) (and F) (and T F))"));

    assert_eq!(result, eval_str("'(#t #f #f)"))
}

#[test]
fn short_circuit() {
    let result = eval_str(
        "
        (begin
          (define foo 0)
    
          (or
            #t
            (set! foo 12))
    
          foo)",
    );

    assert_eq!(result, lisp! { 0 })
}

#[test]
fn native_closure() {
    let my_state = Rc::new(RefCell::new(0));

    let expression = lisp! {
      (begin
        (my_closure)
        (my_closure)
        (my_closure))
    };

    let mut env = default_env();
    let my_state_closure = my_state.clone();
    env.define(
        Symbol::from_ref("my_closure"),
        Value::NativeClosure(Rc::new(RefCell::new(
            move |_env, _args| -> Result<Value, RuntimeError> {
                let current = *my_state_closure.borrow();
                my_state_closure.replace(current + 1);
                Ok(Value::NIL)
            },
        ))),
    );
    let env = Rc::new(RefCell::new(env));

    let code = compile(expression).unwrap();
    op_eval(&code, env).unwrap();

    assert_eq!(*my_state.borrow(), 3);
}

#[cfg(test)]
fn eval_str_with_error(source: &str) -> Result<Value, RuntimeError> {
    let ast = parse(source).next().unwrap().unwrap();
    let env = Rc::new(RefCell::new(default_env()));
    op_eval(&compile(ast).unwrap(), env)
}

#[cfg(test)]
fn eval_str(source: &str) -> Value {
    eval_str_with_error(source).unwrap()
}

#[cfg(test)]
fn eval_str_without_default_env(source: &str) -> Result<Value, RuntimeError> {
    let ast = parse(source).next().unwrap().unwrap();
    let env = Rc::new(RefCell::new(Env::new()));
    op_eval(&compile(ast).unwrap(), env)
}
