use im::vector;
use grisp::eval::op_eval;
use grisp::parser::parse;
use grisp::RuntimeError;
use grisp::{compiler::*, Env};
use grisp::{
    default_env, lisp, {Symbol, Value},
};
use std::{cell::RefCell, rc::Rc};

fn express(source: &str) -> Value {
    parse(source).next().unwrap().unwrap()
}

#[test]
fn test_eval_compile() {
    let env = Rc::new(RefCell::new(Env::new()));

    assert_eq!(
        op_eval(&compile(Value::Int(5)).unwrap(), env.clone()).unwrap(),
        Value::Int(5)
    );
    assert_eq!(
        op_eval(&compile(Value::Int(7)).unwrap(), env.clone()).unwrap(),
        Value::Int(7)
    );
}

#[test]
fn test_eval_load_name() {
    let env = Rc::new(RefCell::new(Env::new()));
    let sym = Symbol::from_ref("x");
    env.borrow_mut().define(sym.clone(), Value::Int(5));

    op_eval(&vec![Opcode::LoadName(sym.to_owned())], env.clone()).unwrap();
    assert_eq!(env.borrow().get(&sym), Some(Value::Int(5)));
}

#[test]
fn test_native_func() {
    let env = Rc::new(RefCell::new(default_env()));

    assert_eq!(
        op_eval(&compile(lisp! {(+ 1 2)}).unwrap(), env.clone()).unwrap(),
        Value::Int(3)
    );

    assert_eq!(
        op_eval(&compile(lisp! {(+ 1 2 3 4 5)}).unwrap(), env.clone()).unwrap(),
        Value::Int(15)
    );

    assert_eq!(
        op_eval(&compile(lisp! {(+ 4)}).unwrap(), env.clone()).unwrap(),
        Value::Int(4)
    );

    assert_eq!(
        op_eval(&compile(lisp! {(+)}).unwrap(), env.clone()).unwrap(),
        Value::Int(0)
    );

    assert_eq!(
        op_eval(&compile(lisp! {(- 5 7)}).unwrap(), env.clone()).unwrap(),
        Value::Int(-2)
    );

    /* Unclear what behaviour we want
    assert_eq!(
        op_eval(compile(lisp! {(print 1 2 3)}).unwrap(), env.clone()).unwrap(),
        Some(Value::Int(3))
    );*/
}

#[test]
fn test_eval_compile_if_condition() {
    let env = Rc::new(RefCell::new(default_env()));

    assert_eq!(
        op_eval(&compile(express("(if #t 2 3)")).unwrap(), env.clone()).unwrap(),
        Value::Int(2)
    );

    assert_eq!(
        op_eval(&compile(express("(if #f 2 3)")).unwrap(), env.clone()).unwrap(),
        Value::Int(3)
    );

    assert_eq!(
        op_eval(
            &compile(express("(if 1 (+ 1 2) (+ 3 4))")).unwrap(),
            env.clone()
        )
        .unwrap(),
        Value::Int(3)
    );
}

#[test]
fn test_eval_defun_block() {
    let env = Rc::new(RefCell::new(default_env()));
    op_eval(
        &compile(lisp! { (defun foo (x) (+ x 1) (- 5 2)) }).unwrap(),
        env.clone(),
    )
    .unwrap();
    assert_eq!(
        op_eval(
            &compile(lisp! {
                (foo 5)
            })
            .unwrap(),
            env.clone()
        )
        .unwrap(),
        Value::Int(3)
    );
}

#[test]
fn test_eval_macro_set_two() {
    let env = Rc::new(RefCell::new(Env::new()));

    let exp = express("(begin (defmacro set2! (v1 v2 e) (list 'begin (list 'set! v1 e) (list 'set! v2 e))) (define a 1) (define b 2) (set2! a b 77) '(a b))");

    op_eval(&compile(exp).unwrap(), env.clone()).unwrap();

    let a = Symbol::from_ref("a");
    let b = Symbol::from_ref("b");

    assert_eq!(env.borrow().get(&a).unwrap(), lisp! { 77 });
    assert_eq!(env.borrow().get(&b).unwrap(), lisp! { 77 });
}

#[test]
fn test_compile_macroexpand() {
    let env = Rc::new(RefCell::new(Env::new()));
    let exp = express("(begin (defmacro set2! (v1 v2 e) (list 'begin (list 'set! v1 e) (list 'set! v2 e))) (macroexpand '(set2! a b 5))))");
    assert_eq!(
        op_eval(&compile(exp).unwrap(), env.clone()).unwrap(),
        express("(begin (set! a 5) (set! b 5))"),
    );
}

#[test]
fn test_def_macro_factorial_expanded() {
    let env = Rc::new(RefCell::new(default_env()));

    assert_eq!(
            op_eval(
                &compile(lisp! {
                    (begin
                        (defmacro factorial (n)  (if (= n 0) 1 (quasiquote (* (comma n) (factorial (comma (- n 1)))))))
                        (macroexpand (quote (factorial 5)))
                    )
                })
                .unwrap(),
                env.clone(),
            )
            .unwrap(),
            lisp! { (* 5 (factorial 4)) }
        );
}

#[test]
fn test_macroexpand_quoted_expression() {
    let env = Rc::new(RefCell::new(default_env()));

    assert_eq!(
        op_eval(
            &compile(express(
                "
                    (begin
                        (defmacro set2! (v1 v2 e)
                            (list 'begin (list 'set! v1 e) (list 'set! v2 e)))
                        (macroexpand '(set2! a b (+ 3 4)))))"
            ))
            .unwrap(),
            env.clone(),
        )
        .unwrap(),
        express("(begin (set! a (+ 3 4)) (set! b (+ 3 4)))")
    );
}

#[test]
fn test_eval_call_func_from_macro() {
    let env = Rc::new(RefCell::new(default_env()));

    let exp = express(
        "
        (begin

            (eval-when-compiled-and-run
                (defun foo (n) (* n n)))
            (defmacro set-squares! (v1 v2 e)
                (define res (foo e))
            (list 'begin (list 'set! v1 res) (list 'set! v2 res)))
            (define a 0)
            (define b 0)
            (set-squares! a b 5)
            ))",
    );
    op_eval(&compile(exp).unwrap(), env.clone()).unwrap();

    let a = Symbol::from_ref("a");
    let b = Symbol::from_ref("b");

    assert_eq!(env.borrow().get(&a).unwrap(), lisp! { 25 });
    assert_eq!(env.borrow().get(&b).unwrap(), lisp! { 25 });
}

#[test]
fn test_env_table() {
    let env = Rc::new(RefCell::new(Env::new()));
    let sym = Symbol::from_ref("x");

    op_eval(
        &vec![
            Opcode::LoadConst(Value::Int(5)),
            Opcode::StoreName(sym.to_owned()),
        ],
        env.clone(),
    )
    .unwrap();
    assert_eq!(env.borrow().get(&sym), Some(Value::Int(5)));
}

#[test]
fn test_eval_lambda() {
    let env = Rc::new(RefCell::new(default_env()));

    assert_eq!(
        op_eval(
            &compile(lisp! {((lambda (x) (+ x 1)) 5)}).unwrap(),
            env.clone()
        )
        .unwrap(),
        Value::Int(6)
    );
}

#[test]
fn test_eval_nested() {
    let env = Rc::new(RefCell::new(default_env()));

    op_eval(
        &compile(lisp! { (define x (+ 1 2 3))}).unwrap(),
        env.clone(),
    )
    .unwrap();
    assert_eq!(
        env.borrow().get(&Symbol::from_ref("x")),
        Some(Value::Int(6))
    );
}

#[test]
fn test_revmap() {
    let env = Rc::new(RefCell::new(default_env()));

    let expr = lisp! {
        (defun revmap (func ls acc)
            (if (!= ls NIL) (revmap func (cdr ls) (cons (func (car ls)) acc)) acc))
    };
    let comp = compile(expr).unwrap();
    op_eval(&comp, env.clone()).unwrap();

    let expr = lisp! { (revmap (lambda (x) (* x x)) (range 0 5) NIL) };
    let comp = compile(expr).unwrap();
    let result = op_eval(&comp, env.clone()).unwrap();
    assert_eq!(result, lisp! { (16 9 4 1 0)});
}

#[test]
fn test_vec_map() {
    let env = Rc::new(RefCell::new(default_env()));

    let expr = parse("(vec:map (lambda (x) (* x x)) (vec:range 0 5))")
        .next()
        .unwrap()
        .unwrap();
    let comp = compile(expr).unwrap();
    let result = op_eval(&comp, env.clone()).unwrap();
    assert_eq!(
        result,
        Value::Vector(vector![
            Value::Int(0),
            Value::Int(1),
            Value::Int(4),
            Value::Int(9),
            Value::Int(16)
        ])
    );
}

#[test]
fn test_recursion() {
    let env = Rc::new(RefCell::new(default_env()));
    op_eval(
        &compile(express(
            "
            (defun factorial (x)
                (if (= x 0) 1 (* x (factorial (- x 1)))))
        ",
        ))
        .unwrap(),
        env.clone(),
    )
    .unwrap();
    assert_eq!(
        op_eval(
            &compile(lisp! {
                (factorial 5)
            })
            .unwrap(),
            env.clone()
        )
        .unwrap(),
        Value::Int(120)
    );
}

#[test]
fn test_eval_begin() {
    let env = Rc::new(RefCell::new(default_env()));

    let program = compile(express(
        "
        (begin
            (defun factorial (x)
                (if (= x 0) 1 (* x (factorial (- x 1)))))
            (factorial 5))
    ",
    ))
    .unwrap();

    assert_eq!(op_eval(&program, env.clone()).unwrap(), Value::Int(120));
}

#[test]
fn test_tco() {
    let env = Rc::new(RefCell::new(default_env()));
    op_eval(
        &compile(lisp! {
            (defun revmap (func ls acc)
            (if (!= ls NIL) (revmap func (cdr ls) (cons (func (car ls)) acc)) acc))
        })
        .unwrap(),
        env.clone(),
    )
    .unwrap();
    op_eval(
        &compile(lisp! {
            (revmap (lambda (x) (* x x)) (range 0 20000) NIL)
        })
        .unwrap(),
        env.clone(),
    )
    .unwrap();
}

#[test]
fn test_eval_def_macro_inc() {
    let env = Rc::new(RefCell::new(default_env()));

    assert_eq!(
        op_eval(
            &compile(express(
                "
                (begin
                    (defmacro inc (var) (list (quote set!) var (list (quote +) var 1)))
                (define a 3)
                (inc a)
                a)
            "
            ))
            .unwrap(),
            env.clone(),
        )
        .unwrap(),
        Value::Int(4)
    );
}

#[test]
fn test_eval_def_macro_set_two_eq() {
    let env = Rc::new(RefCell::new(default_env()));

    assert_eq!(
            op_eval(
                &compile(express("
                    (begin
                        (defmacro set2 (v1 v2 e) (list (quote begin) (list (quote set!) v1 e) (list (quote set!) v2 e)))
                    (define a 3)
                    (define b 4)
                    (set2 a b 5)
                    (= a b))
                "))
                .unwrap(),
                env.clone(),
            )
            .unwrap(),
            Value::True
        );
}

#[test]
fn test_def_macro_factorial() {
    let env = Rc::new(RefCell::new(default_env()));

    assert_eq!(
            op_eval(
                &compile(lisp! {
                    (begin
                        (defmacro factorial (n)  (if (= n 0) 1 (quasiquote (* (comma n) (factorial (comma (- n 1)))))))
                    (factorial 5)
                    )
                })
                .unwrap(),
                env.clone(),
            )
            .unwrap(),
            Value::Int(120)
        );
}

#[test]
fn test_simple_quote() {
    let env = Rc::new(RefCell::new(default_env()));

    assert_eq!(
        op_eval(
            &compile(lisp! {
                (quote (1 2 3 (- 5 1)))
            })
            .unwrap(),
            env.clone(),
        )
        .unwrap(),
        lisp! { (1 2 3 (- 5 1)) }
    );
}

#[test]
fn test_quote_quote() {
    let env = Rc::new(RefCell::new(default_env()));

    assert_eq!(
        op_eval(
            &compile(lisp! {
                (quote (quote 1))
            })
            .unwrap(),
            env.clone(),
        )
        .unwrap(),
        lisp! { (quote 1) }
    );

    assert_eq!(
        op_eval(
            &compile(lisp! {
                (quote (quote (quote 1)))
            })
            .unwrap(),
            env.clone(),
        )
        .unwrap(),
        lisp! { (quote (quote 1)) }
    );
}

#[test]
fn test_simple_comma() {
    let env = Rc::new(RefCell::new(default_env()));

    assert_eq!(
        op_eval(
            &compile(lisp! {
                (quasiquote (1 2 3 (comma (- 5 1))))
            })
            .unwrap(),
            env.clone(),
        )
        .unwrap(),
        lisp! { (1 2 3 4) }
    );
}

#[test]
fn test_eval_let() {
    let env = Rc::new(RefCell::new(default_env()));
    assert_eq!(
        op_eval(
            &compile(lisp! {
                (let ((x 4) (y 2)) (+ x y))
            },)
            .unwrap(),
            env.clone()
        )
        .unwrap(),
        Value::Int(6)
    );
}

#[test]
fn test_eval_let_runtime_error() {
    let env = Rc::new(RefCell::new(default_env()));
    assert_eq!(
        op_eval(
            &compile(express(
                "
                (let ((x 4) (y (+ x 1))) (+ x y))
            "
            ))
            .unwrap(),
            env.clone()
        ),
        Err(RuntimeError {
            msg: "Could not find symbol: x".to_owned()
        })
    );
}

#[test]
fn test_eval_let_star() {
    let env = Rc::new(RefCell::new(default_env()));
    assert_eq!(
        op_eval(
            &compile(express(
                "
                (let* ((x 4) (y (+ x 1))) (+ x y))
            "
            ))
            .unwrap(),
            env.clone()
        )
        .unwrap(),
        Value::Int(9)
    );
}

#[test]
fn test_eval_or() {
    let env = Rc::new(RefCell::new(default_env()));
    assert_eq!(
        op_eval(
            &compile(lisp! {
                (or 4 5 6)
            },)
            .unwrap(),
            env.clone()
        )
        .unwrap(),
        Value::Int(4)
    );

    assert_eq!(
        op_eval(
            &compile(express(
                "
                (or #f #f)
            "
            ))
            .unwrap(),
            env.clone()
        )
        .unwrap(),
        Value::False
    );
}

#[test]
fn test_eval_empty_and() {
    let env = Rc::new(RefCell::new(default_env()));
    assert_eq!(
        op_eval(
            &compile(lisp! {
                (and)
            },)
            .unwrap(),
            env.clone()
        )
        .unwrap(),
        Value::True
    );
}

#[test]
fn test_eval_and() {
    let env = Rc::new(RefCell::new(default_env()));
    assert_eq!(
        op_eval(
            &compile(lisp! {
                (and (- 4 2) (/ 5 2 7 8) (- 6))
            },)
            .unwrap(),
            env.clone()
        )
        .unwrap(),
        Value::Int(-6)
    );

    assert_eq!(
        op_eval(
            &compile(lisp! {
                (and (- 6) (* 5 2 7 8))
            },)
            .unwrap(),
            env.clone()
        )
        .unwrap(),
        Value::Int(560)
    );
}

#[test]
fn test_eval_and_more_complex() {
    let env = Rc::new(RefCell::new(default_env()));
    assert_eq!(
        op_eval(
            &compile(lisp! {
                (and (+ 1 4) (* 6 5) (- 4 2))
            },)
            .unwrap(),
            env.clone()
        )
        .unwrap(),
        Value::Int(2)
    );

    assert_eq!(
        op_eval(
            &compile(express(
                "
                (and 4 #f 6)
            "
            ))
            .unwrap(),
            env.clone()
        )
        .unwrap(),
        Value::False
    );
}

#[test]
fn test_eval_cond() {
    let env = Rc::new(RefCell::new(default_env()));
    assert_eq!(
        op_eval(
            &compile(express(
                "
                (cond (#f 2) (#t 3))
            "
            ))
            .unwrap(),
            env.clone()
        )
        .unwrap(),
        Value::Int(3)
    );

    assert_eq!(
        op_eval(
            &compile(express(
                "
                (cond (#t (+ 1 2)) ((+ 4 2 3 1) 1) (#t 2))
            "
            ))
            .unwrap(),
            env.clone()
        )
        .unwrap(),
        Value::Int(3)
    );

    assert_eq!(
        op_eval(
            &compile(express(
                "
                (cond (#f 0) (#f 1))
            "
            ))
            .unwrap(),
            env.clone()
        )
        .unwrap(),
        Value::NIL
    );
}
