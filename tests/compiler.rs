use grisp::compiler::*;
use grisp::parser::parse;
use grisp::{
    lisp, {Symbol, Value},
};
use std::rc::Rc;

fn plus() -> Symbol {
    Symbol::from_ref("+")
}
fn minus() -> Symbol {
    Symbol::from_ref("-")
}
fn div() -> Symbol {
    Symbol::from_ref("/")
}

#[test]
fn test_compile() {
    assert_eq!(
        compile(Value::Int(5)).unwrap(),
        vec![Opcode::LoadConst(Value::Int(5))]
    );
    assert_eq!(
        compile(Value::Int(7)).unwrap(),
        vec![Opcode::LoadConst(Value::Int(7))]
    );
}

#[test]
fn test_compile_load_and_store() {
    let exp = lisp! { (define x 5) };
    assert_eq!(
        compile(exp).unwrap(),
        vec![
            Opcode::LoadConst(Value::Int(5)),
            Opcode::StoreName(Symbol::from_ref("x"))
        ]
    );
}

#[test]
fn test_compile_with_macro() {
    let exp = express("(begin (defmacro foo (x) `(,x)) (foo +))");
    assert_eq!(
        compile(exp).unwrap(),
        vec![
            Opcode::LoadName(Symbol::from_ref("+")),
            Opcode::CallFunction { arg_count: 0 },
        ]
    );
}

#[test]
fn test_compile_macro_set_two() {
    let exp = express("(begin (defmacro set2! (v1 v2 e) (list 'begin (list 'set! v1 e) (list 'set! v2 e))) (define a 0) (define b 0) (set2! a b 5))");
    assert_eq!(
        compile(exp).unwrap(),
        vec![
            Opcode::LoadConst(Value::Int(0)),
            Opcode::StoreName(Symbol::from_ref("a")),
            Opcode::LoadConst(Value::Int(0)),
            Opcode::StoreName(Symbol::from_ref("b")),
            Opcode::LoadConst(Value::Int(5)),
            Opcode::SetName(Symbol::from_ref("a")),
            Opcode::LoadConst(Value::Int(5)),
            Opcode::SetName(Symbol::from_ref("b")),
        ]
    );
}

#[test]
fn test_compile_load_name() {
    let exp = lisp! { x };
    assert_eq!(
        compile(exp).unwrap(),
        vec![Opcode::LoadName(Symbol::from_ref("x")),]
    );
}

#[test]
fn test_compile_call_func() {
    assert_eq!(
        compile(lisp! { (hello) }).unwrap(),
        vec![
            Opcode::LoadName(Symbol::from_ref("hello")),
            Opcode::CallFunction { arg_count: 0 }
        ]
    );
    assert_eq!(
        compile(lisp! { (hello 1) }).unwrap(),
        vec![
            Opcode::LoadName(Symbol::from_ref("hello")),
            Opcode::LoadConst(Value::Int(1)),
            Opcode::CallFunction { arg_count: 1 }
        ]
    );
    assert_eq!(
        compile(lisp! { (hello 1 2) }).unwrap(),
        vec![
            Opcode::LoadName(Symbol::from_ref("hello")),
            Opcode::LoadConst(Value::Int(1)),
            Opcode::LoadConst(Value::Int(2)),
            Opcode::CallFunction { arg_count: 2 }
        ]
    );
}

#[test]
fn test_compile_if() {
    assert_eq!(
        compile(lisp! { (if 1 2 3) }).unwrap(),
        vec![
            Opcode::LoadConst(Value::Int(1)),
            Opcode::RelativeJumpIfFalse { offset: 2 },
            Opcode::LoadConst(Value::Int(2)),
            Opcode::RelativeJump { offset: 1 },
            Opcode::LoadConst(Value::Int(3)),
        ]
    );
    assert_eq!(
        compile(lisp! { (if 1 (+ 1 2) (+ 3 4 5)) }).unwrap(),
        vec![
            Opcode::LoadConst(Value::Int(1)),
            Opcode::RelativeJumpIfFalse { offset: 5 },
            Opcode::LoadName(plus()),
            Opcode::LoadConst(Value::Int(1)),
            Opcode::LoadConst(Value::Int(2)),
            Opcode::CallFunction { arg_count: 2 },
            Opcode::RelativeJump { offset: 5 },
            Opcode::LoadName(plus()),
            Opcode::LoadConst(Value::Int(3)),
            Opcode::LoadConst(Value::Int(4)),
            Opcode::LoadConst(Value::Int(5)),
            Opcode::CallFunction { arg_count: 3 },
        ]
    );
}

#[test]
fn test_compile_defun() {
    assert_eq!(
        compile(lisp! { (lambda (x) (+ x 1)) }).unwrap(),
        vec![
            Opcode::LoadConst(lisp! { (x) }),
            Opcode::LoadConst(Value::Bytecode(Rc::new(vec![
                Opcode::LoadName(plus()),
                Opcode::LoadName(Symbol::from_ref("x")),
                Opcode::LoadConst(Value::Int(1)),
                Opcode::TailCall { arg_count: 2 },
            ]))),
            Opcode::MakeFunction { arg_count: 1 }
        ]
    );

    assert_eq!(
        compile(lisp! { (defun g (x) (+ x 1)) }).unwrap(),
        vec![
            Opcode::LoadConst(lisp! { (x) }),
            Opcode::LoadConst(Value::Bytecode(Rc::new(vec![
                Opcode::LoadName(plus()),
                Opcode::LoadName(Symbol::from_ref("x")),
                Opcode::LoadConst(Value::Int(1)),
                Opcode::TailCall { arg_count: 2 }
            ]))),
            Opcode::MakeFunction { arg_count: 1 },
            Opcode::StoreName(Symbol::from_ref("g"))
        ]
    );
}

#[test]
fn test_compile_def_macro() {
    assert_eq!(
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
        &compile(express(
            "
            (begin
            (define a 3)
            (set! a (+ a 1))
            a)
        "
        ))
        .unwrap()
    );
}

#[test]
fn test_compile_quasiquote() {
    assert_eq!(
        compile(lisp! {
            (quasiquote (quasiquote (quasiquote 1)))
        })
        .unwrap(),
        vec![
            Opcode::LoadConst(Value::Symbol(Symbol::from_ref("quasiquote"))),
            Opcode::LoadConst(Value::Symbol(Symbol::from_ref("quasiquote"))),
            Opcode::LoadConst(Value::Int(1)),
            Opcode::MakeList { element_count: 2 },
            Opcode::MakeList { element_count: 2 }
        ]
    );
}

#[test]
fn test_compile_let() {
    assert_eq!(
        compile(lisp! {
            (let ((x 4) (y 2)) (+ x y))
        },)
        .unwrap(),
        vec![
            Opcode::PushEnv,
            Opcode::LoadConst(Value::Int(4)),
            Opcode::LoadConst(Value::Int(2)),
            Opcode::StoreName(Symbol::from_ref("y")),
            Opcode::StoreName(Symbol::from_ref("x")),
            Opcode::LoadName(Symbol::from_ref("+")),
            Opcode::LoadName(Symbol::from_ref("x")),
            Opcode::LoadName(Symbol::from_ref("y")),
            Opcode::CallFunction { arg_count: 2 },
            Opcode::PopEnv
        ]
    );
}

#[test]
fn test_compile_let_star() {
    assert_eq!(
        compile(express(
            "
            (let* ((x 4) (y 2)) (+ x y))
        "
        ))
        .unwrap(),
        vec![
            Opcode::PushEnv,
            Opcode::LoadConst(Value::Int(4)),
            Opcode::StoreName(Symbol::from_ref("x")),
            Opcode::LoadConst(Value::Int(2)),
            Opcode::StoreName(Symbol::from_ref("y")),
            Opcode::LoadName(Symbol::from_ref("+")),
            Opcode::LoadName(Symbol::from_ref("x")),
            Opcode::LoadName(Symbol::from_ref("y")),
            Opcode::CallFunction { arg_count: 2 },
            Opcode::PopEnv
        ]
    );
}

#[test]
fn test_compile_or() {
    assert_eq!(
        compile(lisp! {
            (or 4 5 6)
        })
        .unwrap(),
        vec![
            Opcode::LoadConst(Value::Int(4)),
            Opcode::RelativeJumpIfTruePreserve { offset: 3 },
            Opcode::LoadConst(Value::Int(5)),
            Opcode::RelativeJumpIfTruePreserve { offset: 1 },
            Opcode::LoadConst(Value::Int(6)),
        ]
    );
}

#[test]
fn test_compile_and() {
    assert_eq!(
        compile(lisp! {
            (and 4 5 6)
        })
        .unwrap(),
        vec![
            Opcode::LoadConst(Value::Int(4)),
            Opcode::RelativeJumpIfFalsePreserve { offset: 3 },
            Opcode::LoadConst(Value::Int(5)),
            Opcode::RelativeJumpIfFalsePreserve { offset: 1 },
            Opcode::LoadConst(Value::Int(6))
        ]
    );
}

#[test]
fn test_compile_and_more_complex() {
    assert_eq!(
        compile(lisp! {
            (and (- 4 2) (/ 5 2 7 8) (- 6))
        })
        .unwrap(),
        vec![
            Opcode::LoadName(minus()),
            Opcode::LoadConst(Value::Int(4)),
            Opcode::LoadConst(Value::Int(2)),
            Opcode::CallFunction { arg_count: 2 },
            Opcode::RelativeJumpIfFalsePreserve { offset: 10 },
            Opcode::LoadName(div()),
            Opcode::LoadConst(Value::Int(5)),
            Opcode::LoadConst(Value::Int(2)),
            Opcode::LoadConst(Value::Int(7)),
            Opcode::LoadConst(Value::Int(8)),
            Opcode::CallFunction { arg_count: 4 },
            Opcode::RelativeJumpIfFalsePreserve { offset: 3 },
            Opcode::LoadName(minus()),
            Opcode::LoadConst(Value::Int(6)),
            Opcode::CallFunction { arg_count: 1 },
        ]
    );
}

#[test]
fn test_compile_cond() {
    let ast = express("(cond (#f 2) (#t 3))");
    assert_eq!(
        compile(ast).unwrap(),
        vec![
            Opcode::LoadConst(Value::False),
            Opcode::RelativeJumpIfFalse { offset: 2 },
            Opcode::LoadConst(Value::Int(2)),
            Opcode::RelativeJump { offset: 1 },
            Opcode::LoadConst(Value::Int(3)),
        ]
    );

    assert_eq!(
        compile(express("(cond (#t (+ 1 2)) ((+ 4 2 3 1) 1) (#t 2)))")).unwrap(),
        vec![
            Opcode::LoadName(plus()),
            Opcode::LoadConst(Value::Int(1)),
            Opcode::LoadConst(Value::Int(2)),
            Opcode::CallFunction { arg_count: 2 },
        ]
    );

    assert_eq!(
        compile(express("(cond (#f (+ 1 2)) ((+ 4 2 3 1) 1) (7 2)))")).unwrap(),
        vec![
            Opcode::LoadConst(Value::False),
            Opcode::RelativeJumpIfFalse { offset: 5 },
            Opcode::LoadName(plus()),
            Opcode::LoadConst(Value::Int(1)),
            Opcode::LoadConst(Value::Int(2)),
            Opcode::CallFunction { arg_count: 2 },
            Opcode::RelativeJump { offset: 12 },
            Opcode::LoadName(plus()),
            Opcode::LoadConst(Value::Int(4)),
            Opcode::LoadConst(Value::Int(2)),
            Opcode::LoadConst(Value::Int(3)),
            Opcode::LoadConst(Value::Int(1)),
            Opcode::CallFunction { arg_count: 4 },
            Opcode::RelativeJumpIfFalse { offset: 2 },
            Opcode::LoadConst(Value::Int(1)),
            Opcode::RelativeJump { offset: 3 },
            Opcode::LoadConst(Value::Int(7)),
            Opcode::RelativeJumpIfFalse { offset: 1 },
            Opcode::LoadConst(Value::Int(2)),
        ]
    );
}

fn express(source: &str) -> Value {
    parse(source).next().unwrap().unwrap()
}
