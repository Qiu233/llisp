import LLisp.Basic
import LLisp.Elab
import LLisp.Quot

namespace LLisp

abbrev EvalM := ExceptT String <| ReaderT Symbols <| StateM Frame

def lookup! : LexAddr → EvalM Value := fun addr => do
  let frame ← getThe Frame
  let mut f := frame
  for _ in [0:addr.depth] do
    f ← f.parent?.getDM (throw "depth exhausted")
  f.locals[addr.index]?.getDM (throw "local index out of bounds")

-- TODO: find a way to modify ancestor frames
def set_local : LexAddr → Value → EvalM Unit := fun addr val => do
  if addr.depth > 0 then
    throw s!"{decl_name%}: cannot write to non-local definition"
  let f ← getThe Frame
  if f.locals.size ≤ addr.index then
    panic! "impossible"
  modifyThe Frame (fun f => { f with locals := f.locals.set! addr.index val })

def push_frame (size : Nat) (args : List Value) : EvalM Unit := do
  let frame ← getThe Frame
  let locals : Array Value := args.toArray ++ Array.replicate (size - args.length) Value.nil
  let frame' := { parent? := frame, locals }
  set (σ := Frame) frame'

def pop_frame! : EvalM Frame := do
  let frame ← getThe Frame
  let some parent := frame.parent? | panic! s!"parent does not exist"
  set (σ := Frame) parent
  return frame

def car : Value → EvalM Value
  | .cons x _ => return x
  | .nil => throw s!"{decl_name%}: cannot apply on NIL"
  | .number _ => throw s!"{decl_name%}: cannot apply on NUMBER"
  | .symbol s => throw s!"{decl_name%}: cannot apply on symbol {s.name}"
  | .closure _ => throw s!"{decl_name%}: cannot apply on CLOSURE"

def cdr : Value → EvalM Value
  | .cons _ y => return y
  | .nil => throw s!"{decl_name%}: cannot apply on NIL"
  | .number _ => throw s!"{decl_name%}: cannot apply on NUMBER"
  | .symbol s => throw s!"{decl_name%}: cannot apply on symbol {s.name}"
  | .closure _ => throw s!"{decl_name%}: cannot apply on CLOSURE"

mutual

partial def eval_seq : List LexSExpr → EvalM Value := fun xs => do
  let mut ret_val := Value.nil
  for code in xs do
    ret_val ← eval code
  return ret_val

partial def eval' : Value → List LexSExpr → EvalM Value := fun f tail => do
  match f with
  | .symbol s =>
    if s.isInternal then
      let i := InternalSymbol.of_uid s.uid
      let h := LexSExpr.internal_symbol i
      eval <| LexSExpr.list (h :: tail)
    else
      throw s!"{decl_name%}: internal error: symbol at head position cannot evaluate to non-internal symbol"
  | .closure c =>
    if tail.length ≠ c.num_args then
      throw "wrong number of arguments are passed"
    let args ← tail.mapM eval
    let old ← getThe Frame
    set (σ := Frame) c.enclosing
    push_frame c.frame_size args
    let ret_val ← eval_seq c.seq.toList
    set (σ := Frame) old
    return ret_val
  | _ => throw "invalid head"

partial def eval : LexSExpr → EvalM Value
  | .number x => return Value.number x
  | .symbol s addr => lookup! addr
  | .internal_symbol s => return Value.symbol s.toSymbol
  | .list [] => return Value.nil
  | expr@(.list (head :: tail)) => do
    match head with
    | .internal_symbol .quote =>
      let some q := tail[0]? | throw "`quote` expects 1 argument"
      eval q
    | .internal_symbol .if =>
      let condition :: branch_true :: branch_false :: _ := tail | throw "`if` expects 3 arguments"
      if Value.is_false (← eval condition) then
        eval branch_false
      else
        eval branch_true
    | .internal_symbol .cond =>
      for b in tail do
        match b with
        | .list (c :: body) =>
          let c ← eval c
          if !c.is_false then
            return ← eval_seq body
        | _ => throw "`cond` expects 1 argument"
      return Value.nil
    | .internal_symbol .cons =>
      let x :: y :: _ := tail | throw "`cons` expects 2 arguments"
      Value.cons <$> eval x <*> eval y
    | .internal_symbol .and =>
      let x :: y :: _ := tail | throw "`and` expects 2 arguments"
      let x' ← eval x
      if x'.is_false then
        return Value.const_false
      else
        let y' ← eval y
        if y'.is_false then
          return Value.const_false
        else
          return Value.const_true
    | .internal_symbol .car =>
      let some x := tail[0]? | throw "`car` expects 1 argument"
      let x' ← eval x
      car x'
    | .internal_symbol .cdr =>
      let some x := tail[0]? | throw "`cdr` expects 1 argument"
      let x' ← eval x
      cdr x'
    | .internal_symbol .null? =>
      let some x := tail[0]? | throw "`null?` expects 1 argument"
      let x' ← eval x
      match x' with
      | .nil => return Value.const_true
      | _ => return Value.const_false
    | .internal_symbol .eq? =>
      let x :: y :: _ := tail | throw "`eq?` expects 2 arguments"
      let x' ← eval x
      let y' ← eval y
      if Value.veq x' y' then
        return Value.const_true
      else
        return Value.const_false
    | .internal_symbol .pair? =>
      let some x := tail[0]? | throw "`pair?` expects 1 argument"
      let x' ← eval x
      match x' with
      | .cons .. => return Value.const_true
      | _ => return Value.const_false
    | .internal_symbol .atom? =>
      let some x := tail[0]? | throw "`atom?` expects 1 argument"
      let x' ← eval x
      match x' with
      | .cons .. => return Value.const_false
      | _ => return Value.const_true
    | .internal_symbol .num? =>
      let some x := tail[0]? | throw "`num?` expects 1 argument"
      let x' ← eval x
      match x' with
      | .number .. => return Value.const_true
      | _ => return Value.const_false
    | .internal_symbol .lambda =>
      let (frame_size, args, xs) := LexSExpr.lambda! expr
      let enclosing ← getThe Frame
      let c : Closure := { seq := xs.toArray, enclosing, num_args := args.length, frame_size }
      return Value.closure c
    | .internal_symbol .define =>
      let name :: value :: _ := tail | throw "`define` expects 2 arguments"
      let LexSExpr.symbol _ addr := name | throw "The 1st argument of `define` must be a symbol"
      let value' ← eval value
      set_local addr value'
      return Value.nil
    | .internal_symbol .seq => eval_seq tail
    | .internal_symbol .error =>
      let x :: _ := tail | throw "`error` expects 1 arguments"
      let LexSExpr.number x := x | throw "argument of `error` must be a number"
      throw s!"user error: {x}"
    | .internal_symbol .else =>
      return Value.const_true
    | .internal_symbol .true =>
      return Value.const_true
    | .internal_symbol .false =>
      return Value.const_false
    | .symbol sym addr =>
      let f ← lookup! addr
      eval' f tail
    | .list _ =>
      let f ← eval head
      eval' f tail
    | .number _ =>
      throw s!"{decl_name%}: invalid head"

end

def eval_prog_core : List SExpr → ExceptT String IO Value := fun e => do
  let (seq, frameSize, symbols) ← Elab.elaborate e
  let r ← eval_seq seq symbols |>.run' { parent? := none, locals := Array.replicate frameSize Value.nil }
  r

def eval_prog : List SExpr → IO (Except String Value) := eval_prog_core

open LLisp.Quot

def e := Sugar.desugar_list llisp_seq% { (define a null?) (define b (lambda (x) (seq (a x)) )  ) (b `()) }

def i := Sugar.desugar_list llisp_seq% {

(defun caar (xs) (car (car xs)))
(defun cdar (xs) (cdr (car xs)))
(defun cddr (xs) (cdr (cdr xs)))
(defun cddar (xs) (cdr (cdr (car xs))))
(defun cadar (xs) (car (cdr (car xs))))
(defun caddar (xs) (car (cdr (cdr (car xs)))))
(defun cadddr (xs) (car (cdr (cdr (cdr xs)))))
(defun caddr (xs) (car (cdr (cdr xs))))
(defun cadr (xs) (car (cdr xs)))

(defun lookup (x env)
  (cond ((null? env) (error -1))
        ((eq? x (caar env)) (cdar env))
        (else (lookup x (cdr env)))))

(defun pairlis (xs ys env)
  (if (null? xs)
      env
      (cons (cons (car xs) (car ys))
            (pairlis (cdr xs) (cdr ys) env))))

(defun isvar (x) (and (pair? x) (eq? (car x) `var)))

(defun evlis (exps env)
  (if (null? exps)
      `()
      (cons (eval (car exps) env)
            (evlis (cdr exps) env))))

(defun evcon (clauses env)
  (cond ((null? clauses) (error -2))
        ((eval (caar clauses) env)
         (eval (cadar clauses) env))
        (else
         (evcon (cdr clauses) env))))

(defun eval (exp env)
  (cond
    ((num exp)
     exp)

    ((isvar exp)
     (lookup (cadr exp) env))

    ((symbol? exp)
     (cond ((eq? exp `else) 0)
           ((eq? exp `true) 0)
           ((eq? exp `false) `())
           (else (error -3))))

    ((pair? exp)
     (cond

       ((symbol? (car exp))
        (cond

          ((eq? (car exp) `quote)
           (cadr exp))

          ((and (eq? (car exp) `and)
                (pair? (cdr exp)))
           (if (eval (cadr exp) env)
               (if (eval (caddr exp) env)
                   true
                   false)
               false))

          ((and (eq? (car exp) `if)
                (pair? (cdr exp))
                (pair? (cddr exp)))
           (if (eval (cadr exp) env)
               (eval (caddr exp) env)
               (eval (cadddr exp) env)))

          ((eq? (car exp) `null?)
           (null? (eval (cadr exp) env)))

          ((eq? (car exp) `error)
           (error (eval (cadr exp) env)))

          ((eq? (car exp) `pair?)
           (pair? (eval (cadr exp) env)))

          ((eq? (car exp) `symbol?)
           (symbol? (eval (cadr exp) env)))

          ((eq? (car exp) `num?)
           (num (eval (cadr exp) env)))

          ((eq? (car exp) `atom?)
           (atom? (eval (cadr exp) env)))

          ((eq? (car exp) `eq?)
           (eq? (eval (cadr exp) env)
                (eval (caddr exp) env)))

          ((eq? (car exp) `car)
           (car (eval (cadr exp) env)))

          ((eq? (car exp) `cdr)
           (cdr (eval (cadr exp) env)))

          ((eq? (car exp) `cons)
           (cons (eval (cadr exp) env)
                 (eval (caddr exp) env)))

          ((eq? (car exp) `cond)
           (evcon (cdr exp) env))

          (else
           (error -3))))

       ((isvar (car exp))
        (eval (cons (lookup (cadar exp) env)
                     (cdr exp))
               env))

       ((and (pair? (car exp))
             (eq? (caar exp) `lambda))
        (define params (cadar exp))
        (define body   (caddar exp))
        (define args   (evlis (cdr exp) env))
        (define env_   (pairlis params args env))
        (eval body env_))

       ((and (pair? (car exp))
             (eq? (caar exp) `define))
        (define vname  (cadar exp))
        (define val    (eval (caddar exp) env))
        (define env_   (cons (cons vname val) env))
        (eval (cadr exp) env_))

       (else
        (error -3))))

    (else
     (error -3)
     )))

(eval `1 `())
}

#eval eval_prog i
