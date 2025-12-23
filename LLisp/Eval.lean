import LLisp.Basic
import LLisp.Elab

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
    | .internal_symbol .cons =>
      let x :: y :: _ := tail | throw "`cons` expects 2 arguments"
      Value.cons <$> eval x <*> eval y
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
      | _ =>
        dbg_trace "{repr x'}"
        return Value.const_false
    | .internal_symbol .eq? =>
      let x :: y :: _ := tail | throw "`eq?` expects 2 arguments"
      let x' ← eval x
      let y' ← eval y
      if Value.veq x' y' then
        return Value.const_true
      else
        return Value.const_false
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

def code := "(define a null?) (define b (lambda (x) (a x) )  ) (a '())"

def e := Parser.run_parse_prog code |>.toOption.get!

#eval eval_prog e
