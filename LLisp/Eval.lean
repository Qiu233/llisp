import LLisp.Basic
import LLisp.Elab
import LLisp.Quot

namespace LLisp

unsafe abbrev EvalM := ExceptT String <| ReaderT Symbols <| StateRefT (IO.Ref Frame) IO

unsafe def getFrame : EvalM Frame := do
  let frame ← get
  frame.get

unsafe def lookup! : LexAddr → EvalM Value := fun addr => do
  let frame ← getFrame
  let mut f := frame
  for _ in [0:addr.depth] do
    f ← f.parent?.getDM (throw "depth exhausted")
  f.locals[addr.index]?.getDM (throw "local index out of bounds")

-- TODO: find a way to modify ancestor frames
unsafe def set_local : LexAddr → Value → EvalM Unit := fun addr val => do
  if addr.depth > 0 then
    throw s!"{decl_name%}: cannot write to non-local definition"
  let fv ← get
  let f ← fv.get
  if f.locals.size ≤ addr.index then
    panic! "impossible"
  fv.modify (fun f => { f with locals := f.locals.set! addr.index val })

unsafe def push_frame (size : Nat) (args : List Value) : EvalM Unit := do
  let fv ← get
  let frame ← fv.get
  let locals : Array Value := args.toArray ++ Array.replicate (size - args.length) Value.nil
  let frame' := { parent? := frame, locals : Frame }
  set (← IO.mkRef frame')

unsafe def pop_frame! : EvalM Frame := do
  let fv ← get
  let frame ← fv.get
  let some parent := frame.parent? | panic! s!"parent does not exist"
  set (← IO.mkRef parent)
  return frame

unsafe def car : Value → EvalM Value
  | .cons x _ => return x
  | .nil => throw s!"{decl_name%}: cannot apply on NIL"
  | .number _ => throw s!"{decl_name%}: cannot apply on NUMBER"
  | .str _ => throw s!"{decl_name%}: cannot apply on STRING"
  | .symbol s => throw s!"{decl_name%}: cannot apply on symbol {s.name}"
  | .closure _ => throw s!"{decl_name%}: cannot apply on CLOSURE"

unsafe def cdr : Value → EvalM Value
  | .cons _ y => return y
  | .nil => throw s!"{decl_name%}: cannot apply on NIL"
  | .number _ => throw s!"{decl_name%}: cannot apply on NUMBER"
  | .str _ => throw s!"{decl_name%}: cannot apply on STRING"
  | .symbol s => throw s!"{decl_name%}: cannot apply on symbol {s.name}"
  | .closure _ => throw s!"{decl_name%}: cannot apply on CLOSURE"

mutual

unsafe  def eval_seq : List LexSExpr → EvalM Value := fun xs => do
  let mut ret_val := Value.nil
  for code in xs do
    ret_val ← eval code
  return ret_val

unsafe  def eval' : Value → List LexSExpr → EvalM Value := fun f tail => do
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
      throw s!"wrong number of arguments are passed, expected {c.num_args}, but got {tail.length}"
    let args ← tail.mapM eval
    -- let old ← getThe Frame
    let old ← get
    set c.enclosing
    push_frame c.frame_size args
    let ret_val ← eval_seq c.seq.toList
    set old
    return ret_val
  | h => throw s!"invalid head: {h}"

unsafe  def eval : LexSExpr → EvalM Value
  | .number x => return Value.number x
  | .str x => return Value.str x
  | .symbol s addr =>
    if !s.isInternal then
      lookup! addr
    else
      eval (LexSExpr.internal_symbol (InternalSymbol.of_uid s.uid))
  | .internal_symbol (.else) =>
    return Value.const_true
  | .internal_symbol (.true) =>
    return Value.const_true
  | .internal_symbol (.false) =>
    return Value.const_false
  | .internal_symbol s => return Value.symbol s.toSymbol
  | .list [] => return Value.nil
  | expr@(.list (head :: tail)) => do
    match head with
    | .internal_symbol .quote =>
      let some q := tail[0]? | throw "`quote` expects 1 argument"
      return expr_repr q
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
    | .internal_symbol .symbol? =>
      let some x := tail[0]? | throw "`symbol?` expects 1 argument"
      let x' ← eval x
      match x' with
      | .symbol .. => return Value.const_true
      | _ => return Value.const_false
    | .internal_symbol .lambda =>
      let (frame_size, args, xs) := LexSExpr.lambda! expr
      let enclosing ← get
      let c : Closure := { seq := xs.toArray, enclosing, num_args := args.length, frame_size }
      return Value.closure c
    | .internal_symbol .define =>
      let name :: value :: _ := tail | throw "`define` expects 2 arguments"
      let LexSExpr.symbol _ addr := name | throw "The 1st argument of `define` must be a symbol"
      let value' ← eval value
      set_local addr value'
      return Value.nil
    | .internal_symbol .seq =>
      let (LexSExpr.number frameSize) :: body := tail | throw "invalid `seq`"
      assert! frameSize ≥ 0
      let old ← get
      push_frame frameSize.toNat []
      let res ← eval_seq body
      set old
      return res
    | .internal_symbol .error =>
      let x :: _ := tail | throw "`error` expects 1 arguments"
      -- let LexSExpr.number x := x | throw "argument of `error` must be a number"
      let x ← eval x
      throw s!"user error: {x}"
    | .internal_symbol .print =>
      let x :: _ := tail | throw "`print` expects 1 arguments"
      let x ← eval x
      println! s!"{x}"
      return Value.nil
    | .internal_symbol .symbol_name =>
      let x :: _ := tail | throw "`symbol_name` expects 1 arguments"
      let x ← eval x
      match x with
      | .symbol s => return Value.str s.name
      | _ => throw "`symbol_name` expects a symbol"
    | .internal_symbol .add =>
      let x :: y :: _ := tail | throw "`add` expects 2 arguments"
      let x' ← eval x
      let y' ← eval y
      match x', y' with
      | .number x', .number y' => return .number (x' + y')
      | _, _ => throw "`add` expects 2 NUMBERs"
    | .internal_symbol .sub =>
      let x :: y :: _ := tail | throw "`sub` expects 2 arguments"
      let x' ← eval x
      let y' ← eval y
      match x', y' with
      | .number x', .number y' => return .number (x' - y')
      | _, _ => throw "`sub` expects 2 NUMBERs"
    | .internal_symbol .mul =>
      let x :: y :: _ := tail | throw "`mul` expects 2 arguments"
      let x' ← eval x
      let y' ← eval y
      match x', y' with
      | .number x', .number y' => return .number (x' * y')
      | _, _ => throw "`mul` expects 2 NUMBERs"
    | .internal_symbol .div =>
      let x :: y :: _ := tail | throw "`div` expects 2 arguments"
      let x' ← eval x
      let y' ← eval y
      match x', y' with
      | .number x', .number y' => return .number (x' / y')
      | _, _ => throw "`div` expects 2 NUMBERs"
    | .internal_symbol s@(.else)
    | .internal_symbol s@(.true)
    | .internal_symbol s@(.false) =>
      throw s!"symbol {s} is not intended to be used here"
    | .symbol ..
    | .list _ =>
      let f ← eval head
      eval' f tail
    | .number _
    | .str _ =>
      throw s!"{decl_name%}: invalid head"

end

unsafe def eval_prog_core : List SExpr → ExceptT String IO Value := fun e => do
  let (seq, frameSize, symbols) ← Elab.elaborate e
  let r ← eval_seq seq symbols |>.run' (← IO.mkRef { parent? := none, locals := Array.replicate frameSize Value.nil })
  return r

unsafe def eval_prog : List SExpr → IO (Except String Value) := eval_prog_core

open LLisp.Quot

def i := Sugar.desugar_list <| (Parser.run_parse_prog <| (unsafe unsafeIO (IO.FS.readFile "A.lisp")).toOption.get!).toOption.get!

def r := Sugar.desugar_list (Parser.run_parse_prog "(symbol? 'a)").toOption.get!
#eval r.toString

#eval eval_prog i
#eval i
#eval (Parser.run_parse_prog <| (unsafe unsafeIO (IO.FS.readFile "A.lisp")).toOption.get!)
