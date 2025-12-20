import Std
namespace LLisp

inductive InternalSymbol where
  | quote
  | if
  | lambda
  | define
  | cons
  | car
  | cdr
  | null?
  | eq?
deriving Repr, BEq, Inhabited

/-- the in-code literal of the symbol -/
def InternalSymbol.toString : InternalSymbol → String
  | .quote  => "quote"
  | .if     => "if"
  | .lambda => "lambda"
  | .define => "define"
  | .cons   => "cons"
  | .car    => "car"
  | .cdr    => "cdr"
  | .null?  => "null?"
  | .eq?    => "eq?"

def InternalSymbol.uid : InternalSymbol → Nat
  | .quote  => 0
  | .if     => 1
  | .lambda => 2
  | .define => 3
  | .cons   => 4
  | .car    => 5
  | .cdr    => 6
  | .null?  => 7
  | .eq?    => 8

def InternalSymbol.of_uid : Nat → InternalSymbol
  | 0 => .quote
  | 1 => .if
  | 2 => .lambda
  | 3 => .define
  | 4 => .cons
  | 5 => .car
  | 6 => .cdr
  | 7 => .null?
  | 8 => .eq?
  | _ => panic! "InternalSymbol.of_uid: uid unexpected"

def INTERNAL_SYMBOL_UID_MAX := 8

def allInternalSymbols : List InternalSymbol := List.range INTERNAL_SYMBOL_UID_MAX |>.map InternalSymbol.of_uid

def internalSymbolTable : Std.HashMap String InternalSymbol := Std.HashMap.ofList <| allInternalSymbols.map fun x => (x.toString, x)

instance : ToString InternalSymbol := ⟨InternalSymbol.toString⟩


example : ∀ a : InternalSymbol, ∃ b : InternalSymbol, b.uid = a.uid - 1 := by
  intro a
  cases a <;> simp [InternalSymbol.uid]
  . exists .quote
  . exists .quote
  . exists .if
  . exists .lambda
  . exists .define
  . exists .cons
  . exists .car
  . exists .cdr
  . exists .null?

example : ∃ s : InternalSymbol, s.uid = INTERNAL_SYMBOL_UID_MAX := by exists .eq?

example : ∀ s : InternalSymbol, s.uid ≤ INTERNAL_SYMBOL_UID_MAX := by
  intro s
  cases s <;> simp [INTERNAL_SYMBOL_UID_MAX, InternalSymbol.uid]

structure Symbol where
  name : String
  uid : Nat
deriving Repr, Inhabited

def allInternalSymbols' : Std.HashMap String Symbol := Std.HashMap.ofList <| allInternalSymbols.map fun x => (x.toString, { name := x.toString, uid := x.uid })

def Symbol.isInternal : Symbol → Bool := fun x => x.uid ≤ INTERNAL_SYMBOL_UID_MAX

def InternalSymbol.toSymbol : InternalSymbol → Symbol := fun x => { name := x.toString, uid := x.uid }

instance : BEq Symbol where
  beq x y := x.uid == y.uid

/-- Lexical address -/
structure LexAddr where
  depth : Nat
  index : Nat
deriving Repr, BEq, Inhabited

inductive LexSExpr where
  | list : List LexSExpr → LexSExpr
  | number : Int → LexSExpr
  | internal_symbol : InternalSymbol → LexSExpr
  | symbol : Symbol → LexAddr → LexSExpr
deriving Repr, BEq, Inhabited

mutual

inductive Value where
  | nil : Value
  | cons : Value → Value → Value
  | number : Int → Value
  | symbol : Symbol → Value
  | closure : Closure → Value
deriving Repr, BEq, Inhabited

structure Frame where
  parent? : Option Frame
  locals : Array Value
deriving Repr, BEq, Inhabited

structure Closure where
  num_args : Nat
  frame_size : Nat
  seq : Array LexSExpr
  enclosing : Frame
deriving Repr, BEq, Inhabited

end

structure Symbols where
  symbols : Std.HashMap String Symbol := allInternalSymbols'
  next_uid : Nat := INTERNAL_SYMBOL_UID_MAX + 1
deriving Repr, Inhabited

abbrev EvalM := ExceptT String <| StateT Frame <| StateM Symbols

-- def alloc_new_symbol (sym : String) : EvalM Symbol := do
--   let s ← getThe Symbols
--   if let some t := s.symbols[sym]? then
--     return t
--   let uid := s.next_uid
--   let symbol : Symbol := { name := sym, uid }
--   set { s with symbols := s.symbols.insert sym symbol, next_uid := uid + 1 }
--   return symbol

-- def Frame.lookup! : Frame → LexAddr → Value := fun frame addr => Id.run do
--   let mut f := frame
--   for _ in [0:addr.depth] do
--     f := f.parent?.getD (panic! "depth exhausted")
--   f.locals[addr.index]?.getD (panic! "local index out of bounds")

def lookup! : LexAddr → EvalM Value := fun addr => do
  let frame ← getThe Frame
  let mut f := frame
  for _ in [0:addr.depth] do
    f ← f.parent?.getDM (throw "depth exhausted")
  f.locals[addr.index]?.getDM (throw "local index out of bounds")

def set_local : LexAddr → Value → EvalM Unit := fun addr val => do
  if addr.depth > 0 then
    throw s!"{decl_name%}: cannot write to non-local definition"
  let f ← getThe Frame
  if f.locals.size ≤ addr.index then
    panic! "???"
  modifyThe Frame (fun f => { f with locals := f.locals.set! addr.index val })
  -- let frame ← getThe Frame
  -- let mut f := frame
  -- let mut tl := #[]
  -- for _ in [0:addr.depth] do
  --   tl := tl.push f
  --   f ← f.parent?.getDM (throw "depth exhausted")
  -- let f' := { f with locals := f.locals.set! addr.index val }
  -- let frame' := tl.foldl (init := f') fun acc x => { x with parent? := some acc } -- rebuild the chain
  -- set (σ := Frame) frame'

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

partial def Frame.length : Frame → Nat := fun f =>
  if let some p := f.parent? then
    p.length + 1
  else
    1

def expr_repr : LexSExpr → Value
  | .number x => Value.number x
  | .symbol s _ => Value.symbol s
  | .internal_symbol s => Value.symbol s.toSymbol
  | .list [] => Value.nil
  | .list (head :: tail) => Value.cons (expr_repr head) (expr_repr (.list tail))

def Value.mkQuote : Value → Value := fun v => Value.cons (Value.symbol InternalSymbol.quote.toSymbol) (Value.cons v Value.nil)

def quote : LexSExpr → Value := fun v => Value.mkQuote (expr_repr v)

def Value.const_true : Value := Value.number 0

def Value.const_false : Value := Value.nil

def Value.is_false : Value → Bool := fun v => v == Value.const_false

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

def Value.veq : Value → Value → Bool
  | .nil, .nil => true
  | .symbol x, .symbol y => x == y
  | .number x, .number y => x == y
  | _, _ => false

def LexSExpr.lambda! : LexSExpr → Nat × List (Symbol × LexAddr) × List LexSExpr := fun expr => Id.run do
  let LexSExpr.list (LexSExpr.internal_symbol InternalSymbol.lambda :: ts) := expr | panic! s!"not a lambda"
  let fail : ∀ {α} [Inhabited α], Unit → α := fun () => panic! s!"invalid lambda construct"
  let (LexSExpr.number frameSize) :: (LexSExpr.list args) :: xs := ts | fail ()
  if frameSize < 0 then
    panic! "frame size is negative"
  let args := args.map fun
    | .symbol s a => (s, a)
    | _ => fail ()
  return (frameSize.toNat, args, xs)

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
