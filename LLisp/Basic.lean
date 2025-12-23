import Std
import Lean

namespace LLisp


section

open Lean Meta Elab

private syntax internal_symbol_entry := rawIdent (" => " str)?

set_option hygiene false

local
elab "declare_internal_symbols%" "{" es:internal_symbol_entry,* "}" : command => do
  let es := es.getElems.map fun x => match x with | `(internal_symbol_entry| $name $[=> $str]?) => (name, str) | _ => panic! "impossible"
  let ts ← es.mapM fun (x, _) => `(Parser.Command.ctor| | $x:ident)
  let type ← `(inductive InternalSymbol where $ts* deriving Repr, BEq, Inhabited)
  let alts ← es.mapM fun (x, s) =>
    let s := s.getD (quote x.getId.toString)
    `(Parser.Term.matchAltExpr| | $x:ident => $s:term )
  let toString ← `(def InternalSymbol.toString : InternalSymbol → String $alts:matchAlt*)
  let nums := Array.range es.size |>.map fun i => (quote i : TSyntax `num)
  let alts ← es.zipWithM (bs := nums) fun (x, _) n =>
    `(Parser.Term.matchAltExpr| | .$x:ident => $n:term )
  let uid ← `(def InternalSymbol.uid : InternalSymbol → Nat $alts:matchAlt*)
  let alts ← es.zipWithM (bs := nums) fun (x, _) n =>
    `(Parser.Term.matchAltExpr| | $n:term => .$x:ident )
  let alts := alts.push (← `(Parser.Term.matchAltExpr| | _ => panic! s!"{decl_name%}: uid unexpected"))
  let of_uid ← `(def InternalSymbol.of_uid : Nat → InternalSymbol $alts:matchAlt*)
  let max := es.size - 1
  let max' ← `(def INTERNAL_SYMBOL_UID_MAX := $(quote max))
  Command.elabCommand type
  Command.elabCommand toString
  Command.elabCommand uid
  Command.elabCommand of_uid
  Command.elabCommand max'

declare_internal_symbols% {
  quote,
  if,
  lambda,
  define,
  cons,
  car,
  cdr,
  null?,
  eq?
}

end

def allInternalSymbols : List InternalSymbol := List.range INTERNAL_SYMBOL_UID_MAX |>.map InternalSymbol.of_uid

def internalSymbolTable : Std.HashMap String InternalSymbol := Std.HashMap.ofList <| allInternalSymbols.map fun x => (x.toString, x)

instance : ToString InternalSymbol := ⟨InternalSymbol.toString⟩

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
  private mk' ::
  symbols : Std.HashMap String Symbol := allInternalSymbols'
  next_uid : Nat := INTERNAL_SYMBOL_UID_MAX + 1
deriving Repr

def Symbols.new : Symbols := {}

instance : Inhabited Symbols where
  default := Symbols.new

def Symbols.push : Symbols → String → (Symbol × Symbols) := fun symbols name =>
  let uid := symbols.next_uid
  let s := { name, uid }
  (s, { symbols with symbols := symbols.symbols.insert name s, next_uid := uid + 1 })

-- def Frame.lookup! : Frame → LexAddr → Value := fun frame addr => Id.run do
--   let mut f := frame
--   for _ in [0:addr.depth] do
--     f := f.parent?.getD (panic! "depth exhausted")
--   f.locals[addr.index]?.getD (panic! "local index out of bounds")

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
