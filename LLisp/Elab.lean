import LLisp.Basic
import LLisp.Parser

namespace LLisp

namespace Elab

inductive Phase where
  | expr
  | literal
deriving BEq

structure Scope where
  next : Nat
  bindings : Std.HashMap String Nat
deriving Inhabited, Repr

abbrev Env := List Scope

def Env.size! : Env → Nat := fun e => e.head!.next

abbrev ElabM := ExceptT String <| StateM Symbols

private def emptyScope : Scope := { next := 0, bindings := {} }
private def baseEnv : Env := [emptyScope]
private def literalAddr : LexAddr := { depth := 0, index := 0 }

private def internalSymbol? (name : String) : Option InternalSymbol :=
  internalSymbolTable[name]?

private def internSymbol (name : String) : ElabM Symbol := do
  let s ← get
  if let some sym := s.symbols[name]? then
    return sym
  let uid := s.next_uid
  let sym : Symbol := { name := name, uid }
  set { s with symbols := s.symbols.insert name sym, next_uid := uid + 1 }
  return sym

private def lookupAddr (env : Env) (name : String) : Option LexAddr := Id.run do
  let mut depth := 0
  let mut frames := env
  while true do
    let (scope :: rest) := frames | break
    if let some idx := scope.bindings[name]? then
      return some { depth, index := idx }
    depth := depth + 1
    frames := rest
  return none

private def bindDefine (env : Env) (name : String) : ElabM (Env × Symbol × LexAddr) := do
  let sym ← internSymbol name
  match env with
  | [] => throw s!"{decl_name%}: empty environment"
  | scope :: rest =>
    if let some idx := scope.bindings[name]? then
      return (env, sym, { depth := 0, index := idx })
    let idx := scope.next
    let scope' := { scope with next := idx + 1, bindings := scope.bindings.insert name idx }
    return (scope' :: rest, sym, { depth := 0, index := idx })

private def bindParams (params : List SExpr) : ElabM (Scope × List LexSExpr) := do
  let mut scope := emptyScope
  let mut acc : List LexSExpr := []
  for param in params do
    let name ←
      match param with
      | .symbol s => pure s
      | _ => throw s!"{decl_name%}: lambda parameters must be symbols"
    if scope.bindings.contains name then
      throw s!"{decl_name%}: duplicate lambda parameter {name}"
    let sym ← internSymbol name
    let idx := scope.next
    scope := { scope with next := idx + 1, bindings := scope.bindings.insert name idx }
    acc := LexSExpr.symbol sym { depth := 0, index := idx } :: acc
  return (scope, acc.reverse)

mutual

private partial def elabExpr (env : Env) (phase : Phase) (expr : SExpr) : ElabM (LexSExpr × Env) := do
  match expr with
  | .number n => return (.number n, env)
  | .symbol name =>
    match phase with
    | .literal =>
      let sym ← internSymbol name
      return (.symbol sym literalAddr, env)
    | .expr =>
      if let some i := internalSymbol? name then
        return (.internal_symbol i, env)
      let some addr := lookupAddr env name
        | throw s!"{decl_name%}: unknown symbol {name}"
      let sym ← internSymbol name
      return (.symbol sym addr, env)
  | .list terms =>
    match phase with
    | .literal =>
      let elems ← mapInMode env .literal terms
      return (.list elems, env)
    | .expr =>
      match terms with
      | [] => return (.list [], env)
      | first :: rest =>
        match first with
        | .symbol headName =>
          match internalSymbol? headName with
          | some InternalSymbol.quote =>
            let some arg := rest[0]?
              | throw s!"{decl_name%}: `quote` expects 1 argument"
            let (argLex, _) ← elabExpr env .literal arg
            return (.list [LexSExpr.internal_symbol .quote, argLex], env)
          | some InternalSymbol.lambda =>
            match rest with
            | params :: body =>
              let paramTerms ←
                match params with
                | .list xs => pure xs
                | _ => throw s!"{decl_name%}: lambda expects a list of parameters"
              let (scope, argLex) ← bindParams paramTerms
              let (bodyLex, env') ← elabSeq (scope :: env) body
              let lam := LexSExpr.internal_symbol InternalSymbol.lambda
              return (.list (lam :: (LexSExpr.number env'.size!) :: LexSExpr.list argLex :: bodyLex), env)
            | [] => throw s!"{decl_name%}: lambda expects a parameter list"
          | some InternalSymbol.define =>
            let some nameS := rest[0]? | throw s!"{decl_name%}: `define` expects a target symbol"
            let some valueS := rest[1]? | throw s!"{decl_name%}: `define` expects a value"
            let name ←
              match nameS with
              | .symbol s => pure s
              | _ => throw s!"{decl_name%}: `define` target must be a symbol"
            let (env', sym, addr) ← bindDefine env name
            let (valueLex, _) ← elabExpr env' .expr valueS
            let head := LexSExpr.internal_symbol InternalSymbol.define
            return (.list [head, LexSExpr.symbol sym addr, valueLex], env')
          | some internal =>
            let head := LexSExpr.internal_symbol internal
            let args ← mapInMode env .expr rest
            return (.list (head :: args), env)
          | none =>
            let (head, _) ← elabExpr env .expr first
            let tail ← mapInMode env .expr rest
            return (.list (head :: tail), env)
        | _ =>
          let (head, _) ← elabExpr env .expr first
          let tail ← mapInMode env .expr rest
          return (.list (head :: tail), env)

private partial def elabSeq (env : Env) (prog : List SExpr) : ElabM (List LexSExpr × Env) := do
  match prog with
  | [] => return ([], env)
  | expr :: rest =>
    let (current, env') ← elabExpr env .expr expr
    let (tail, env'') ← elabSeq env' rest
    return (current :: tail, env'')

private partial def mapInMode (env : Env) (phase : Phase) : List SExpr → ElabM (List LexSExpr)
  | [] => return []
  | x :: xs => do
    let (head, _) ← elabExpr env phase x
    let tail ← mapInMode env phase xs
    return head :: tail

end

def elaborate (program : List SExpr) : Except String (List LexSExpr × Env × Symbols) := do
  let initSymbols : Symbols := { symbols := allInternalSymbols', next_uid := INTERNAL_SYMBOL_UID_MAX + 1 }
  let (r, s) := (elabSeq baseEnv program).run initSymbols
  let l ← Prod.fst <$> r
  let r ← Prod.snd <$> r
  return (l, r, s)

end Elab

def code := "(define a null?) (define b (lambda (x) (a x) )  ) (a '())"

def e := Parser.run_parse_prog code |>.toOption.get!

def r := Elab.elaborate e |>.toOption.get!



#eval e
#eval r

#eval LLisp.eval_seq r.1 |>.run' { parent? := none, locals := Array.replicate r.2.1.size! Value.nil } |>.run' r.2.2



end LLisp
