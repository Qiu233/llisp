import LLisp.Basic
import LLisp.Frontend

namespace LLisp

namespace Elab

private inductive Phase where
  | expr
  | literal
deriving BEq

private structure Scope where
  next : Nat
  bindings : Std.HashMap String Nat
deriving Inhabited, Repr

private abbrev Env := List Scope

def Env.size! : Env → Nat := fun e => e.head!.next

abbrev ElabM := ExceptT String <| StateRefT Symbols IO

private def emptyScope : Scope := { next := 0, bindings := {} }
private def baseEnv : Env := [emptyScope]
private def literalAddr : LexAddr := { depth := 0, index := 0 }

private def internalSymbol? (name : String) : Option InternalSymbol :=
  internalSymbolTable[name]?

private def internSymbol (name : String) : ElabM Symbol := do
  modifyGet fun s =>
    if let some sym := s.symbols[name]? then
      (sym, s)
    else
      s.push name

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

private def isDefineForm : SExpr → Bool
  | .list (.symbol name :: _) => internalSymbol? name == some .define
  | _ => false

private def parseDefineArgs (args : List SExpr) : ElabM (String × SExpr) := do
  let some nameS := args[0]? | throw s!"{decl_name%}: `define` expects a target symbol"
  let some valueS := args[1]? | throw s!"{decl_name%}: `define` expects a value"
  let name ←
    match nameS with
    | .symbol s => pure s
    | _ => throw s!"{decl_name%}: `define` target must be a symbol"
  return (name, valueS)

private def spanDefineBlock : List SExpr → (List SExpr × List SExpr)
  | [] => ([], [])
  | expr :: rest =>
    if isDefineForm expr then
      let (defs, tail) := spanDefineBlock rest
      (expr :: defs, tail)
    else
      ([], expr :: rest)

private def parseDefineExpr : SExpr → ElabM (String × SExpr)
  | .list (.symbol _ :: args) => parseDefineArgs args
  | _ => throw s!"{decl_name%}: `define` expects a list"


/-- It is crucial that all symbols must be resolved statically, which means we cannot construct a symbol at runtime. -/
private def internAllSymbols (e : SExpr) : ElabM Unit := do
  let _ ← e.traverse (m := ElabM) fun x => do
    match x with
    | .symbol s =>
      discard <| internSymbol s
    | _ => pure ()
    return none

mutual

private partial def elabExpr (env : Env) (phase : Phase) (expr : SExpr) : ElabM (LexSExpr × Env) := do
  match expr with
  | .number n => return (.number n, env)
  | .str n => return (.str n, env)
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
          | some InternalSymbol.seq =>
            let mut scope := emptyScope
            let (bodyLex, env') ← elabSeq (scope :: env) rest
            return (.list ((LexSExpr.internal_symbol .seq) :: (LexSExpr.number env'.size!) :: bodyLex), env)
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
            let (name, valueS) ← parseDefineArgs rest
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

private partial def elabDefineBlock (env : Env) (defs : List SExpr) : ElabM (List LexSExpr × Env) := do
  let parsed ← defs.mapM parseDefineExpr
  let rec bindAll (env : Env) (acc : List (Symbol × LexAddr × SExpr)) : List (String × SExpr) →
      ElabM (Env × List (Symbol × LexAddr × SExpr))
    | [] => return (env, acc.reverse)
    | (name, value) :: rest => do
        let (env', sym, addr) ← bindDefine env name
        bindAll env' ((sym, addr, value) :: acc) rest
  let (env', entries) ← bindAll env [] parsed
  let head := LexSExpr.internal_symbol InternalSymbol.define
  let lexDefs ← entries.mapM fun (sym, addr, value) => do
    let (valueLex, _) ← elabExpr env' .expr value
    return LexSExpr.list [head, LexSExpr.symbol sym addr, valueLex]
  return (lexDefs, env')

private partial def elabSeq (env : Env) (prog : List SExpr) : ElabM (List LexSExpr × Env) := do
  match prog with
  | [] => return ([], env)
  | expr :: rest =>
    if isDefineForm expr then
      let (defineBlock, tail) := spanDefineBlock (expr :: rest)
      let (defsLex, env') ← elabDefineBlock env defineBlock
      let (tailLex, env'') ← elabSeq env' tail
      return (defsLex ++ tailLex, env'')
    else
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

def elaborate (program : List SExpr) : ExceptT String IO (List LexSExpr × Nat × Symbols) := do
  let initSymbols : Symbols := Symbols.new
  let (r, s) ← StateRefT'.run (do
    internAllSymbols (SExpr.list program)
    elabSeq baseEnv program) initSymbols
  return (r.fst, r.snd.size!, s)

end Elab

end LLisp
