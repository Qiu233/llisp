import Std

inductive LLisp.SExpr where
  | list : List SExpr → SExpr
  | number : Int → SExpr
  | str : String → SExpr
  | symbol : String → SExpr
deriving Repr, BEq, Inhabited

def LLisp.SExpr.toString : LLisp.SExpr → String
  | .list [.symbol "quote", body] => s!"'{body.toString}"
  | .list xs => s!"({String.intercalate " " (xs.map LLisp.SExpr.toString)})"
  | .number i => s!"{i}"
  | .str i => s!"\"{i}\""
  | .symbol s => s

instance : ToString LLisp.SExpr where
  toString x := x.toString

@[specialize]
def LLisp.SExpr.traverse {m : Type → Type} [Monad m] (f : LLisp.SExpr → m (Option LLisp.SExpr)) : LLisp.SExpr → m LLisp.SExpr
  | e@(.number _)
  | e@(.symbol _)
  | e@(.str _) => (f e) <&> fun y => y.getD e
  | .list xs => do
    let ys ← xs.mapM (fun x => (f x) <&> fun y => y.getD x)
    return .list ys

namespace LLisp.Parser

open Std.Internal.Parsec
open Std.Internal.Parsec.String

def comment : Parser Unit := do
  _ ← pchar ';'
  while true do
    let some p ← peek? | break
    skip
    if p == '\n' then
      break

def ws : Parser Unit := do
  _ ← many ((discard <| satisfy Char.isWhitespace) <|> comment)

def atom (s : String) : Parser Unit := do
  _ ← pstring s
  ws

def is_symbol_char : Char → Bool := fun c =>
  Char.isAlphanum c || String.contains "-_?*+/<>=" c

def symbol : Parser String := many1Chars (Std.Internal.Parsec.satisfy is_symbol_char)
  -- let start ← satisfy Char.isAlphanum
  -- let remaining ← many (Std.Internal.Parsec.satisfy is_symbol_char)
  -- return String.ofList (start :: remaining.toList)

def number : Parser Int := do
  let x ← peek!
  if x == '-' then
    skip
    let n ← digits
    return -(Int.ofNat n)
  else
    digits

def str : Parser String := do
  _ ← skipChar '\"'
  let r ← manyChars (Std.Internal.Parsec.satisfy fun x => x != '\"')
  _ ← skipChar '\"'
  return r

mutual

partial def list : Parser (List SExpr) := do
  atom "("
  let ts ← many (sexp <* ws)
  atom ")"
  return ts.toList

partial def quote : Parser SExpr := do
  skipChar '\''
  sexp <* ws

partial def qquote : Parser SExpr := do
  skipChar '`'
  sexp <* ws

partial def unquote : Parser SExpr := do
  skipChar ','
  sexp <* ws

partial def sexp : Parser SExpr := do
  attempt (SExpr.number <$> number)
  <|> attempt (SExpr.str <$> str)
  <|> attempt (SExpr.symbol <$> symbol)
  <|> attempt (SExpr.list <$> list)
  <|> attempt (quote <&> fun q => SExpr.list [SExpr.symbol "quote", q])
  <|> attempt (qquote <&> fun q => SExpr.list [SExpr.symbol "quasiquote", q])
  <|> attempt (unquote <&> fun q => SExpr.list [SExpr.symbol "unquote", q])

end

def parse_prog : Parser (List SExpr) := do
  Array.toList <$> (ws *> many (sexp <* ws))
  -- Array.toList <$> (ws *> many (sexp <* ws <* eof))

def run_parse_prog : String → Except String (List SExpr) := parse_prog.run

end Parser

namespace Sugar

mutual

partial def desugar : SExpr → SExpr
  | .list [.symbol "quasiquote", inner] => expand_quasiquote inner
  | .list (.symbol "unquote" :: _) => panic! "unquote outside of quasiquote"
  | .list (.symbol "defun" :: name :: args :: body) =>
    desugar <| .list [.symbol "define", name, .list (.symbol "lambda" :: args :: body) ]
  | .list xs => .list (xs.map desugar)
  | e => e

partial def expand_quasiquote : SExpr → SExpr
  | .list [.symbol "unquote", inner] => desugar inner
  | .list (.symbol "unquote" :: _) => panic! "unquote expects one argument"
  | .list xs => expand_quasiquote_list xs
  | e => .list [.symbol "quote", e]

partial def expand_quasiquote_list : List SExpr → SExpr
  | [] => .list [.symbol "quote", .list []]
  | x :: xs => .list [.symbol "cons", expand_quasiquote x, expand_quasiquote_list xs ]

end

def desugar_list : List SExpr → List SExpr := List.map desugar

end Sugar
