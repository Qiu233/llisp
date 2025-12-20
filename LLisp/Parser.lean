import Std

inductive LLisp.SExpr where
  | list : List SExpr → SExpr
  | number : Int → SExpr
  | symbol : String → SExpr
deriving Repr, BEq, Inhabited

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

def symbol : Parser String := do
  many1Chars (Std.Internal.Parsec.satisfy is_symbol_char)

def number : Parser Int := do
  let x ← peek!
  if x == '-' then
    let n ← digits
    return -(Int.ofNat n)
  else
    digits

mutual

partial def list : Parser (List SExpr) := do
  atom "("
  let ts ← many (sexp <* ws)
  atom ")"
  return ts.toList

partial def quote : Parser SExpr := do
  skipChar '\''
  sexp <* ws

partial def sexp : Parser SExpr := do
  attempt (SExpr.number <$> number)
  <|> attempt (SExpr.symbol <$> symbol)
  <|> attempt (SExpr.list <$> list)
  <|> attempt (quote <&> fun q => SExpr.list [SExpr.symbol "quote", q])

end

def parse_prog : Parser (List SExpr) := do
  Array.toList <$> many (sexp <* ws)

def run_parse_prog : String → Except String (List SExpr) := parse_prog.run
