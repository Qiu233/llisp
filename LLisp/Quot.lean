import LLisp.Frontend
import Lean

open Lean Meta Parser Elab PrettyPrinter Syntax.MonadTraverser

namespace LLisp.Quot

declare_syntax_cat llisp_sexp

scoped syntax rawIdent : llisp_sexp
scoped syntax num : llisp_sexp
scoped syntax "-" num : llisp_sexp
scoped syntax "(" llisp_sexp* ")" : llisp_sexp

private def quotFn : ParserFn := chFn '`'

private def quot : Parser where
  fn := quotFn

open Parenthesizer in
@[combinator_parenthesizer quot]
private def quot.parenthesizer : Parenthesizer := do
  visitToken

open Formatter in
@[combinator_formatter quot]
private def quot.formatter : Formatter := do
  let stx ← getCur
  match stx with
  | .atom _ s =>
    modify fun st => { st with stack := st.stack.push s, isUngrouped := false }
    goLeft
  | _ => throwError s!"not quot character: {← getCur}"

scoped syntax quot noWs llisp_sexp : llisp_sexp
scoped syntax "," noWs llisp_sexp : llisp_sexp

scoped syntax "llisp%" "{" llisp_sexp "}" : term
scoped syntax "llisp_seq%" "{" (llisp_sexp ppLine)* "}" : term

scoped macro_rules
  | `(llisp% { $x:ident }) =>
    ``(SExpr.symbol $(quote x.getId.toString))
  | `(llisp% { $x:num }) =>
    ``(SExpr.number $(quote x.getNat))
  | `(llisp% { - $x:num }) =>
    ``(SExpr.number (-$(quote x.getNat)))
  | `(llisp% { ( $xs* ) }) => do
    let ys ← xs.mapM fun x => `(llisp% { $x })
    ``(SExpr.list [$ys,*])
  | `(llisp% { `$x }) => do
    let y ← `(llisp% { $x })
    ``(SExpr.list [SExpr.symbol "quasiquote", $y])
  | `(llisp% { ,$x }) => do
    let y ← `(llisp% { $x })
    ``(SExpr.list [SExpr.symbol "unquote", $y])
  | `(llisp_seq% { $x }) => ``([llisp% { $x }])
  | `(llisp_seq% { $x $xs* }) => do
    ``(llisp% { $x } :: llisp_seq% { $xs* })
