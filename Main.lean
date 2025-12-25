import LLisp.Eval
import DateTime

open LLisp
open LLisp.Quot


@[specialize]
def time (f : IO α) : IO (α × Nat) := do
  let start ← DateTime.current_millis
  let r ← f
  let end' ← DateTime.current_millis
  return (r, end' - start)


def wrap (n : Nat) (work : String) : String :=
  match n with
  | 0 => work
  | n + 1 => s!"(wrap {n + 1} {wrap n work})"

unsafe def main : IO Unit := do
  let work := "'((lambda (x) (car x)) (cons layer 2))"
  let template ← IO.FS.readFile "examples/Lisp.lisp"
  let tests ← (· + 1) <$> List.range 2 |>.mapM fun n => do
  -- let tests ← [2] |>.mapM fun n => do
    let code := template.replace "$CODE" (wrap n work)
    let ast ← match Parser.run_parse_prog code with
      | .error e => throw <| IO.userError s!"failed to parse with error: {e}"
      | .ok r => pure r
    let ast := Sugar.desugar_list ast
    return (n, ast)
  let rs ← tests.mapM fun (n, ast) => do
    let (result, t) ← time (eval_prog ast)
    match result with
    | .ok r => println! "result: {r}"
    | .error e => throw <| IO.userError s!"failed to run with error: {e}"
    return json% { depth:$n, time_ms:$t }
  let json := json% { work:$work, tests:$rs }
  IO.FS.writeFile "test.json" json.pretty

-- #eval main

-- def i := Sugar.desugar_list <| (Parser.run_parse_prog <| (unsafe unsafeIO (IO.FS.readFile "examples/Lisp.lisp")).toOption.get!).toOption.get!

-- #eval i.toString

-- #eval eval_prog i
