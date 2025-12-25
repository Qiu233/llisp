import Lake
open Lake DSL

require DateTime from git "https://github.com/Qiu233/DateTime.git"

elab "#get_libstdcpp" : command =>
  open Lean Elab Command Term in do
  let defLib (term : Expr) :=
    liftTermElabM <| addAndCompile <| Declaration.defnDecl {
        name := `libstdcpp
        levelParams := []
        type := mkApp (mkConst ``Option [.zero]) (mkConst ``System.FilePath)
        value := term
        hints := .abbrev
        safety := .safe
      }
  if System.Platform.isOSX then
    defLib (mkApp (mkConst ``none [.zero]) (mkConst ``System.FilePath))
    return
  let output ← IO.Process.run {
    cmd := "whereis"
    args := #["libstdc++.so.6"]
  }
  match output.split (·.isWhitespace) with
  | name :: loc :: _ =>
    logInfo s!"found {name} at {loc}"
    defLib (mkAppN (mkConst ``some [.zero]) #[
      mkConst ``System.FilePath,
      mkApp (mkConst ``System.FilePath.mk) (mkStrLit loc)])
  | _ =>
    logError ("whereis output malformed:\n" ++ output)

#get_libstdcpp -- now available as `libstdcpp` declaration

package "llisp" where
  version := v!"0.1.0"
  moreLinkArgs := match libstdcpp with | none => #[] | some x => #[x.toString]

lean_lib LLisp where
  -- add library configuration options here

@[default_target]
lean_exe "llisp" where
  root := `Main
