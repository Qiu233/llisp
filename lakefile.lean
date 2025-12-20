import Lake
open Lake DSL

package "llisp" where
  version := v!"0.1.0"

lean_lib LLisp where
  -- add library configuration options here

@[default_target]
lean_exe "llisp" where
  root := `Main
