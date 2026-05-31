import Lake
open Lake DSL

require "leanprover-community" / "mathlib" @ git "v4.28.0"

package «NewtonLean» where

@[default_target]
lean_lib «NewtonLean» where
