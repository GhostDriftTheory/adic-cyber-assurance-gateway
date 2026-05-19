import Lake
open Lake DSL

package «adic_cyber_assurance_gateway» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

@[default_target]
lean_lib «adic_cyber_assurance_gateway» where
