import Lake
open Lake DSL

def moreServerArgs := #[
  "-Dpp.unicode.fun=true", -- pretty-prints `fun a ↦ b`
  "-Dpp.proofs.withType=false"
]

package «symplectic» where
  moreServerArgs := moreServerArgs

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
  @ s!"v{Lean.versionString}"

@[default_target]
lean_lib «Symplectic» where
  moreLeanArgs := moreServerArgs
  weakLeanArgs := #[]
