import Lake
open Lake DSL

package FoldArityVerif where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require aeneas from git
  "https://github.com/AeneasVerif/aeneas" @ "main" / "backends/lean"

-- so the Aeneas-extracted code can be imported as dependency
lean_lib FoldArity

@[default_target]
lean_lib FoldArityVerif
