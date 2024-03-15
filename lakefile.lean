import Lake
open Lake DSL

package «RamificationGroup» where
    leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

lean_lib «RamificationGroup» where
  -- add library configuration options here

@[default_target]
lean_exe «ramificationgroup» where
  root := `Main

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"

require local_class_field_theory from git "https://github.com/mariainesdff/LocalClassFieldTheory.git"
