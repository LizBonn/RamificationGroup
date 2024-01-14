import Lake
open Lake DSL

package «RamificationGroup» where
  -- add package configuration options here

lean_lib «RamificationGroup» where
  -- add library configuration options here

@[default_target]
lean_exe «ramificationgroup» where
  root := `Main

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"
