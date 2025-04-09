import Lake
open Lake DSL

package «linear_logic» where
  -- add package configuration options here

lean_lib «LinearLogic» where
  -- add library configuration options here

@[default_target]
lean_exe «linear_logic» where
  root := `Main
