import Lake
open Lake DSL

package «my_project_1» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «MyProject1» {
  -- add any library configuration options here
}
