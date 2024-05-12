import Lake
open Lake DSL

package «SelectionSort» where
  -- add package configuration options here

lean_lib «SelectionSort» where
  -- add library configuration options here

@[default_target]
lean_exe «selectionsort» where
  root := `Main
