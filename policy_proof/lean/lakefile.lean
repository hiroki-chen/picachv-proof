import Lake
open Lake DSL

package lean {
  -- add package configuration options here
}

lean_lib Lean {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe lean {
  root := `Main
}
