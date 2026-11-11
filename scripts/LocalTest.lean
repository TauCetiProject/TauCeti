import Init.System.IO

/-- Run the shared local audits; the library build remains a separate command. -/
def main (args : List String) : IO UInt32 := do
  -- Lake preserves the caller's cwd, including with `lake -d`.
  let some root := (← IO.appPath).parent >>= (·.parent) >>= (·.parent) >>= (·.parent)
    | throw <| IO.userError "local driver must run from the package build directory"
  let child ← IO.Process.spawn {
    cmd := "bash"
    cwd := some root
    args := #["scripts/local-checks.sh", "test"] ++ args.toArray
  }
  child.wait
