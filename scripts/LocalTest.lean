import Init.System.IO

/-- Run the shared local audits; the library build remains a separate command. -/
def main (args : List String) : IO UInt32 := do
  let child ← IO.Process.spawn {
    cmd := "bash"
    args := #["scripts/local-checks.sh", "test"] ++ args.toArray
  }
  child.wait
