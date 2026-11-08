import Init.System.IO

/-- Run the shared source and scoped environment checks. -/
def main (args : List String) : IO UInt32 := do
  let child ← IO.Process.spawn {
    cmd := "bash"
    args := #["scripts/local-checks.sh", "lint"] ++ args.toArray
  }
  child.wait
