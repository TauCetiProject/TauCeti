import Site.Theme
import Site.CI

open Verso Genre Blog

/-- Render the real CI page independently of the front-page mathematics examples. -/
def main (options : List String) : IO UInt32 := do
  let site : Site := .page `Home (%doc Site.CI) #[
    .static "static" "static_files",
    .page "ci" (%docName Site.CI) (%doc Site.CI) #[]
  ]
  blogMain theme site (options := options)
