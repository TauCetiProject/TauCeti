import Site.Theme
import Site.Blog

open Verso Genre Blog

private def post (draft : Bool) : BlogPost := {
  id := if draft then `Draft else `Published
  contents := {
    title := #[.text (if draft then "Unpublished draft" else "First post")]
    titleString := if draft then "Unpublished draft" else "First post"
    metadata := some {
      date := ⟨2026, 10, 28⟩
      authors := ["Test Author"]
      categories := [⟨"Updates", "updates"⟩]
      draft
    }
    content := #[.para #[.text "A post with ", .emph #[.text "formatted text"],
      .text " and a ", .link #[.text "home link"] "/", .text "."]]
    subParts := #[]
  }
}

/-- Exercise the production registry, templates, and generator without the maths examples. -/
def main (args : List String) : IO UInt32 := do
  let mode :: options := args | throw <| IO.userError "Expected a fixture mode"
  let entries ← match mode with
    | "empty" => pure #[]
    | "draft" => pure #[post true]
    | "published" => pure #[post true, post false]
    | _ => throw <| IO.userError s!"Unknown fixture mode: {mode}"
  let site : Site := .page `Home (%doc Site.Blog.Index) #[
    .static "static" "static_files",
    .page "about" `About (%doc Site.Blog.Index) #[],
    Site.Blog.directory entries
  ]
  blogMain theme site (options := options)
