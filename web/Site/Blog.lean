import Site.Blog.Index

open Verso Genre Blog

namespace Site.Blog

/-- Register posts here, newest first. See web/README.md for the post format. -/
def posts : Array BlogPost := #[]

/-- Filter drafts before traversal so they cannot appear in archives or category lists. -/
def directory (entries : Array BlogPost := posts) : Dir :=
  .blog "blog" (%docName Site.Blog.Index) (%doc Site.Blog.Index)
    (entries.filter fun post => !(post.contents.metadata.map (·.draft) |>.getD false))

end Site.Blog
