import VersoBlog
import Site.Theme
import Site

open Verso Genre Blog

def taucetiSite : Site := .page (%docName Site.Front) (%doc Site.Front) #[
  .static "static" "static_files",
  .page "about" (%docName Site.About) (%doc Site.About) #[],
  .page "team" (%docName Site.Team) (%doc Site.Team) #[],
  .page "statistics" (%docName Site.Stats) (%doc Site.Stats) #[],
  .page "progress" (%docName Site.Progress) (%doc Site.Progress) #[],
  .page "ci" (%docName Site.CI) (%doc Site.CI) #[],
  Site.Blog.directory
]

def main := blogMain theme taucetiSite
