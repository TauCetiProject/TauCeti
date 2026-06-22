import VersoBlog
import Site.Theme
import Site

open Verso Genre Blog Site Syntax

def taucetiSite : Site := site Site.Front /
  static "static" ← "static_files"
  "about" Site.About
  "statistics" Site.Stats

def main := blogMain theme taucetiSite
