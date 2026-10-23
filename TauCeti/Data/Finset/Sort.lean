/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sort

/-!
# Sorting a two-element finset

Sorting the finset `{a, b}` of two distinct elements with `r a b` gives the list `[a, b]`.
-/

public section

namespace Finset

variable {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [Std.Antisymm r]
  [Std.Total r] [DecidableEq α]

/-- Sorting a two-element finset `{a, b}` with `r a b` lists `a` before `b`. -/
theorem sort_pair {a b : α} (hab : r a b) (hne : a ≠ b) : sort {a, b} r = [a, b] := by
  rw [sort_insert r (fun c hc => mem_singleton.1 hc ▸ hab) (notMem_singleton.2 hne),
    sort_singleton]

end Finset
