/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sort

/-!
# Sorting small and erased finsets

Sorting the finset `{a, b}` of two distinct elements with `r a b` gives the list `[a, b]`, and
sorting `s.erase a` gives the sorted list of `s` with `a` erased.
-/

public section

namespace Finset

variable {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [Std.Antisymm r]
  [Std.Total r] [DecidableEq α]

/-- Sorting a two-element finset `{a, b}` with `r a b` lists `a` before `b`. -/
theorem sort_pair {a b : α} (hab : r a b) (hne : a ≠ b) : sort {a, b} r = [a, b] := by
  rw [sort_insert r (fun c hc => mem_singleton.1 hc ▸ hab) (notMem_singleton.2 hne),
    sort_singleton]

/-- Sorting `s.erase a` erases `a` from the sorted list of `s`. -/
theorem sort_erase (s : Finset α) (a : α) : sort (s.erase a) r = (sort s r).erase a :=
  List.Perm.eq_of_pairwise' (pairwise_sort _ r) ((pairwise_sort s r).erase a) <|
    Multiset.coe_eq_coe.1 <| by rw [sort_eq, erase_val, ← Multiset.coe_erase, sort_eq]

end Finset
