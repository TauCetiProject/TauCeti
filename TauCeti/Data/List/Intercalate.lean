/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Basic

/-!
# Lists joined by a separator

`sep.intercalate L` joins the lists of `L` with the list `sep` between any two of them. This file
gives its length (`List.length_intercalate`) and its image under `List.flatMap`
(`List.flatMap_intercalate`): substituting lists for the entries substitutes into the separator and
into each joined list. Together with `List.splitOn_intercalate`, which recovers a nonempty list of
joined lists when the separator is a single entry occurring in none of them, these are what is
needed to encode finitely many equations between lists as one equation, the separator marking the
boundaries.

## References

* L. Ciobanu, V. Diekert, M. Elder, *Solution sets for equations over free groups are EDT0L
  languages*, Internat. J. Algebra Comput. 26 (2016), 843–886, §2, (1)–(2) (a system of word
  equations as one equation with a separator `#`).
-/

public section

namespace List

variable {α β : Type*}

/-- The length of lists joined by a separator: the total length of the lists plus one separator
between any two consecutive ones. -/
@[simp]
theorem length_intercalate (sep : List α) (L : List (List α)) :
    (sep.intercalate L).length = (L.map length).sum + sep.length * (L.length - 1) := by
  induction L with
  | nil => simp
  | cons l L ih =>
    cases L with
    | nil => simp
    | cons l' L =>
      simp only [intercalate_cons_cons, length_append, ih, map_cons, sum_cons, length_cons]
      grind

/-- Substituting lists for the entries of lists joined by a separator joins the substituted lists
by the substituted separator. -/
@[simp]
theorem flatMap_intercalate (f : α → List β) (sep : List α) (L : List (List α)) :
    (sep.intercalate L).flatMap f = (sep.flatMap f).intercalate (L.map (·.flatMap f)) := by
  induction L with
  | nil => simp
  | cons l L ih => cases L <;> simp_all

/-- Three lists joined by a one-entry separator: two copies of the separator. -/
example : ([0].intercalate [[1, 2], [], [3]]).length = 5 := by
  rw [length_intercalate]
  rfl

/-- Doubling every entry doubles the separator and every joined list. -/
example : ([0].intercalate [[1], [2]]).flatMap (fun a ↦ [a, a]) =
    [0, 0].intercalate [[1, 1], [2, 2]] := by
  rw [flatMap_intercalate]
  rfl

end List
