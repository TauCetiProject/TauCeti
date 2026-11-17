/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Function

/-!
# Injectivity from injectivity on a cover

A map on `X = A ∪ B` that is injective on `A` and on `B`, and which sends exactly the points of
`A` to values satisfying a predicate `P`, is injective: two points with the same image are both
in `A` or both outside it, and a point outside `A` lies in `B`.

## Main results

* `TauCeti.injective_of_injOn_of_union_eq_univ`: the statement above.
-/

public section

namespace TauCeti

open Set

variable {X Y : Type*} {A B : Set X}

/-- A map on `X = A ∪ B` that is injective on `A` and on `B`, and which sends exactly the points
of `A` to values satisfying a predicate `P`, is injective. -/
theorem injective_of_injOn_of_union_eq_univ {g : X → Y} {P : Y → Prop}
    (hAB : A ∪ B = univ) (hP : ∀ x, P (g x) ↔ x ∈ A) (hA : InjOn g A) (hB : InjOn g B) :
    Function.Injective g := by
  intro x y hxy
  have hxy' : x ∈ A ↔ y ∈ A := by rw [← hP, ← hP, hxy]
  by_cases hx : x ∈ A
  · exact hA hx (hxy'.1 hx) hxy
  · exact hB (compl_subset_iff_union.mpr hAB hx) (compl_subset_iff_union.mpr hAB (hxy'.not.1 hx))
      hxy

end TauCeti
