/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Lattice.Indexed

/-!
# Injectivity from injectivity on a cover

A map on `X = A ∪ B` that is injective on `A` and on `B`, and which sends exactly the points of
`A` to values satisfying a predicate `P`, is injective: two points with the same image are both
in `A` or both outside it, and a point outside `A` lies in `B`.

## Main results

* `TauCeti.injective_of_injOn_of_union_eq_univ`: the statement above.
* `TauCeti.injOn_of_subset_iUnion`: injectivity on a set covered by an ordered family, when each
  piece is injective and cross-coincidences land in the shared piece.
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

/-- A map `g` on a set `T ⊆ ⋃ i, S i` is injective on `T` if it is injective on each `S i` and any
coincidence `g x = g y` between `x ∈ S i` and `y ∈ S j` (`i < j`) puts `x ∈ S j` or `y ∈ S i`. -/
theorem injOn_of_subset_iUnion {ι : Type*} [LinearOrder ι] {S : ι → Set X} {T : Set X}
    {g : X → Y} (hT : T ⊆ ⋃ i, S i) (hS : ∀ i, InjOn g (S i))
    (hcross : ∀ ⦃i j⦄, i < j → ∀ ⦃x y⦄, x ∈ S i → y ∈ S j → g x = g y → x ∈ S j ∨ y ∈ S i) :
    InjOn g T := by
  intro x hx y hy hxy
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hT hx)
  obtain ⟨j, hj⟩ := mem_iUnion.1 (hT hy)
  rcases lt_trichotomy i j with hij | rfl | hij
  · rcases hcross hij hi hj hxy with h | h
    · exact hS j h hj hxy
    · exact hS i hi h hxy
  · exact hS i hi hj hxy
  · rcases hcross hij hj hi hxy.symm with h | h
    · exact (hS i h hi hxy.symm).symm
    · exact (hS j hj h hxy.symm).symm

end TauCeti
