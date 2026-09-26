/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.RingTheory.LocalRing.Defs

import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.Index

/-!
# The Artin–Schreier map `t ↦ t² + t` on a finite ring

On a finite nontrivial ring, the map `t ↦ t² + t` is not surjective: it sends both `0` and
`-1` to zero. This supplies residue-field witnesses for local square and norm arguments.

On a finite commutative local ring of characteristic two the map is additive with kernel
`{0, 1}`, so its range has index two: the sum of two elements outside the range lies in the range.
Over the residue field, this makes the unramified quadratic class of a dyadic local field unique.
-/

public section

namespace TauCeti

/-- The map `t ↦ t² + t` has a value outside its range on every finite nontrivial ring. -/
theorem exists_not_mem_range_sq_add_self (R : Type*) [Ring R] [Finite R] [Nontrivial R] :
    ∃ a : R, a ∉ Set.range (fun t : R => t ^ 2 + t) := by
  by_contra! h
  have hsurj : Function.Surjective (fun t : R => t ^ 2 + t) := fun a => h a
  have hinj := Finite.injective_iff_surjective.mpr hsurj
  exact one_ne_zero (neg_eq_zero.mp (hinj (a₁ := (-1 : R)) (a₂ := 0) (by simp [pow_two])))

/-- On a finite commutative local ring of characteristic two, the sum of two elements outside
the range of `t ↦ t² + t` lies in the range. -/
theorem add_mem_range_sq_add_self {R : Type*} [CommRing R] [IsLocalRing R] [Finite R]
    [CharP R 2] {a b : R} (ha : a ∉ Set.range (fun t : R => t ^ 2 + t))
    (hb : b ∉ Set.range (fun t : R => t ^ 2 + t)) :
    a + b ∈ Set.range (fun t : R => t ^ 2 + t) := by
  -- In characteristic two, `t ↦ t² + t` is additive.
  let f : R →+ R := (frobenius R 2).toAddMonoidHom + AddMonoidHom.id R
  have hf (t : R) : f t = t ^ 2 + t := by simp [f, frobenius_def]
  -- Its kernel is `{0, 1}`, of cardinality two.
  have hker : Nat.card f.ker = 2 := by
    have : (f.ker : Set R) = {0, 1} := by
      ext t
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, hf,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro ht
        have hmul : t * (t + 1) = 0 := by simpa [mul_add, pow_two] using ht
        rcases IsLocalRing.isUnit_or_isUnit_of_add_one (a := t) (b := t + 1)
          (by simp [← add_assoc, CharTwo.add_self_eq_zero]) with hu | hu
        · exact Or.inr (by simpa [CharTwo.add_eq_zero] using hu.mul_right_eq_zero.mp hmul)
        · exact Or.inl (hu.mul_left_eq_zero.mp hmul)
      · rintro (rfl | rfl) <;> simp [CharTwo.add_self_eq_zero]
    rw [← SetLike.coe_sort_coe, this, Nat.card_coe_set_eq, Set.ncard_pair zero_ne_one]
  have hindex : f.range.index = 2 := by
    rw [AddSubgroup.index_range, hker]
  have hrange : ∀ x, x ∈ f.range ↔ x ∈ Set.range (fun t : R => t ^ 2 + t) := fun x => by
    simp only [AddMonoidHom.mem_range, Set.mem_range, hf]
  rw [← hrange, AddSubgroup.add_mem_iff_of_index_two hindex, hrange, hrange]
  exact iff_of_false ha hb

end TauCeti
