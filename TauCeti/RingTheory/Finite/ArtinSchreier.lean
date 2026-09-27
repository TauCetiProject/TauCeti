/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.GroupTheory.Index
public import TauCeti.RingTheory.LocalRing.Basic

import Mathlib.Data.Set.Card

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

/-- On a finite commutative local ring of characteristic two, the Artin–Schreier map
`frobenius R 2 + id` has range of index two. -/
theorem index_range_frobenius_two_add_id (R : Type*) [CommRing R] [IsLocalRing R] [Finite R]
    [CharP R 2] :
    ((frobenius R 2).toAddMonoidHom + AddMonoidHom.id R).range.index = 2 := by
  rw [AddSubgroup.index_range]
  have hker : (((frobenius R 2).toAddMonoidHom + AddMonoidHom.id R).ker : Set R) =
      {0, 1} := by
    ext t
    simp [frobenius_def]
  rw [← SetLike.coe_sort_coe, hker, Nat.card_coe_set_eq, Set.ncard_pair zero_ne_one]

/-- On a finite commutative local ring of characteristic two, the sum of two elements outside
the range of `t ↦ t² + t` lies in the range. -/
theorem add_mem_range_sq_add_self {R : Type*} [CommRing R] [IsLocalRing R] [Finite R]
    [CharP R 2] {a b : R} (ha : a ∉ Set.range (fun t : R => t ^ 2 + t))
    (hb : b ∉ Set.range (fun t : R => t ^ 2 + t)) :
    a + b ∈ Set.range (fun t : R => t ^ 2 + t) := by
  have h := AddSubgroup.add_mem_iff_of_index_two (index_range_frobenius_two_add_id R)
    (a := a) (b := b)
  simpa [AddMonoidHom.mem_range, frobenius_def, ← Set.mem_range, ha, hb] using h

end TauCeti
