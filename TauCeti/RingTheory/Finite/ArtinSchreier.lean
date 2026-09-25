/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Data.Fintype.Card

/-!
# A finite-ring Artin–Schreier witness

On a finite nontrivial ring, the map `t ↦ t² + t` is not surjective: it sends both `0` and
`-1` to zero. This supplies residue-field witnesses for local square and norm arguments.
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

end TauCeti
