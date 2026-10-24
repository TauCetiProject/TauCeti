/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.Lattice

/-!
# Comparing functions by a maximal coordinate ratio

On a finite nonempty type, every function lies below a scalar multiple of a strictly positive
function, with equality at a coordinate where the ratio is maximal.

## Main results

* `TauCeti.exists_le_smul_of_pos`: domination by a scalar multiple of a positive function,
  with a coordinate where equality holds.
-/

public section

namespace TauCeti

/-- Comparing coordinate ratios gives a scalar multiple lying above a vector and touching it. -/
theorem exists_le_smul_of_pos {n K : Type*} [Finite n] [Semifield K] [LinearOrder K]
    [IsStrictOrderedRing K] {v : n → K} (hv : ∀ i, 0 < v i) (j : n) (y : n → K) :
    ∃ i, y ≤ (y i / v i) • v ∧ y i = y i / v i * v i := by
  have : Nonempty n := ⟨j⟩
  obtain ⟨i, hi⟩ := Finite.exists_max fun i => y i / v i
  refine ⟨i, fun k ↦ ?_, (div_mul_cancel₀ _ (hv i).ne').symm⟩
  simpa [mul_comm] using (div_le_iff₀ (hv k)).1 (hi k)

end TauCeti
