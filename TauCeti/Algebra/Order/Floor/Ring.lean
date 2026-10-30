/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Decomposition into unit intervals

A point of `[0, n)` in an ordered ring with a floor operation is the sum of an index in
`Fin n` and a remainder in `[0, 1)`. This describes, for example, time along one of the
finitely many edges in a polygonal boundary parametrization.
-/

public section

namespace TauCeti

/-- A point of `[0, n)` is an index in `Fin n` plus a remainder in `[0, 1)`. -/
theorem exists_eq_natCast_add_of_mem_Ico {R : Type*} [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] {n : ℕ} {t : R} (ht : t ∈ Set.Ico (0 : R) n) :
    ∃ j : Fin n, ∃ u ∈ Set.Ico (0 : R) 1, t = (j : ℕ) + u :=
  ⟨⟨⌊t⌋₊, (Nat.floor_lt ht.1).2 ht.2⟩, t - ⌊t⌋₊,
    ⟨sub_nonneg.2 (Nat.floor_le ht.1),
      (sub_lt_iff_lt_add).2 (by simpa only [add_comm] using Nat.lt_floor_add_one t)⟩, by simp⟩

end TauCeti
