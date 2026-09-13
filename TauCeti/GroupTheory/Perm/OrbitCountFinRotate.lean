/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.OrbitCount
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Orbits of cyclic rotation

Cyclic rotation of a nonempty finite ordinal has one orbit, including the singleton case
where the rotation is the identity. This count includes fixed points.
-/

public section

namespace TauCeti

/-- Cyclic rotation has one orbit when the ordinal is nonempty, and none otherwise. -/
@[simp]
theorem orbitCount_finRotate (n : ℕ) : orbitCount (finRotate n) = if n = 0 then 0 else 1 := by
  rcases n with _ | _ | n
  · rw [finRotate_zero]
    change orbitCount (1 : Equiv.Perm (Fin 0)) = 0
    exact (orbitCount_one (α := Fin 0)).trans (by simp)
  · rw [show 0 + 1 = 1 by omega, finRotate_one]
    change orbitCount (1 : Equiv.Perm (Fin 1)) = 1
    exact (orbitCount_one (α := Fin 1)).trans (by simp)
  · rw [Equiv.Perm.orbitCount_eq_card_parts_partition,
      Equiv.Perm.parts_partition_of_isCycle isCycle_finRotate, support_finRotate]
    simp

end TauCeti
