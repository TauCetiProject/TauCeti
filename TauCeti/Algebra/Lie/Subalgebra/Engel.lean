/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.EngelSubalgebra
import Mathlib.Algebra.Lie.Weights.Cartan

/-!
# Nilpotent subalgebras and Engel subalgebras

A nilpotent Lie subalgebra lies in the Engel subalgebra of each of its elements. This is the
converse of Mathlib's `LieSubalgebra.isNilpotent_of_forall_le_engel`, and it holds over any
commutative ring.

## Main results

* `LieSubalgebra.le_engel_of_isNilpotent`: a nilpotent subalgebra lies in the Engel subalgebra of
  each of its elements.
-/

public section

namespace LieSubalgebra

open LieAlgebra LieModule

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- A nilpotent subalgebra lies in the Engel subalgebra of each of its elements. -/
theorem le_engel_of_isNilpotent (U : LieSubalgebra R L) [LieRing.IsNilpotent U] (h : U) :
    U ≤ engel R (h : L) := by
  intro y hy
  have hy₀ : y ∈ rootSpace U (0 : U → R) := toLieSubmodule_le_rootSpace_zero R L U hy
  have := genWeightSpace_le_genWeightSpaceOf L h (0 : U → R) hy₀
  rw [LieModule.mem_genWeightSpaceOf] at this
  simpa only [mem_engel_iff, zero_smul, sub_zero, LieAlgebra.ad, LieSubalgebra.toEnd_eq,
    Pi.zero_apply] using this

end LieSubalgebra
