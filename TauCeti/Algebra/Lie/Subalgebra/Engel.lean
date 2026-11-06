/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.EngelSubalgebra
public import Mathlib.LinearAlgebra.Semisimple
import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.LinearAlgebra.Eigenspace.Semisimple

/-!
# Nilpotent subalgebras and Engel subalgebras

A nilpotent Lie subalgebra lies in the Engel subalgebra of each of its elements. This is the
converse of Mathlib's `LieSubalgebra.isNilpotent_of_forall_le_engel`, and it holds over any
commutative ring.

The Engel subalgebra of `x` is the generalized eigenspace of `ad x` at `0`. When `ad x` is
semisimple this generalized eigenspace is the eigenspace, so the Engel subalgebra of `x` is the
centralizer of `x`.

## Main results

* `LieSubalgebra.le_engel_of_isNilpotent`: a nilpotent subalgebra lies in the Engel subalgebra of
  each of its elements.
* `LieSubalgebra.mem_engel_iff_lie_eq_zero`: if `ad x` is semisimple, then `y` lies in the Engel
  subalgebra of `x` exactly when `⁅x, y⁆ = 0`.
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

/-- If the adjoint action of `x` is semisimple, then the Engel subalgebra of `x` is the centralizer
of `x`: `y` lies in it exactly when `⁅x, y⁆ = 0`. -/
theorem mem_engel_iff_lie_eq_zero {x y : L} (hx : (ad R L x).IsFinitelySemisimple) :
    y ∈ engel R x ↔ ⁅x, y⁆ = 0 := by
  have h := hx.maxGenEigenspace_eq_eigenspace 0
  refine ⟨fun hy ↦ ?_, fun hy ↦ (mem_engel_iff R x y).2 ⟨1, by simpa using hy⟩⟩
  obtain ⟨n, hn⟩ := (mem_engel_iff R x y).1 hy
  have hmem : y ∈ (ad R L x).maxGenEigenspace 0 :=
    (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨n, by simpa using hn⟩
  rw [h, Module.End.mem_eigenspace_iff, zero_smul] at hmem
  simpa using hmem

end LieSubalgebra
