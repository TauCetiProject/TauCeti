/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single

/-!
# Presentations from augmented chain complexes

For a nonnegative chain complex augmented to `M`, an isomorphism on zeroth homology
identifies `M` with the cokernel of the first differential. No projectivity of the terms
or exactness in positive degrees is needed. This extracts presentations from resolutions
in categories where the resolving objects need not be projective.

The argument uses Mathlib's `ShortComplex.quasiIso_iff_of_zeros'`.
-/

public section

open CategoryTheory Limits HomologicalComplex

namespace ChainComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- An augmentation inducing an isomorphism on zeroth homology presents its target as the
cokernel of the first differential. Only the degree-zero quasi-isomorphism is needed. -/
noncomputable def isColimitCokernelCoforkOfQuasiIsoAt (K : ChainComplex C ℕ) {M : C}
    (π : K ⟶ (single₀ C).obj M) [QuasiIsoAt π 0] :
    IsColimit (CokernelCofork.ofπ (f := K.d 1 0) (π.f 0)
      (by rw [← π.comm 1 0, single_obj_d, comp_zero])) := by
  have h := (ShortComplex.quasiIso_iff_of_zeros'
    ((shortComplexFunctor' C (ComplexShape.down ℕ) 1 0 0).map π)
    (K.shape _ _ (by simp))
    (single_obj_d (ComplexShape.down ℕ) ..) (single_obj_d (ComplexShape.down ℕ) ..)).mp
      ((quasiIsoAt_iff' π 1 0 0 (by simp [prev]) (by simp)).mp inferInstance)
  letI := h.2
  exact h.1.gIsCokernel

end ChainComplex
