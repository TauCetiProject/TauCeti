/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import TauCeti.LinearAlgebra.BilinearForm.Basic
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Orthogonal splitting along a finite-dimensional subspace

A nondegenerate restriction to a finite-dimensional subspace identifies that subspace with its
dual via `LinearMap.BilinForm.toDual` for the flipped form. This gives an orthogonal splitting
without requiring reflexivity of the form or finite dimension of the ambient space. An anisotropic
diagonal is sufficient for the required nondegeneracy on the subspace.
-/

public section

namespace LinearMap.BilinForm

/-- A finite-dimensional subspace on which a bilinear form is nondegenerate splits off along
its right orthogonal complement. -/
theorem isCompl_orthogonal_of_finiteDimensional_of_restrict_nondegenerate {K M : Type*} [Field K]
    [AddCommGroup M] [Module K M] (B : LinearMap.BilinForm K M) (W : Submodule K M)
    [FiniteDimensional K W] (hB : (B.restrict W).Nondegenerate) :
    IsCompl W (B.orthogonal W) := by
  refine ⟨disjoint_orthogonal_of_restrict_nondegenerate hB, codisjoint_iff.mpr (eq_top_iff.mpr ?_)⟩
  intro x _
  have hflip : (B.restrict W).flip.Nondegenerate := nondegenerate_flip_iff.mpr hB
  let w := ((B.restrict W).flip.toDual hflip).symm ((B.flip x).domRestrict W)
  have hw (y : W) : B y w = B y x :=
    apply_toDual_symm_apply (hB := hflip) ((B.flip x).domRestrict W) y
  refine Submodule.mem_sup.mpr ⟨w, w.property, x - w, mem_orthogonal_iff.mpr ?_,
    add_sub_cancel _ _⟩
  intro y hy
  simp [hw ⟨y, hy⟩]

/-- A bilinear form with anisotropic diagonal is nondegenerate on every submodule. -/
theorem nondegenerate_restrict_of_anisotropic {R M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] (B : LinearMap.BilinForm R M)
    (hB : B.toQuadraticMap.Anisotropic) (W : Submodule R M) : (B.restrict W).Nondegenerate := by
  rw [restrict_eq_compl₁₂]
  exact nondegenerate_of_anisotropic _
    (B.anisotropic_toQuadraticMap_compl₁₂ hB _ W.injective_subtype)

end LinearMap.BilinForm
