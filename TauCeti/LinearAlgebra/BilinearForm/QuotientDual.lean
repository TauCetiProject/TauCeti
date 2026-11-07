/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Duality with the quotient by an orthogonal complement

A nondegenerate bilinear form `B` on a finite-dimensional vector space identifies
`V ⧸ Wᗮ` with `W*` by `[v] ↦ B(·, v)|W`. No symmetry of `B` is required.
For a Lagrangian subspace, `Wᗮ = W`, so this is the canonical identification of its
normal quotient with its dual. The order of the two arguments fixes the sign of
that identification.

The construction uses Mathlib's `BilinForm.toDual`, `Submodule.dualRestrict`, and
`LinearMap.quotKerEquivOfSurjective`.
-/

public noncomputable section

namespace LinearMap.BilinForm

section Semiring

variable {K V : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V]

/-- The kernel of the pairing with a subspace in the first argument is its right
orthogonal complement. -/
theorem ker_dualRestrict_comp_flip (B : LinearMap.BilinForm K V) (W : Submodule K V) :
    LinearMap.ker (W.dualRestrict.comp B.flip) = B.orthogonal W := by
  ext v
  simp only [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.comp_apply,
    Submodule.dualRestrict_apply, LinearMap.BilinForm.flip_apply, LinearMap.zero_apply,
    mem_orthogonal_iff, Subtype.forall]

end Semiring

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Pairing with a subspace in the first argument is surjective onto its dual
when the ambient bilinear form is nondegenerate. -/
theorem surjective_dualRestrict_comp_flip (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (W : Submodule K V) : Function.Surjective (W.dualRestrict.comp B.flip) :=
  (Subspace.dualRestrict_surjective (W := W)).comp (B.flip.toDual hB.flip).surjective

/-- The quotient by the right orthogonal complement of a subspace is canonically
its dual, via `[v] ↦ B(·, v)|W`. -/
def quotientOrthogonalEquivDual (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (W : Submodule K V) : (V ⧸ B.orthogonal W) ≃ₗ[K] Module.Dual K W :=
  (Submodule.quotEquivOfEq _ _ (B.ker_dualRestrict_comp_flip W).symm).trans
    ((W.dualRestrict.comp B.flip).quotKerEquivOfSurjective
      (B.surjective_dualRestrict_comp_flip hB W))

/-- Evaluation of the orthogonal-quotient duality on a representative. -/
@[simp]
theorem quotientOrthogonalEquivDual_mk_apply (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (W : Submodule K V) (v : V) (w : W) :
    B.quotientOrthogonalEquivDual hB W (Submodule.Quotient.mk v) w = B w v :=
  (rfl)

/-- The inverse duality is characterized by its pairings with the subspace. -/
theorem quotientOrthogonalEquivDual_symm_apply_eq_mk_iff (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (W : Submodule K V) (α : Module.Dual K W) (v : V) :
    (B.quotientOrthogonalEquivDual hB W).symm α = Submodule.Quotient.mk v ↔
      ∀ w : W, B w v = α w := by
  rw [LinearEquiv.symm_apply_eq]
  exact (LinearMap.ext_iff).trans (forall_congr' fun w ↦ eq_comm)

end LinearMap.BilinForm
