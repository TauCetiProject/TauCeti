/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Symplectic forms on open submanifolds

Pullback by the inclusion of an open submanifold preserves nondegeneracy and symplecticity.
The tangent-space symplectic form is transported by the canonical tangent-space equivalence,
so linear symplectic calculations on an open submanifold agree with ambient calculations.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, Section 3.1.
-/

public section

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M}

/-- A nondegenerate two-form restricts to a nondegenerate form on every open submanifold. -/
theorem IsNondegenerate.mpullback_subtype_val (hσ : σ.IsNondegenerate) (U : Opens M) :
    IsNondegenerate (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val σ) := by
  rw [isNondegenerate_iff_separatingLeft]
  intro x v hv
  apply (Manifold.tangentSpaceOpenEquiv (I := I) x).injective
  rw [map_zero]
  apply isNondegenerate_iff_separatingLeft.mp hσ (x : M)
  intro w
  simpa only [SmoothForm.eval₂_mpullback, Manifold.mfderiv_subtype_val,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using
    hv ((Manifold.tangentSpaceOpenEquiv (I := I) x).symm w)

/-- Inclusion of an open submanifold transports its tangent-space symplectic form to the
ambient tangent-space form. -/
theorem IsNondegenerate.symplecticFormAt_mpullback_subtype_val_transport
    (hσ : σ.IsNondegenerate) {U : Opens M} (x : U) :
    ((hσ.mpullback_subtype_val U).symplecticFormAt x).transport
        (Manifold.tangentSpaceOpenEquiv (I := I) x).toLinearEquiv =
      hσ.symplecticFormAt (x : M) := by
  rw [← SymplecticForm.isSymplectomorphism_iff_transport_eq,
    SymplecticForm.isSymplectomorphism_iff]
  intro v w
  simp only [IsNondegenerate.symplecticFormAt_apply, SmoothForm.eval₂_mpullback,
    Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_toLinearEquiv,
    ContinuousLinearEquiv.coe_coe]

/-- A symplectic form restricts to a symplectic form on every open submanifold. -/
theorem IsSymplectic.mpullback_subtype_val (hσ : σ.IsSymplectic) (U : Opens M) :
    IsSymplectic (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val σ) :=
  ⟨hσ.isClosed.mpullback _ _, hσ.isNondegenerate.mpullback_subtype_val U⟩

end TauCeti.SmoothTwoForm
